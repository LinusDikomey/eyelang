use ir::{
    mc::{BlockBuilder, MachineIR, MirBlock, Op, VReg, VRegs},
    offset_in_tuple, BlockGraph, BlockIndex, FunctionId, IrType, Ref, Tag,
};

use crate::isa::{Inst, Reg};

const ABI_PARAM_REGISTERS: [Reg; 6] = [Reg::edi, Reg::esi, Reg::edx, Reg::ecx, Reg::r8d, Reg::r9d];
const ABI_RETURN_REGISTER: Reg = Reg::rax;

type Builder<'a> = BlockBuilder<'a, Inst>;

pub fn codegen(
    body: &ir::FunctionIr,
    function: &ir::Function,
    types: &ir::IrTypes,
) -> MachineIR<Inst> {
    let mut mir = MachineIR::new();
    let mut builder = mir.begin_block(MirBlock::ENTRY);
    let mut values = vec![MCValue::None; body.inst.len()];

    builder.inst(Inst::push64, [Op::Reg(Reg::rbp)]);
    builder.inst(Inst::movrr64, [Op::Reg(Reg::rbp), Op::Reg(Reg::rsp)]);
    // This instruction's immediate operand will be updated at the end with the used stack space.
    // In the future, the stack size might be known a priori when the IR tracks a list of stack
    // slots.
    let stack_setup_indices = vec![builder.next_inst_index()];
    builder.inst(Inst::subri64, [Op::Reg(Reg::rsp), Op::Imm(0)]);

    let (mir_entry_block, entry_block_args) = builder.create_block(function.params.count);
    builder.register_successor(mir_entry_block);
    // TODO: handle args abi correctly with different arg sizes and more than 6 args.
    builder.build_copyargs(
        Inst::Copyargs,
        entry_block_args.iter().map(|vreg| vreg.op()),
        ABI_PARAM_REGISTERS
            .iter()
            .take(entry_block_args.iter().len())
            .map(|&arg_phys_reg| Op::Reg(arg_phys_reg)),
    );

    let block_map = body
        .blocks()
        .map(|block| {
            let args = body.get_block_args(block);
            let (mir_block, mir_args) = if block == BlockIndex::ENTRY {
                (mir_entry_block, entry_block_args)
            } else {
                builder.create_block(args.count() as u32)
            };
            for (arg, mir_arg) in args.iter().zip(mir_args.iter()) {
                values[arg as usize] = MCValue::Reg(MCReg::Virtual(mir_arg));
                if block == BlockIndex::ENTRY {}
            }
            (mir_block, mir_args)
        })
        .collect();
    let mut gen = Gen {
        function,
        body,
        types,
        stack_setup_indices,
        block_map,
    };

    let graph = BlockGraph::calculate(gen.body);

    for &block in graph.postorder().iter().rev() {
        let mir_block = gen.block_map[block.idx() as usize].0;
        let mut builder = mir.begin_block(mir_block);
        for (i, inst) in body.get_block(block) {
            values[i as usize] = gen.gen_inst(inst, &mut builder, &values, &body.extra);
        }
    }

    for idx in gen.stack_setup_indices {
        mir.replace_operand(idx, 1, offset_op(mir.stack_offset() as i32));
    }
    mir
}

struct Gen<'a> {
    function: &'a ir::Function,
    body: &'a ir::FunctionIr,
    types: &'a ir::IrTypes,
    stack_setup_indices: Vec<u32>,
    block_map: Box<[(MirBlock, VRegs)]>,
}
impl<'a> Gen<'a> {
    fn create_epilogue(&mut self, builder: &mut Builder) {
        self.stack_setup_indices.push(builder.next_inst_index());
        builder.inst(Inst::addri64, [Op::Reg(Reg::rsp), Op::Imm(0)]);
        builder.inst(Inst::pop64, [Op::Reg(Reg::rbp)]);
    }

    fn gen_inst(
        &mut self,
        inst: ir::Instruction,
        builder: &mut Builder,
        values: &[MCValue],
        extra: &[u8],
    ) -> MCValue {
        match inst.tag {
            Tag::BlockArg => unreachable!(),
            Tag::Int => MCValue::Imm(inst.data.int()),
            Tag::LargeInt => todo!(),
            Tag::Float => todo!(),
            Tag::Decl => {
                let layout = self.types.layout(self.types[inst.data.ty()]);
                let offset = -(builder.create_stack_slot(layout) as i32) - layout.size as i32;
                MCValue::PtrOffset(MCReg::Register(Reg::rbp), offset)
            }
            Tag::Load => {
                let ptr = get_ref(&values, inst.data.un_op());
                match self.types[inst.ty] {
                    IrType::Unit => MCValue::None,
                    IrType::I32 => match ptr {
                        MCValue::None => panic!(),
                        MCValue::Undef => MCValue::Undef,
                        MCValue::Imm(_) => todo!("load from addresses"),
                        MCValue::Reg(r) => MCValue::PtrOffset(r, 0),
                        MCValue::Indirect(r, offset) => {
                            let loaded = builder.reg();
                            builder
                                .inst(Inst::movrm32, [loaded.op(), r.op(), Op::Imm(offset as u64)]);
                            MCValue::Reg(MCReg::Virtual(loaded))
                        }
                        MCValue::PtrOffset(r, offset) => MCValue::Indirect(r, offset),
                    },
                    ty => todo!("load value of type {ty:?}"),
                }
            }
            Tag::Store => {
                let (ptr, val) = inst.data.bin_op();
                let ptr = get_ref(&values, ptr);
                let val = get_ref(&values, val);
                let MCValue::PtrOffset(ptr, off) = ptr else {
                    todo!("handle store into {ptr:?}")
                };
                match val {
                    MCValue::None | MCValue::Undef => {}
                    MCValue::Imm(val) => {
                        builder.inst(Inst::movmi32, [ptr.op(), Op::Imm(off as u64), Op::Imm(val)])
                    }
                    MCValue::Reg(r) => {
                        builder.inst(Inst::movmr32, [ptr.op(), Op::Imm(off as u64), r.op()])
                    }
                    MCValue::PtrOffset(_, _) => todo!(),
                    MCValue::Indirect(r, r_off) => {
                        let tmp = builder.reg();
                        builder.inst(Inst::movrm32, [tmp.op(), r.op(), offset_op(r_off)]);
                        builder.inst(Inst::movmr32, [ptr.op(), offset_op(off), tmp.op()]);
                    }
                }
                MCValue::None
            }
            Tag::MemberPtr => {
                let (ptr, elem_types, elem_idx) = inst.data.member_ptr(extra);
                let offset = ir::offset_in_tuple(elem_types, elem_idx, self.types);
                //let offset: i32 = offset.try_into().expect("TODO: handle large offsets");
                match get_ref(values, ptr) {
                    MCValue::None => unreachable!(),
                    MCValue::Undef => MCValue::Undef,
                    MCValue::Imm(imm) => MCValue::Imm(imm + offset),
                    MCValue::Reg(r) => MCValue::PtrOffset(
                        r,
                        TryInto::<i32>::try_into(offset).expect("TODO: handle large offsets"),
                    ),
                    MCValue::PtrOffset(r, cur) => MCValue::PtrOffset(
                        r,
                        cur + TryInto::<i32>::try_into(offset).expect("TODO: handle large offsets"),
                    ),
                    MCValue::Indirect(r, r_off) => {
                        let vreg = builder.reg();
                        builder.inst(Inst::movrm64, [vreg.op(), r.op(), offset_op(r_off)]);
                        MCValue::PtrOffset(MCReg::Virtual(vreg), r_off)
                    }
                }
            }
            Tag::MemberValue => todo!("MemberValue"),
            Tag::Add => self.bin_op_commutative(
                builder,
                values,
                inst.data.bin_op(),
                self.types[inst.ty],
                BinOpInsts {
                    rr: Inst::addrr32,
                    ri: Inst::addri32,
                    is_rri: false,
                    rm: Inst::addrm32,
                },
                |a, b| {
                    (TryInto::<i32>::try_into(a).unwrap() + TryInto::<i32>::try_into(b).unwrap())
                        as u64
                },
            ),
            Tag::Sub => self.bin_op_noncommutative(
                builder,
                values,
                inst.data.bin_op(),
                self.types[inst.ty],
                BinOpInsts {
                    rr: Inst::subrr32,
                    ri: Inst::subri32,
                    is_rri: false,
                    rm: Inst::subrm32,
                },
                |a, b| {
                    TryInto::<i32>::try_into(a)
                        .unwrap()
                        .wrapping_sub(TryInto::<i32>::try_into(b).unwrap())
                        as u64
                },
            ),
            Tag::Mul => self.bin_op_commutative(
                builder,
                values,
                inst.data.bin_op(),
                self.types[inst.ty],
                BinOpInsts {
                    rr: Inst::imulrr32,
                    ri: Inst::imulrri32,
                    is_rri: true,
                    rm: Inst::imulrm32,
                },
                |a, b| {
                    (TryInto::<i32>::try_into(a).unwrap() * TryInto::<i32>::try_into(b).unwrap())
                        as u64
                },
            ),
            Tag::Div => todo!(),
            Tag::Mod => todo!(),
            Tag::Ret => {
                let val = inst.data.un_op();
                let val = get_ref(&values, val);
                match self.function.return_type {
                    IrType::Unit => {
                        self.create_epilogue(builder);
                        builder.inst(Inst::ret0, []);
                    }
                    IrType::I32 => {
                        match val {
                            MCValue::Reg(MCReg::Register(Reg::eax)) => {}
                            MCValue::Reg(reg) => {
                                builder.inst(Inst::Copy, [Op::Reg(Reg::eax), reg.op()]);
                            }
                            MCValue::Imm(imm) => {
                                builder.inst(Inst::movri32, [Op::Reg(Reg::eax), Op::Imm(imm)]);
                            }
                            MCValue::Indirect(reg, offset) => builder.inst(
                                Inst::movrm32,
                                [Op::Reg(Reg::eax), reg.op(), Op::Imm(offset as u64)],
                            ),
                            MCValue::PtrOffset(_, _) => todo!("calculate ptr addr for ret"),
                            MCValue::None | MCValue::Undef => {}
                        }
                        self.create_epilogue(builder);
                        builder.inst(Inst::ret32, []);
                    }
                    ty => todo!("handle return type {ty:?}"),
                }
                MCValue::None
            }
            Tag::Call => {
                let (extra_start, arg_count) = inst.data.extra_len();
                let start = extra_start as usize;
                let mut bytes = [0; 8];
                bytes.copy_from_slice(&self.body.extra[start..start + 8]);
                let func = FunctionId::from_bytes(bytes);
                assert_eq!(arg_count, 0, "TODO: call args");
                /*
                let refs = (0..arg_count).map(|i| {
                    let mut ref_bytes = [0; 4];
                    let begin = 8 + start + (4 * i) as usize;
                    ref_bytes.copy_from_slice(&extra[begin..begin + 4]);
                    Ref::from_bytes(ref_bytes)
                });
                */
                builder.inst(Inst::call, [Op::Func(func)]);
                match self.types[inst.ty] {
                    IrType::Unit => MCValue::Undef,
                    IrType::I32 => MCValue::Reg(MCReg::Register(ABI_RETURN_REGISTER)),
                    IrType::Const(_) => panic!(),
                    other => todo!("handle call with type {other:?}"),
                }
            }
            Tag::Eq | Tag::NE | Tag::LT | Tag::GT | Tag::LE | Tag::GE => {
                let (a, b) = inst.data.bin_op();
                let ty = self.body.get_ref_ty(a, self.types);
                self.comparison(builder, values, inst.tag, a, b, ty)
            }
            Tag::Goto => {
                let (target, extra_idx) = inst.data.goto();
                self.copy_block_args(builder, values, target, extra_idx);
                let mir_block = self.block_map[target.idx() as usize].0;
                builder.inst(Inst::jmp, [Op::Block(mir_block)]);
                builder.register_successor(mir_block);
                MCValue::Undef
            }
            Tag::Branch => {
                let (cond, t, f, i) = inst.data.branch(extra);
                let mir_t = self.block_map[t.idx() as usize].0;
                let mir_f = self.block_map[f.idx() as usize].0;
                builder.register_successor(mir_t);
                builder.register_successor(mir_f);
                match get_ref(&values, cond) {
                    MCValue::Reg(r) => {
                        builder.inst(Inst::cmpri8, [r.op(), Op::Imm(0)]);
                        // TODO: generate true block next, create false block label
                        // builder.inst(Inst::je, [Op::Block(f)]);
                    }
                    value => todo!("handle branch cond value {value:?}"),
                }
                self.copy_block_args(builder, values, t, i);
                builder.inst(Inst::je, [Op::Block(mir_f)]);
                let f_extra_idx = i + self.body.get_block_args(t).count() * 4;
                self.copy_block_args(builder, values, f, f_extra_idx);
                builder.inst(Inst::jmp, [Op::Block(mir_t)]);
                MCValue::Undef
            }
            Tag::Global => todo!(),
            Tag::Uninit => MCValue::Undef,
            Tag::MemberPtr => todo!(),
            Tag::MemberValue => todo!(),
            Tag::ArrayIndex => todo!(),
            Tag::String => todo!(),
            Tag::Neg => todo!(),
            Tag::Not => todo!(),
            Tag::Or => todo!(),
            Tag::And => todo!(),
            Tag::CastInt => todo!(),
            Tag::CastFloat => todo!(),
            Tag::CastIntToFloat => todo!(),
            Tag::CastFloatToInt => todo!(),
            Tag::IntToPtr => todo!(),
            Tag::PtrToInt => todo!(),
            Tag::Asm => todo!(),
        }
    }

    fn copy_block_args(
        &self,
        builder: &mut Builder,
        values: &[MCValue],
        target: BlockIndex,
        extra_index: usize,
    ) {
        let t_count = self.body.get_block_args(target).count();
        let mut bytes = [0; 4];
        let t_to = self.body.get_block_args(target).iter().map(|arg| {
            let MCValue::Reg(MCReg::Virtual(v)) = values[arg as usize] else {
                unreachable!()
            };
            v.op::<Reg>()
        });
        let t_from = (0..t_count).map(|arg_index| {
            let i = extra_index + arg_index * 4;
            bytes.copy_from_slice(&self.body.extra[i..i + 4]);
            let r = ir::Ref::from_bytes(bytes);
            let MCValue::Reg(r) = get_ref(values, r) else {
                todo!()
            };
            r.op()
        });
        builder.build_copyargs(Inst::Copyargs, t_to, t_from);
    }

    fn bin_op_commutative(
        &mut self,
        builder: &mut Builder,
        values: &[MCValue],
        (lhs, rhs): (Ref, Ref),
        ty: IrType,
        insts32: BinOpInsts,
        fold: impl Fn(u64, u64) -> u64,
    ) -> MCValue {
        let lhs = get_ref(&values, lhs);
        let rhs = get_ref(&values, rhs);
        let changed_reg = match ty {
            IrType::U32 | IrType::I32 => match (lhs, rhs) {
                (MCValue::Undef, _) | (_, MCValue::Undef) => return MCValue::Undef,
                (MCValue::Imm(a), MCValue::Imm(b)) => return MCValue::Imm(fold(a, b)),
                (MCValue::Reg(lhs), MCValue::Reg(rhs)) => {
                    builder.inst(insts32.rr, [lhs.op(), rhs.op()]);
                    lhs
                }
                (MCValue::Reg(reg), MCValue::Imm(imm)) | (MCValue::Imm(imm), MCValue::Reg(reg)) => {
                    if insts32.is_rri {
                        let out = builder.reg();
                        builder.inst(insts32.ri, [out.op(), reg.op(), Op::Imm(imm)]);
                        MCReg::Virtual(out)
                    } else {
                        builder.inst(insts32.ri, [reg.op(), Op::Imm(imm)]);
                        reg
                    }
                }
                (MCValue::Reg(reg), MCValue::Indirect(ptr, off))
                | (MCValue::Indirect(ptr, off), MCValue::Reg(reg)) => {
                    builder.inst(insts32.rm, [reg.op(), ptr.op(), Op::Imm(off as u64)]);
                    reg
                }
                (MCValue::Indirect(a, a_off), other) | (other, MCValue::Indirect(a, a_off)) => {
                    let reg = builder.reg();
                    builder.inst(Inst::movrm32, [reg.op(), a.op(), Op::Imm(a_off as u64)]);
                    match other {
                        MCValue::Indirect(b, b_off) => {
                            builder.inst(insts32.rm, [reg.op(), b.op(), Op::Imm(b_off as u64)])
                        }
                        MCValue::Imm(imm) => builder.inst(insts32.ri, [reg.op(), Op::Imm(imm)]),
                        _ => unreachable!(),
                    }
                    MCReg::Virtual(reg)
                }
                (MCValue::PtrOffset(_, _) | MCValue::None, _)
                | (_, MCValue::PtrOffset(_, _) | MCValue::None) => unreachable!(),
            },
            _ => todo!("handle add of type {ty:?}"),
        };

        let v = builder.reg();
        builder.inst(Inst::Copy, [Op::VReg(v), changed_reg.op()]);
        MCValue::Reg(MCReg::Virtual(v))
    }

    fn bin_op_noncommutative(
        &mut self,
        builder: &mut Builder,
        values: &[MCValue],
        (lhs, rhs): (Ref, Ref),
        ty: IrType,
        insts32: BinOpInsts,
        fold: impl Fn(u64, u64) -> u64,
    ) -> MCValue {
        match ty {
            IrType::I32 | IrType::U32 => {}
            _ => todo!("handle op ty {ty:?}"),
        }
        let lhs = get_ref(values, lhs);
        let rhs = get_ref(values, rhs);
        let lhs = match (lhs, rhs) {
            (MCValue::None | MCValue::PtrOffset(_, _), _)
            | (_, MCValue::None | MCValue::PtrOffset(_, _)) => unreachable!(),
            (MCValue::Undef, _) | (_, MCValue::Undef) => return MCValue::Undef,
            (MCValue::Imm(a), MCValue::Imm(b)) => return MCValue::Imm(fold(a, b)),
            (MCValue::Imm(lhs), _) => {
                let reg = builder.reg();
                builder.inst(Inst::movri32, [reg.op(), Op::Imm(lhs)]);
                reg
            }
            (MCValue::Reg(a), _) => builder.copy_to_fresh(a.op()),
            (MCValue::Indirect(a, a_off), _) => {
                let reg = builder.reg();
                builder.inst(Inst::movrm32, [reg.op(), a.op(), offset_op(a_off)]);
                reg
            }
        };
        match rhs {
            MCValue::None | MCValue::Undef | MCValue::PtrOffset(_, _) => unreachable!(),
            MCValue::Imm(i) => builder.inst(insts32.ri, [lhs.op(), Op::Imm(i)]),
            MCValue::Reg(r) => builder.inst(insts32.rr, [lhs.op(), r.op()]),
            MCValue::Indirect(r, r_off) => {
                builder.inst(insts32.rm, [lhs.op(), r.op(), offset_op(r_off)])
            }
        }
        MCValue::Reg(MCReg::Virtual(lhs))
    }

    fn comparison(
        &mut self,
        builder: &mut Builder,
        values: &[MCValue],
        tag: Tag,
        a: Ref,
        b: Ref,
        ty: IrType,
    ) -> MCValue {
        let a = get_ref(values, a);
        let b = get_ref(values, b);
        match ty {
            IrType::I32 => {}
            _ => todo!("handle comparison of type {ty:?}"),
        }
        let mut flip = false;
        match (a, b) {
            (MCValue::None | MCValue::PtrOffset(_, _), _)
            | (_, MCValue::None | MCValue::PtrOffset(_, _)) => unreachable!(),
            (MCValue::Undef, _) | (_, MCValue::Undef) => return MCValue::Undef,
            (MCValue::Reg(a), MCValue::Reg(b)) => {
                builder.inst(Inst::cmprr32, [a.op(), b.op()]);
            }
            (MCValue::Reg(r), MCValue::Imm(imm)) => {
                builder.inst(Inst::cmpri32, [r.op(), Op::Imm(imm)]);
            }
            (MCValue::Imm(imm), MCValue::Reg(r)) => {
                flip = true;
                builder.inst(Inst::cmpri32, [r.op(), Op::Imm(imm)]);
            }
            (MCValue::Imm(a), MCValue::Imm(b)) => {
                let a: i32 = a.try_into().unwrap();
                let b: i32 = b.try_into().unwrap();
                let value = match tag {
                    Tag::Eq => a == b,
                    Tag::NE => a != b,
                    Tag::LT => a < b,
                    Tag::GT => a > b,
                    Tag::LE => a <= b,
                    Tag::GE => a >= b,
                    _ => unreachable!(),
                };
                return MCValue::Imm(value as _);
            }
            (MCValue::Reg(r), MCValue::Indirect(m, m_off)) => {
                builder.inst(
                    Inst::cmprm32,
                    [r.op(), m.op(), Op::Imm(m_off as i64 as u64)],
                );
            }
            (MCValue::Indirect(m, m_off), MCValue::Reg(r)) => {
                flip = true;
                builder.inst(
                    Inst::cmprm32,
                    [r.op(), m.op(), Op::Imm(m_off as i64 as u64)],
                );
            }
            (MCValue::Indirect(a, a_off), MCValue::Imm(imm)) => {
                builder.inst(Inst::cmpmi32, [a.op(), offset_op(a_off), Op::Imm(imm)]);
            }
            (MCValue::Imm(imm), MCValue::Indirect(b, b_off)) => {
                flip = true;
                builder.inst(Inst::cmpmi32, [b.op(), offset_op(b_off), Op::Imm(imm)]);
            }
            (MCValue::Indirect(a, a_off), MCValue::Indirect(b, b_off)) => {
                let va = builder.reg();
                builder.inst(Inst::movrm32, [va.op(), a.op(), offset_op(a_off)]);
                builder.inst(Inst::cmprm32, [va.op(), b.op(), offset_op(b_off)]);
            }
        };
        let r = builder.reg();
        let set_inst = match (tag, flip) {
            (Tag::Eq, _) => Inst::setz8,
            (Tag::NE, _) => Inst::setnz8,
            (Tag::LT, false) | (Tag::GE, true) => Inst::setl8,
            (Tag::GT, false) | (Tag::LE, true) => Inst::setg8,
            (Tag::LE, false) | (Tag::GT, true) => Inst::setle8,
            (Tag::GE, false) | (Tag::LT, true) => Inst::setge8,
            _ => unreachable!(),
        };
        builder.inst(set_inst, [r.op()]);
        MCValue::Reg(MCReg::Virtual(r))
    }
}

fn offset_op(offset: i32) -> Op<Reg> {
    Op::Imm(offset as i64 as u64)
}

struct BinOpInsts {
    rr: Inst,
    ri: Inst,
    is_rri: bool,
    rm: Inst,
}

#[derive(Debug, Clone, Copy)]
enum MCValue {
    /// this value doesn't have any runtime bits
    None,
    /// value is undefined and can be assumed to be any value at runtime
    Undef,
    /// an immediate (pointer-sized) constant value
    Imm(u64),
    /// value is located in a register
    Reg(MCReg),
    /// represents a constant offset from a register
    PtrOffset(MCReg, i32),
    /// value is located at a constant offset from an address in a register
    Indirect(MCReg, i32),
}
impl MCValue {
    // Converts the value to either a value in a register or an intermediate, potentially loading it
    // and applying constant offsets.
    pub fn to_ri32(self, builder: &mut Builder) -> RI {
        match self {
            Self::None => unreachable!("ri value should have a runtime value"),
            Self::Undef => RI::Undef,
            Self::Imm(imm) => RI::Imm(imm),
            Self::Reg(r) => RI::Reg(r),
            Self::PtrOffset(r, i) => {
                let vreg = builder.reg();
                builder.inst(Inst::Copy, [vreg.op(), r.op()]);
                builder.inst(Inst::addri32, [vreg.op(), Op::Imm(i as u64)]);
                RI::Reg(MCReg::Virtual(vreg))
            }
            Self::Indirect(r, off) => {
                let vreg = builder.reg();
                builder.inst(Inst::movrm32, [vreg.op(), r.op(), Op::Imm(off as u64)]);
                RI::Reg(MCReg::Virtual(vreg))
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum RI {
    Undef,
    Imm(u64),
    Reg(MCReg),
}

#[derive(Debug, Clone, Copy)]
pub enum MCReg {
    Register(Reg),
    Virtual(VReg),
}
impl MCReg {
    pub fn op(self) -> Op<Reg> {
        match self {
            MCReg::Register(r) => Op::Reg(r),
            MCReg::Virtual(r) => Op::VReg(r),
        }
    }
}

fn get_ref(values: &[MCValue], r: ir::Ref) -> MCValue {
    match r.into_val() {
        Some(ir::RefVal::True) => MCValue::Imm(1),
        Some(ir::RefVal::False) => MCValue::Imm(0),
        Some(ir::RefVal::Unit) => MCValue::None,
        Some(ir::RefVal::Undef) => MCValue::Undef,
        None => values[r.into_ref().unwrap() as usize],
    }
}
