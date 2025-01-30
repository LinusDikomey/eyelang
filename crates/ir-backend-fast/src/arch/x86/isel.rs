use ir::{
    mc::RegClass,
    modify::IrModify,
    rewrite::{Rewrite, RewriteCtx, Visitor},
    BlockGraph, BlockId, BlockTarget, Environment, FunctionId, FunctionIr, MCReg, Parameter,
    Primitive, PrimitiveInfo, Ref, Type, TypeIds, Types,
};

use crate::{
    arch::x86::{
        abi::{self, ReturnPlace},
        isa::Reg,
    },
    MCValue,
};

pub fn codegen(
    env: &Environment,
    body: &ir::FunctionIr,
    function: &ir::Function,
    types: &ir::Types,
) -> (FunctionIr, ir::Types) {
    /*
    let mut mir = MachineIR::new();
    let mut builder = mir.begin_block(MirBlock::ENTRY);
    let mut values = vec![MCValue::None; body.inst_count() as usize];

    builder.inst(Inst::push64, [Op::Reg(Reg::rbp)]);
    builder.inst(Inst::movrr64, [Op::Reg(Reg::rbp), Op::Reg(Reg::rsp)]);
    // This instruction's immediate operand will be updated at the end with the used stack space.
    // In the future, the stack size might be known a priori when the IR tracks a list of stack
    // slots.
    let stack_setup_indices = vec![builder.next_inst_index()];
    builder.inst(Inst::subri64, [Op::Reg(Reg::rsp), Op::Imm(0)]);
    */

    /*
    let abi = abi::get_function_abi(
        types,
        function.params().iter().map(|p| {
            let Parameter::RefOf(ty) = p else { panic!() };
            ty
        }),
        function.return_type().unwrap(),
        env.primitives(),
    );
    */

    //let (mir_entry_block, entry_block_args) =
    //    builder.create_block(abi.arg_registers().iter().map(|r| r.class()));
    //let (mir_entry_block, entry_block_args) = builder.create_block([]);
    //builder.register_successor(mir_entry_block);
    /*
    builder.build_copyargs(
        Inst::Copyargs,
        entry_block_args.iter().map(|vreg| vreg.op()),
        abi.arg_registers().iter().copied().map(Op::Reg),
    );
    */

    /*
    let block_map = body
        .block_ids()
        .map(|block| {
            let (mir_block, mir_args) = if block == BlockId::ENTRY {
                (mir_entry_block, entry_block_args)
            } else {
                builder.create_block(block_args_to_reg_classes(
                    body,
                    types,
                    env.primitives(),
                    body.get_block_args(block),
                ))
            };
            let mut mir_arg_iter = mir_args.iter();
            for arg in body.get_block_args(block) {
                let arg_ty = body.get_ref_ty(arg);
                let mir_classes = block_arg_regs(function.types()[arg_ty], types, env.primitives());
                let value = match mir_classes {
                    ZeroToTwo::Zero => MCValue::None,
                    ZeroToTwo::One(_) => MCValue::Reg(MCReg::Virtual(mir_arg_iter.next().unwrap())),
                    ZeroToTwo::Two(_, _) => MCValue::TwoRegs(
                        MCReg::Virtual(mir_arg_iter.next().unwrap()),
                        MCReg::Virtual(mir_arg_iter.next().unwrap()),
                    ),
                };
                values[arg.idx()] = value;
            }
            (mir_block, mir_args)
        })
        .collect();
    */
    /*
    let mut gen = Gen {
        env,
        modules,
        //abi,
        function,
        body,
        types,
        stack_setup_indices,
        block_map,
    };
    */
    let mut rewriter = InstructionSelector::new(env);
    let mut body = IrModify::new(body.clone());
    let mut types = types.clone();
    let mut ctx = IselCtx {
        unit: types.add(Type::Tuple(ir::TypeIds::EMPTY)),
        values: vec![MCValue::None; body.inst_count() as usize].into_boxed_slice(),
    };
    ir::rewrite::rewrite_in_place(&mut body, &types, env, &mut ctx, rewriter);

    /*
    let graph = BlockGraph::calculate(gen.body, gen.env);

    for &block in graph.postorder().iter().rev() {
        let mir_block = gen.block_map[block.idx()].0;
        let mut builder = mir.begin_block(mir_block);
        for (i, inst) in body.get_block(block) {
            values[i.idx()] = gen.gen_inst(inst, block, &mut builder, &values, body);
        }
    }
    */

    /*
    for idx in stack_setup_indices {
        mir.replace_operand(idx, 1, offset_op(mir.stack_offset() as i32));
    }
    mir
    */
    (body.finish_and_compress(env), types)
}

fn block_args_to_reg_classes<'a, I: IntoIterator<Item = ir::Ref>>(
    ir: &'a ir::FunctionIr,
    types: &'a ir::Types,
    primitives: &'a [PrimitiveInfo],
    args: I,
) -> impl 'a + Iterator<Item = RegClass>
where
    I::IntoIter: 'a,
{
    args.into_iter().flat_map(|arg| {
        let ty = ir.get_ref_ty(arg);
        block_arg_regs(types[ty], types, primitives)
    })
}

fn block_arg_regs(ty: Type, types: &Types, primitives: &[PrimitiveInfo]) -> ZeroToTwo<RegClass> {
    match ty {
        ir::Type::Primitive(p) => match Primitive::try_from(p).unwrap() {
            Primitive::Unit => ZeroToTwo::Zero,
            Primitive::I1 | Primitive::I8 | Primitive::U8 => ZeroToTwo::One(RegClass::GP8),
            Primitive::I16 | Primitive::U16 => ZeroToTwo::One(RegClass::GP16),
            Primitive::I32 | Primitive::U32 => ZeroToTwo::One(RegClass::GP32),
            Primitive::I64 | Primitive::U64 | Primitive::Ptr => ZeroToTwo::One(RegClass::GP64),
            Primitive::I128 | Primitive::U128 => ZeroToTwo::Two(RegClass::GP64, RegClass::GP64),
            Primitive::F32 => ZeroToTwo::One(RegClass::F32),
            Primitive::F64 => ZeroToTwo::One(RegClass::F64),
        },
        ir::Type::Array(_, _) | ir::Type::Tuple(_) => {
            match ir::type_layout(ty, types, primitives).size {
                0 => ZeroToTwo::Zero,
                1 => ZeroToTwo::One(RegClass::GP8),
                2 => ZeroToTwo::One(RegClass::GP16),
                3..=4 => ZeroToTwo::One(RegClass::GP32),
                5..=8 => ZeroToTwo::One(RegClass::GP64),
                9..=16 => ZeroToTwo::Two(RegClass::GP64, RegClass::GP64),
                _ => todo!("large block args"),
            }
        }
    }
}

enum ZeroToTwo<T> {
    Zero,
    One(T),
    Two(T, T),
}
impl<T> Default for ZeroToTwo<T> {
    fn default() -> Self {
        Self::Zero
    }
}
impl<T> Iterator for ZeroToTwo<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match std::mem::take(self) {
            Self::Zero => None,
            Self::One(a) => {
                *self = Self::Zero;
                Some(a)
            }
            Self::Two(a, b) => {
                *self = Self::One(b);
                Some(a)
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}
impl<T> ExactSizeIterator for ZeroToTwo<T> {
    fn len(&self) -> usize {
        match self {
            Self::Zero => 0,
            Self::One(_) => 1,
            Self::Two(_, _) => 2,
        }
    }
}

struct Gen<'a> {
    env: &'a mut ir::Environment,
    //abi: Box<dyn abi::Abi>,
    function: &'a ir::Function,
    body: &'a mut ir::FunctionIr,
    types: &'a ir::Types,
    stack_setup_indices: Vec<u32>,
    block_map: Box<[(BlockId, u32)]>,
}
impl Gen<'_> {
    /*
    fn create_epilogue(&mut self, builder: &mut Builder) {
        self.stack_setup_indices.push(builder.next_inst_index());
        builder.inst(Inst::addri64, [Op::Reg(Reg::rsp), Op::Imm(0)]);
        builder.inst(Inst::pop64, [Op::Reg(Reg::rbp)]);
    }
    */

    fn gen_inst(
        &mut self,
        inst: &ir::Instruction,
        block: BlockId,
        //builder: &mut Builder<'_>,
        values: &[MCValue],
        body: &FunctionIr,
    ) -> MCValue {
        todo!()
        /*
        match inst.tag {
            Tag::Nothing => MCValue::None,
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
                let ptr = get_ref(values, inst.data.un_op());
                match ptr {
                    MCValue::None | MCValue::TwoRegs(_, _) => unreachable!(),
                    MCValue::Undef => MCValue::Undef,
                    MCValue::Imm(_) => todo!("load from addresses"),
                    MCValue::Reg(r) => MCValue::PtrOffset(r, 0),
                    MCValue::Indirect(r, offset) => match self.types[inst.ty] {
                        IrType::Unit => MCValue::None,
                        IrType::I32 | IrType::U32 => {
                            let loaded = builder.reg(RegClass::GP32);
                            builder
                                .inst(Inst::movrm32, [loaded.op(), r.op(), Op::Imm(offset as u64)]);
                            MCValue::Reg(MCReg::Virtual(loaded))
                        }
                        IrType::I64 | IrType::U64 | IrType::Ptr => {
                            let loaded = builder.reg(RegClass::GP64);
                            builder
                                .inst(Inst::movrm64, [loaded.op(), r.op(), Op::Imm(offset as u64)]);
                            MCValue::Reg(MCReg::Virtual(loaded))
                        }
                        ty => todo!("load value of type {ty:?}"),
                    },
                    MCValue::PtrOffset(r, offset) => MCValue::Indirect(r, offset),
                }
            }
            Tag::Store => self.store(builder, values, inst.data.bin_op()),
            Tag::MemberPtr => {
                let (ptr, elem_types, elem_idx) = inst.data.member_ptr(extra);
                let offset = ir::offset_in_tuple(elem_types, elem_idx, self.types);
                match get_ref(values, ptr) {
                    MCValue::None | MCValue::TwoRegs(_, _) => unreachable!(),
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
                        let vreg = builder.reg(RegClass::GP64);
                        builder.inst(Inst::movrm64, [vreg.op(), r.op(), offset_op(r_off)]);
                        MCValue::PtrOffset(
                            MCReg::Virtual(vreg),
                            r_off
                                + TryInto::<i32>::try_into(offset)
                                    .expect("TODO: handle large offsets"),
                        )
                    }
                }
            }
            Tag::MemberValue => todo!("MemberValue"),
            Tag::InsertMember => todo!("InsertMember"),
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
            Tag::Rem => todo!(),
            Tag::Ret => {
                let val = inst.data.un_op();
                let val = get_ref(values, val);
                match self.function.return_type {
                    IrType::Unit => {
                        self.create_epilogue(builder);
                        builder.inst(Inst::ret0, []);
                    }
                    IrType::I32 => {
                        match val {
                            MCValue::None | MCValue::PtrOffset(_, _) | MCValue::TwoRegs(_, _) => {
                                unreachable!()
                            }
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
                            MCValue::Undef => {}
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
                match self.abi.return_place() {
                    ReturnPlace::None => MCValue::None,
                    ReturnPlace::Reg(r) => {
                        MCValue::Reg(MCReg::Virtual(builder.copy_to_fresh(Op::Reg(r), r.class())))
                    }
                    ReturnPlace::TwoRegs(r1, r2) => {
                        let vr1 = builder.reg(RegClass::GP64);
                        let vr2 = builder.reg(RegClass::GP64);
                        builder.build_copyargs(
                            Inst::Copyargs,
                            [vr1.op(), vr2.op()],
                            [Op::Reg(r1), Op::Reg(r2)],
                        );
                        MCValue::TwoRegs(MCReg::Virtual(vr1), MCReg::Virtual(vr2))
                    }
                }
            }
            Tag::FunctionPtr | Tag::CallPtr => todo!(),
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
                match get_ref(values, cond) {
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
            Tag::ArrayIndex => todo!(),
            Tag::String => todo!(),
            Tag::Neg => todo!(),
            Tag::Not => todo!(),
            Tag::Or => todo!(),
            Tag::And => todo!(),
            Tag::Xor => todo!(),
            Tag::Rol => todo!(),
            Tag::Ror => todo!(),
            Tag::CastInt => todo!(),
            Tag::CastFloat => todo!(),
            Tag::CastIntToFloat => todo!(),
            Tag::CastFloatToInt => todo!(),
            Tag::IntToPtr => todo!(),
            Tag::PtrToInt => todo!(),
            Tag::Asm => todo!(),
        }
        */
    }

    /*
    fn copy_block_args(
        &self,
        builder: &mut Builder,
        values: &[MCValue],
        target: BlockId,
        extra_index: usize,
    ) {
        let t_count = self.body.get_block_args(target).count();
        let mut bytes = [0; 4];
        let t_to = self.body.get_block_args(target).map(|arg| {
            let MCValue::Reg(MCReg::Virtual(v)) = values[arg.idx()] else {
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
    */

    /*
    fn store(
        &mut self,
        builder: &mut Builder,
        values: &[MCValue],
        (ptr, val): (Ref, Ref),
    ) -> MCValue {
        let ptr = get_ref(values, ptr);
        let ty = self.types[self.body.get_ref_ty(val)];
        let val = get_ref(values, val);
        let MCValue::PtrOffset(ptr, off) = ptr else {
            todo!("handle store into {ptr:?}")
        };
        match val {
            MCValue::None | MCValue::Undef => {}
            MCValue::Imm(val) => {
                let inst = match ty {
                    IrType::Unit | IrType::Tuple(_) | IrType::Array(_, _) => {
                        unreachable!()
                    }
                    IrType::U1 | IrType::I8 | IrType::U8 => Inst::movmi8,
                    IrType::I16 | IrType::U16 => Inst::movmi16,
                    IrType::I32 | IrType::U32 => Inst::movmi32,
                    IrType::I64 | IrType::U64 | IrType::Ptr => Inst::movmi64,
                    IrType::I128 | IrType::U128 | IrType::F32 | IrType::F64 => todo!(),
                };
                builder.inst(inst, [ptr.op(), offset_op(off), Op::Imm(val)])
            }
            MCValue::Reg(r) => {
                let layout = ir::type_layout(ty, self.types);
                let inst = match layout.size {
                    0 => unreachable!(),
                    1 => Inst::movmr8,
                    2 => Inst::movmr16,
                    4 => Inst::movmr32,
                    8 => Inst::movmr64,
                    3 | 5..=7 => todo!("store size {}", layout.size),
                    size => {
                        unreachable!("value of size {size} can't be stored in register")
                    }
                };
                builder.inst(inst, [ptr.op(), offset_op(off), r.op()])
            }
            MCValue::TwoRegs(r1, r2) => {
                let layout = ir::type_layout(ty, self.types);
                match layout.size {
                    9..=15 => todo!(),
                    16 => {
                        builder.inst(Inst::movmr64, [ptr.op(), offset_op(off), r1.op()]);
                        builder.inst(Inst::movmr64, [ptr.op(), offset_op(off + 8), r2.op()]);
                        return MCValue::None;
                    }
                    _ => unreachable!(),
                }
            }
            MCValue::PtrOffset(_, _) => todo!(),
            MCValue::Indirect(r, r_off) => {
                // TODO: handle other sizes than 32 bits
                let tmp = builder.reg(RegClass::GP32);
                builder.inst(Inst::movrm32, [tmp.op(), r.op(), offset_op(r_off)]);
                builder.inst(Inst::movmr32, [ptr.op(), offset_op(off), tmp.op()]);
            }
        }
        MCValue::None
    }
        */

    /*
    fn bin_op_commutative(
        &mut self,
        builder: &mut Builder,
        values: &[MCValue],
        (lhs, rhs): (Ref, Ref),
        ty: ir::Type,
        insts32: BinOpInsts,
        fold: impl Fn(u64, u64) -> u64,
    ) -> MCValue {
        let lhs = get_ref(values, lhs);
        let rhs = get_ref(values, rhs);
        let (insts, class, movrm) = match ty {
            IrType::I32 | IrType::U32 => (insts32, RegClass::GP32, Inst::movrm32),
            _ => todo!(),
        };
        let changed_reg = match (lhs, rhs) {
            (MCValue::Undef, _) | (_, MCValue::Undef) => return MCValue::Undef,
            (MCValue::Imm(a), MCValue::Imm(b)) => return MCValue::Imm(fold(a, b)),
            (MCValue::Reg(lhs), MCValue::Reg(rhs)) => {
                builder.inst(insts.rr, [lhs.op(), rhs.op()]);
                lhs
            }
            (MCValue::Reg(reg), MCValue::Imm(imm)) | (MCValue::Imm(imm), MCValue::Reg(reg)) => {
                if insts.is_rri {
                    let out = builder.reg(class);
                    builder.inst(insts.ri, [out.op(), reg.op(), Op::Imm(imm)]);
                    MCReg::Virtual(out)
                } else {
                    builder.inst(insts.ri, [reg.op(), Op::Imm(imm)]);
                    reg
                }
            }
            (MCValue::Reg(reg), MCValue::Indirect(ptr, off))
            | (MCValue::Indirect(ptr, off), MCValue::Reg(reg)) => {
                builder.inst(insts.rm, [reg.op(), ptr.op(), Op::Imm(off as u64)]);
                reg
            }
            (MCValue::Indirect(a, a_off), other) | (other, MCValue::Indirect(a, a_off)) => {
                let reg = builder.reg(class);
                builder.inst(movrm, [reg.op(), a.op(), offset_op(a_off)]);
                match other {
                    MCValue::Indirect(b, b_off) => {
                        builder.inst(insts.rm, [reg.op(), b.op(), offset_op(b_off)])
                    }
                    MCValue::Imm(imm) => builder.inst(insts.ri, [reg.op(), Op::Imm(imm)]),
                    _ => unreachable!(),
                }
                return MCValue::Reg(MCReg::Virtual(reg));
            }
            (MCValue::PtrOffset(_, _) | MCValue::None | MCValue::TwoRegs(_, _), _)
            | (_, MCValue::PtrOffset(_, _) | MCValue::None | MCValue::TwoRegs(_, _)) => {
                unreachable!()
            }
        };

        MCValue::Reg(MCReg::Virtual(
            builder.copy_to_fresh(changed_reg.op(), class),
        ))
    }
        */

    /*
    fn bin_op_noncommutative(
        &mut self,
        builder: &mut Builder,
        values: &[MCValue],
        (lhs, rhs): (Ref, Ref),
        ty: ir::Type,
        insts32: BinOpInsts,
        fold: impl Fn(u64, u64) -> u64,
    ) -> MCValue {
        let (insts, class, movri, movrm) = match ty {
            IrType::I32 | IrType::U32 => (insts32, RegClass::GP32, Inst::movri32, Inst::movrm32),
            _ => todo!("handle op ty {ty:?}"),
        };
        let lhs = get_ref(values, lhs);
        let rhs = get_ref(values, rhs);
        let lhs = match (lhs, rhs) {
            (MCValue::None | MCValue::PtrOffset(_, _) | MCValue::TwoRegs(_, _), _)
            | (_, MCValue::None | MCValue::PtrOffset(_, _) | MCValue::TwoRegs(_, _)) => {
                unreachable!()
            }
            (MCValue::Undef, _) | (_, MCValue::Undef) => return MCValue::Undef,
            (MCValue::Imm(a), MCValue::Imm(b)) => return MCValue::Imm(fold(a, b)),
            (MCValue::Imm(lhs), _) => {
                let reg = builder.reg(class);
                builder.inst(movri, [reg.op(), Op::Imm(lhs)]);
                reg
            }
            (MCValue::Reg(a), _) => builder.copy_to_fresh(a.op(), class),
            (MCValue::Indirect(a, a_off), _) => {
                let reg = builder.reg(class);
                builder.inst(movrm, [reg.op(), a.op(), offset_op(a_off)]);
                reg
            }
        };
        match rhs {
            MCValue::None | MCValue::Undef | MCValue::PtrOffset(_, _) | MCValue::TwoRegs(_, _) => {
                unreachable!()
            }
            MCValue::Imm(i) => builder.inst(insts.ri, [lhs.op(), Op::Imm(i)]),
            MCValue::Reg(r) => builder.inst(insts.rr, [lhs.op(), r.op()]),
            MCValue::Indirect(r, r_off) => {
                builder.inst(insts.rm, [lhs.op(), r.op(), offset_op(r_off)])
            }
        }
        MCValue::Reg(MCReg::Virtual(lhs))
    }
    */

    /*
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
        let class = match ty {
            IrType::I32 => RegClass::GP32,
            _ => todo!("handle comparison of type {ty:?}"),
        };
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
                let va = builder.reg(class);
                builder.inst(Inst::movrm32, [va.op(), a.op(), offset_op(a_off)]);
                builder.inst(Inst::cmprm32, [va.op(), b.op(), offset_op(b_off)]);
            }
            (MCValue::TwoRegs(_, _), _) | (_, MCValue::TwoRegs(_, _)) => {
                todo!("handle comparison with large integers")
            }
        };
        let r = builder.reg(class);
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
    */
}

pub struct IselCtx {
    unit: ir::TypeId,
    values: Box<[MCValue]>,
}
impl ir::rewrite::RewriteCtx for IselCtx {}
impl IselCtx {
    fn set(&mut self, r: Ref, value: MCValue) {
        self.values[r.idx()] = value;
    }

    fn get(&mut self, r: Ref) -> MCValue {
        match r {
            Ref::TRUE => MCValue::Imm(1),
            Ref::FALSE => MCValue::Imm(0),
            Ref::UNIT => MCValue::None,
            r => self.values[r.idx()],
        }
    }
}

ir::visitor! {
    InstructionSelector,
    Rewrite,
    ir, types, inst, env,
    ctx: IselCtx;

    use arith: ir::dialect::Arith;
    use tuple: ir::dialect::Tuple;
    use mem: ir::dialect::Mem;
    use cf: ir::dialect::Cf;

    use x86: crate::arch::x86::isa::X86;

    patterns:
    (%r = arith.Int (#x)) => {
        let reg = ir.new_reg();
        ctx.set(r, MCValue::Reg(reg));
        x86.movri32(reg, x.try_into().unwrap(), ctx.unit)
    };
    (%r = cf.Ret value) => {
        let MCValue::Reg(reg) = ctx.get(value) else {
            todo!()
        };
        // TODO: physical registers for eax here
        let eax = MCReg::from_phys(Reg::eax);
        let inst = x86.movrr32(eax, reg, ctx.unit);
        ir.add_before(env, r, inst);
        x86.ret32(ctx.unit)
    };
    (cf.Goto (@b b_args)) => {
        x86.jmp(BlockTarget(b, &[]), ctx.unit)
    };
    (%r = cf.Branch (%lt = arith.LT a b) (@b1 b1_args) (@b2 b2_args)) => {
        let MCValue::Reg(a) = ctx.get(a) else {
            todo!()
        };
        let MCValue::Reg(b) = ctx.get(b) else {
            todo!()
        };
    // FIXME: this is only valid when this is the only use of the LT
        ir.replace(env, lt, x86.cmprr32(a, b, ctx.unit));
        let jl = x86.jl(BlockTarget(b1, &[]), ctx.unit);
        ir.add_before(env, r, jl);
        x86.jmp(BlockTarget(b2, &[]), ctx.unit)
    };
}

/*
fn offset_op(offset: i32) -> Op<Reg> {
    Op::Imm(offset as i64 as u64)
}

struct BinOpInsts {
    rr: Inst,
    ri: Inst,
    is_rri: bool,
    rm: Inst,
}

fn get_ref(values: &[MCValue], r: ir::Ref) -> MCValue {
    match r {
        Ref::TRUE => MCValue::Imm(1),
        Ref::FALSE => MCValue::Imm(0),
        Ref::UNIT => MCValue::None,
        _ => values[r.idx()],
    }
}
*/
