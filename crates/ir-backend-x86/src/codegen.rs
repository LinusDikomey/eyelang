use std::collections::VecDeque;

use ir::{
    mc::{BlockBuilder, MachineIR, MirBlock, Op, VReg},
    BlockIndex, FunctionId, IrType, Tag,
};

use crate::isa::{Inst, Reg};

const ABI_PARAM_REGISTERS: [Reg; 6] = [Reg::edi, Reg::esi, Reg::edx, Reg::ecx, Reg::r8d, Reg::r9d];
const ABI_RETURN_REGISTER: Reg = Reg::rax;

struct Gen<'a> {
    function: &'a ir::Function,
    body: &'a ir::FunctionIr,
    types: &'a ir::IrTypes,
    stack_setup_indices: Vec<u32>,
    block_queue: VecDeque<BlockIndex>,
    block_map: Box<[Option<MirBlock>]>,
}
impl<'a> Gen<'a> {
    fn create_epilogue(&mut self, builder: &mut BlockBuilder<Inst>) {
        self.stack_setup_indices.push(builder.next_inst_index());
        builder.inst(Inst::addri64, [Op::Reg(Reg::rsp), Op::Imm(0)]);
        builder.inst(Inst::pop64, [Op::Reg(Reg::rbp)]);
    }

    fn gen_inst(
        &mut self,
        inst: ir::Instruction,
        builder: &mut BlockBuilder<Inst>,
        values: &[MCValue],
    ) -> MCValue {
        match inst.tag {
            Tag::Param => {
                assert!(matches!(self.types[inst.ty], IrType::I32), "TODO");
                let param_idx = unsafe { inst.data.int32 };
                let abi_reg = *ABI_PARAM_REGISTERS
                    .get(param_idx as usize)
                    .expect("TODO: more than 6 args");
                let reg = builder.reg();
                builder.inst(Inst::Copy, [reg.op(), Op::Reg(abi_reg)]);
                MCValue::Register(MCReg::Virtual(reg))
            }
            Tag::Int => MCValue::Imm(unsafe { inst.data.int }),
            Tag::Decl => {
                let layout = self.types.layout(self.types[unsafe { inst.data.ty }]);
                let offset = -(builder.create_stack_slot(layout) as i64) - layout.size as i64;
                MCValue::PtrOffset(MCReg::Register(Reg::rbp), offset)
            }
            Tag::Load => {
                let ptr = get_ref(&values, unsafe { inst.data.un_op });
                match self.types[inst.ty] {
                    IrType::Unit => MCValue::None,
                    IrType::I32 => match ptr {
                        MCValue::None => panic!(),
                        MCValue::Undef => MCValue::Undef,
                        MCValue::Imm(_) => todo!("load from addresses"),
                        MCValue::Register(r) => MCValue::PtrOffset(r, 0),
                        MCValue::Indirect(r, offset) => {
                            let loaded = builder.reg();
                            builder
                                .inst(Inst::movrm32, [loaded.op(), r.op(), Op::Imm(offset as u64)]);
                            MCValue::Register(MCReg::Virtual(loaded))
                        }
                        MCValue::PtrOffset(r, offset) => MCValue::Indirect(r, offset),
                    },
                    ty => todo!("load value of type {ty:?}"),
                }
            }
            Tag::Store => {
                let (ptr, val) = unsafe { inst.data.bin_op };
                let ptr = get_ref(&values, ptr);
                let val = get_ref(&values, val);
                match val {
                    MCValue::None | MCValue::Undef => {}
                    MCValue::Imm(val) => match ptr {
                        MCValue::PtrOffset(ptr, off) => {
                            builder
                                .inst(Inst::movmi32, [ptr.op(), Op::Imm(off as u64), Op::Imm(val)]);
                        }
                        _ => todo!("store imm into {ptr:?}"),
                    },
                    MCValue::Register(r) => match ptr {
                        MCValue::PtrOffset(ptr, off) => {
                            builder.inst(Inst::movmr32, [ptr.op(), Op::Imm(off as u64), r.op()]);
                        }
                        _ => todo!("store register into {ptr:?}"),
                    },
                    MCValue::PtrOffset(_, _) => todo!(),
                    MCValue::Indirect(_, _) => todo!(),
                }
                MCValue::None
            }
            Tag::Add => {
                let ty = self.types[inst.ty];
                let (lhs, rhs) = unsafe { inst.data.bin_op };
                let lhs = get_ref(&values, lhs);
                let rhs = get_ref(&values, rhs);
                let changed_reg = match ty {
                    IrType::I32 => match (lhs, rhs) {
                        (MCValue::Register(lhs), MCValue::Register(rhs)) => {
                            builder.inst(Inst::addrr32, [lhs.op(), rhs.op()]);
                            lhs
                        }
                        (MCValue::Register(reg), MCValue::Imm(imm))
                        | (MCValue::Imm(imm), MCValue::Register(reg)) => {
                            builder.inst(Inst::addri32, [reg.op(), Op::Imm(imm)]);
                            reg
                        }
                        (MCValue::Register(reg), MCValue::Indirect(ptr, off))
                        | (MCValue::Indirect(ptr, off), MCValue::Register(reg)) => {
                            builder.inst(Inst::addrm32, [reg.op(), ptr.op(), Op::Imm(off as u64)]);
                            reg
                        }
                        (MCValue::Indirect(a, a_off), other) => {
                            let reg = builder.reg();
                            builder.inst(Inst::movrm32, [reg.op(), a.op(), Op::Imm(a_off as u64)]);
                            match other {
                                MCValue::Indirect(b, b_off) => builder
                                    .inst(Inst::addrm32, [reg.op(), b.op(), Op::Imm(b_off as u64)]),
                                MCValue::Imm(imm) => {
                                    builder.inst(Inst::addri32, [reg.op(), Op::Imm(imm)])
                                }
                                _ => unreachable!(),
                            }
                            MCReg::Virtual(reg)
                        }
                        _ => todo!("add {lhs:?}, {rhs:?}"),
                    },
                    _ => todo!("handle add of type {ty:?}"),
                };

                let v = builder.reg();
                builder.inst(Inst::Copy, [Op::VReg(v), changed_reg.op()]);
                MCValue::Register(MCReg::Virtual(v))
            }
            Tag::Ret => {
                let val = unsafe { inst.data.un_op };
                let val = get_ref(&values, val);
                match self.function.return_type {
                    IrType::Unit => {
                        self.create_epilogue(builder);
                        builder.inst(Inst::ret0, []);
                    }
                    IrType::I32 => {
                        match val {
                            MCValue::Register(MCReg::Register(Reg::eax)) => {}
                            MCValue::Register(reg) => {
                                builder.inst(Inst::Copy, [Op::Reg(Reg::eax), reg.op()]);
                            }
                            MCValue::Imm(imm) => {
                                builder.inst(Inst::Copy, [Op::Reg(Reg::eax), Op::Imm(imm)]);
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
                let (extra_start, arg_count) = unsafe { inst.data.extra_len };
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
                    IrType::I32 => MCValue::Register(MCReg::Register(ABI_RETURN_REGISTER)),
                    IrType::Const(_) => panic!(),
                    other => todo!("handle call with type {other:?}"),
                }
            }
            Tag::Eq | Tag::NE | Tag::LT | Tag::GT | Tag::LE | Tag::GE => {
                let (a, b) = unsafe { inst.data.bin_op };
                let ty = self.body.get_ref_ty(a, self.types);
                let a = get_ref(&values, a);
                let b = get_ref(&values, b);
                match ty {
                    IrType::I32 => {}
                    _ => todo!("handle comparison of type {ty:?}"),
                }
                let mut flip = false;
                match (a, b) {
                    (MCValue::Register(a), MCValue::Register(b)) => {
                        builder.inst(Inst::cmprr32, [a.op(), b.op()]);
                    }
                    (MCValue::Register(r), MCValue::Imm(imm)) => {
                        builder.inst(Inst::cmpri32, [r.op(), Op::Imm(imm)]);
                    }
                    (MCValue::Imm(imm), MCValue::Register(r)) => {
                        flip = true;
                        builder.inst(Inst::cmpri32, [r.op(), Op::Imm(imm)]);
                    }
                    _ => todo!("handle comparison with {b:?}"),
                };
                let r = builder.reg();
                let set_inst = match (inst.tag, flip) {
                    (Tag::Eq, _) => Inst::setz8,
                    (Tag::NE, _) => Inst::setnz8,
                    (Tag::LT, false) | (Tag::GE, true) => Inst::setl8,
                    (Tag::GT, false) | (Tag::LE, true) => Inst::setg8,
                    (Tag::LE, false) | (Tag::GT, true) => Inst::setle8,
                    (Tag::GE, false) | (Tag::LT, true) => Inst::setge8,
                    _ => unreachable!(),
                };
                builder.inst(set_inst, [r.op()]);
                MCValue::Register(MCReg::Virtual(r))
            }
            Tag::Goto => {
                let block = unsafe { inst.data.block };
                let mir_block = self.get_queue_block(builder, block);
                builder.inst(Inst::jmp, [Op::Block(mir_block)]);
                builder.register_successor(mir_block);
                MCValue::Undef
            }
            Tag::Branch => {
                let (cond, extra_branches) = unsafe { inst.data.ref_int };
                let i = extra_branches as usize;
                let t = ir::BlockIndex::from_bytes(self.body.extra[i..i + 4].try_into().unwrap());
                let f =
                    ir::BlockIndex::from_bytes(self.body.extra[i + 4..i + 8].try_into().unwrap());
                let t = self.get_queue_block(builder, t);
                let f = self.get_queue_block(builder, f);
                builder.register_successor(t);
                builder.register_successor(f);
                match get_ref(&values, cond) {
                    MCValue::Register(r) => {
                        builder.inst(Inst::cmpri8, [r.op(), Op::Imm(0)]);
                        builder.inst(Inst::je, [Op::Block(f)]);
                        builder.inst(Inst::jmp, [Op::Block(t)]);
                        // TODO: generate true block next, create false block label
                        // builder.inst(Inst::je, [Op::Block(f)]);
                    }
                    value => todo!("handle branch cond value {value:?}"),
                }
                MCValue::Undef
            }
            _ => todo!("implement ir instruction tag {:?} in x86 backend", inst.tag),
        }
    }

    fn get_queue_block(&mut self, builder: &mut BlockBuilder<Inst>, block: BlockIndex) -> MirBlock {
        *self.block_map[block.idx() as usize].get_or_insert_with(|| {
            let mir_block = builder.create_block();
            self.block_queue.push_back(block);
            mir_block
        })
    }
}

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

    let mut block_map = vec![None; body.blocks().len()].into_boxed_slice();

    let mir_entry_block = builder.create_block();
    builder.register_successor(mir_entry_block);
    block_map[BlockIndex::ENTRY.idx() as usize] = Some(mir_entry_block);

    let mut gen = Gen {
        function,
        body,
        types,
        stack_setup_indices,
        block_queue: VecDeque::from([BlockIndex::ENTRY]),
        block_map,
    };

    while let Some(block) = gen.block_queue.pop_front() {
        let mir_block =
            *gen.block_map[block.idx() as usize].get_or_insert_with(|| mir.create_block());
        let mut builder = mir.begin_block(mir_block);
        for (i, inst) in body.get_block(block) {
            values[i as usize] = gen.gen_inst(inst, &mut builder, &values);
        }
    }

    for idx in gen.stack_setup_indices {
        mir.replace_operand(idx, 1, Op::Imm(mir.stack_offset()));
    }
    mir
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
    Register(MCReg),
    /// represents a pointer offset from a register
    PtrOffset(MCReg, i64),
    /// value is located at a constant offset from an address in a register
    Indirect(MCReg, i64),
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
