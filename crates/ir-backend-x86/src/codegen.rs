use ir::{
    mc::{MachineIR, Op, VReg},
    FunctionId, IrType,
};

use crate::isa::{Inst, Reg};

const ABI_PARAM_REGISTERS: [Reg; 6] = [Reg::edi, Reg::esi, Reg::edx, Reg::ecx, Reg::r8d, Reg::r9d];
const ABI_RETURN_REGISTER: Reg = Reg::rax;

pub fn codegen(
    body: &ir::FunctionIr,
    function: &ir::Function,
    types: &ir::IrTypes,
) -> MachineIR<Inst> {
    let mut mir = MachineIR::new();
    let mut values = vec![MCValue::None; body.inst.len()];

    mir.inst(Inst::push64, [Op::Reg(Reg::rbp)]);
    mir.inst(Inst::movrr64, [Op::Reg(Reg::rbp), Op::Reg(Reg::rsp)]);
    // This instruction's immediate operand will be updated at the end with the used stack space.
    // In the future, the stack size might be known a priori when the IR tracks a list of stack
    // slots.
    let mut stack_setup_indices = vec![mir.insts.len()];
    mir.inst(Inst::subri64, [Op::Reg(Reg::rsp), Op::Imm(0)]);

    let mut epilogue = |mir: &mut MachineIR<Inst>| {
        stack_setup_indices.push(mir.insts.len());
        mir.inst(Inst::addri64, [Op::Reg(Reg::rsp), Op::Imm(0)]);
        mir.inst(Inst::pop64, [Op::Reg(Reg::rbp)]);
    };

    for (i, inst) in body.inst.iter().enumerate() {
        values[i] = match inst.tag {
            ir::Tag::BlockBegin => MCValue::None,
            ir::Tag::Param => {
                assert!(matches!(types[inst.ty], IrType::I32), "TODO");
                let param_idx = unsafe { inst.data.int32 };
                let abi_reg = *ABI_PARAM_REGISTERS
                    .get(param_idx as usize)
                    .expect("TODO: more than 6 args");
                let reg = mir.reg();
                mir.inst(Inst::movrr32, [reg.op(), Op::Reg(abi_reg)]);
                MCValue::Register(MCReg::Virtual(reg))
            }
            ir::Tag::Int => MCValue::Imm(unsafe { inst.data.int }),
            ir::Tag::Decl => {
                let layout = types.layout(types[unsafe { inst.data.ty }]);
                let offset = -(mir.create_stack_slot(layout) as i64) - layout.size as i64;
                MCValue::PtrOffset(MCReg::Register(Reg::rbp), offset)
            }
            ir::Tag::Load => {
                let ptr = get_ref(&values, unsafe { inst.data.un_op });
                match types[inst.ty] {
                    IrType::Unit => MCValue::None,
                    IrType::I32 => match ptr {
                        MCValue::None => panic!(),
                        MCValue::Undef => MCValue::Undef,
                        MCValue::Imm(_) => todo!("load from addresses"),
                        MCValue::Register(r) => MCValue::PtrOffset(r, 0),
                        MCValue::Indirect(r, offset) => {
                            let loaded = mir.reg();
                            mir.inst(Inst::movrm32, [loaded.op(), r.op(), Op::Imm(offset as u64)]);
                            MCValue::Register(MCReg::Virtual(loaded))
                        }
                        MCValue::PtrOffset(r, offset) => MCValue::Indirect(r, offset),
                    },
                    ty => todo!("load value of type {ty:?}"),
                }
            }
            ir::Tag::Store => {
                let (ptr, val) = unsafe { inst.data.bin_op };
                let ptr = get_ref(&values, ptr);
                let val = get_ref(&values, val);
                match val {
                    MCValue::None | MCValue::Undef => {}
                    MCValue::Imm(val) => match ptr {
                        MCValue::PtrOffset(ptr, off) => {
                            mir.inst(Inst::movmi32, [ptr.op(), Op::Imm(off as u64), Op::Imm(val)]);
                        }
                        _ => todo!("store imm into {ptr:?}"),
                    },
                    MCValue::Register(r) => match ptr {
                        MCValue::PtrOffset(ptr, off) => {
                            mir.inst(Inst::movmr32, [ptr.op(), Op::Imm(off as u64), r.op()]);
                        }
                        _ => todo!("store register into {ptr:?}"),
                    },
                    MCValue::PtrOffset(_, _) => todo!(),
                    MCValue::Indirect(_, _) => todo!(),
                }
                MCValue::None
            }
            ir::Tag::Add => {
                let ty = types[inst.ty];
                let (lhs, rhs) = unsafe { inst.data.bin_op };
                let lhs = get_ref(&values, lhs);
                let rhs = get_ref(&values, rhs);
                let changed_reg = match ty {
                    IrType::I32 => match (lhs, rhs) {
                        (MCValue::Register(lhs), MCValue::Register(rhs)) => {
                            mir.inst(Inst::addrr32, [lhs.op(), rhs.op()]);
                            lhs
                        }
                        (MCValue::Register(reg), MCValue::Imm(imm))
                        | (MCValue::Imm(imm), MCValue::Register(reg)) => {
                            mir.inst(Inst::addri32, [reg.op(), Op::Imm(imm)]);
                            reg
                        }
                        (MCValue::Register(reg), MCValue::Indirect(ptr, off))
                        | (MCValue::Indirect(ptr, off), MCValue::Register(reg)) => {
                            mir.inst(Inst::addrm32, [reg.op(), ptr.op(), Op::Imm(off as u64)]);
                            reg
                        }
                        (MCValue::Indirect(a, a_off), MCValue::Indirect(b, b_off)) => {
                            let reg = mir.reg();
                            mir.inst(Inst::movrm32, [reg.op(), a.op(), Op::Imm(a_off as u64)]);
                            mir.inst(Inst::addrm32, [reg.op(), b.op(), Op::Imm(b_off as u64)]);
                            MCReg::Virtual(reg)
                        }
                        _ => todo!("add {lhs:?}, {rhs:?}"),
                    },
                    _ => todo!("handle add of type {ty:?}"),
                };

                let v = mir.reg();
                mir.inst(Inst::movrr32, [Op::VReg(v), changed_reg.op()]);
                MCValue::Register(MCReg::Virtual(v))
            }
            ir::Tag::Ret => {
                let val = unsafe { inst.data.un_op };
                let val = get_ref(&values, val);
                match function.return_type {
                    IrType::Unit => {
                        epilogue(&mut mir);
                        mir.inst(Inst::ret0, []);
                    }
                    IrType::I32 => {
                        match val {
                            MCValue::Register(MCReg::Register(Reg::eax)) => {}
                            MCValue::Register(reg) => {
                                mir.inst(Inst::movrr32, [Op::Reg(Reg::eax), reg.op()]);
                            }
                            MCValue::Imm(imm) => {
                                mir.inst(Inst::movri32, [Op::Reg(Reg::eax), Op::Imm(imm)]);
                            }
                            MCValue::Indirect(reg, offset) => mir.inst(
                                Inst::movrm32,
                                [Op::Reg(Reg::eax), reg.op(), Op::Imm(offset as u64)],
                            ),
                            MCValue::PtrOffset(_, _) => todo!("calculate ptr addr for ret"),
                            MCValue::None | MCValue::Undef => {}
                        }
                        epilogue(&mut mir);
                        mir.inst(Inst::ret32, []);
                    }
                    ty => todo!("handle return type {ty:?}"),
                }
                MCValue::None
            }
            ir::Tag::Call => {
                let (extra_start, arg_count) = unsafe { inst.data.extra_len };
                let start = extra_start as usize;
                let mut bytes = [0; 8];
                bytes.copy_from_slice(&body.extra[start..start + 8]);
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
                mir.inst(Inst::call, [Op::Func(func)]);
                match types[inst.ty] {
                    IrType::Unit => MCValue::Undef,
                    IrType::I32 => MCValue::Register(MCReg::Register(ABI_RETURN_REGISTER)),
                    IrType::Const(_) => panic!(),
                    other => todo!("handle call with type {other:?}"),
                }
            }
            _ => todo!("implement ir instruction tag {:?} in x86 backend", inst.tag),
        };
    }
    for idx in stack_setup_indices {
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
