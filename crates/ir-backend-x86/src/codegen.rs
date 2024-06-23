use ir::{
    mc::{MachineIR, Operand},
    FunctionId, IrType,
};

use crate::machine_ir::{Inst, MCReg, MCValue, Register};

const ABI_PARAM_REGISTERS: [Register; 6] = [
    Register::edi,
    Register::esi,
    Register::edx,
    Register::ecx,
    Register::r8d,
    Register::r9d,
];
const ABI_RETURN_REGISTER: Register = Register::rax;

pub fn codegen(function: &ir::FunctionIr, types: &ir::IrTypes) -> MachineIR<Inst> {
    let mut mir = MachineIR::new();
    let mut values = vec![MCValue::None; function.inst.len()];

    for (i, inst) in function.inst.iter().enumerate() {
        values[i] = match inst.tag {
            ir::Tag::BlockBegin => MCValue::None,
            ir::Tag::Param => {
                assert!(matches!(types[inst.ty], IrType::I32), "TODO");
                let param_idx = unsafe { inst.data.int32 };
                let abi_reg = *ABI_PARAM_REGISTERS
                    .get(param_idx as usize)
                    .expect("TODO: more than 6 args");
                let reg = mir.reg();
                mir.inst(Inst::movrr32, [reg.op(), Operand::Reg(abi_reg)]);
                MCValue::Register(MCReg::Virtual(reg))
            }
            ir::Tag::Int => MCValue::Imm(unsafe { inst.data.int }),
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
                            mir.inst(Inst::addri32, [reg.op(), Operand::Imm(imm)]);
                            reg
                        }
                        _ => todo!(),
                    },
                    _ => todo!("handle add of type {ty:?}"),
                };

                let v = mir.reg();
                mir.inst(Inst::movrr32, [Operand::VReg(v), changed_reg.op()]);
                MCValue::Register(MCReg::Virtual(v))
            }
            ir::Tag::Ret => {
                let val = unsafe { inst.data.un_op };
                let val = get_ref(&values, val);
                match val {
                    MCValue::Register(MCReg::Register(Register::eax)) => {}
                    MCValue::Register(reg) => {
                        // assert!(matches!(ty, IrType::I32), "TODO");
                        mir.inst(Inst::movrr32, [Operand::Reg(Register::eax), reg.op()]);
                    }
                    MCValue::Imm(imm) => {
                        mir.inst(
                            Inst::movri32,
                            [Operand::Reg(Register::eax), Operand::Imm(imm)],
                        );
                    }
                    MCValue::None | MCValue::Undef => {}
                }
                mir.inst(Inst::ret32, []);
                MCValue::None
            }
            ir::Tag::Call => {
                let (extra_start, arg_count) = unsafe { inst.data.extra_len };
                let start = extra_start as usize;
                let mut bytes = [0; 8];
                bytes.copy_from_slice(&function.extra[start..start + 8]);
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
                mir.inst(Inst::call, [Operand::Func(func)]);
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
    mir
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
