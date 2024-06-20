use crate::machine_ir::{Inst, MCValue, MachineIR, Operand, RegSize, Register};

const ABI_PARAM_REGISTERS: [Register; 6] = [
    Register::edi,
    Register::esi,
    Register::edx,
    Register::ecx,
    Register::e8,
    Register::e9,
];
const ABI_RETURN_REGISTER: Register = Register::rax;

pub fn codegen(function: &ir::FunctionIr) -> MachineIR {
    let mut mir = MachineIR::new();
    let mut values = vec![MCValue::None; function.inst.len()];

    for (i, inst) in function.inst.iter().enumerate() {
        values[i] = match inst.tag {
            ir::Tag::BlockBegin => MCValue::None,
            ir::Tag::Param => {
                let param_idx = unsafe { inst.data.int32 };
                MCValue::Register(
                    *ABI_PARAM_REGISTERS
                        .get(param_idx as usize)
                        .expect("TODO: more than 6 args"),
                )
            }
            ir::Tag::Add => {
                let (lhs, rhs) = unsafe { inst.data.bin_op };
                let lhs = get_ref(&values, lhs);
                let rhs = get_ref(&values, rhs);
                match (lhs, rhs) {
                    (MCValue::Register(lhs), MCValue::Register(rhs)) => {
                        assert_eq!(lhs.size(), RegSize::S4, "TODO");
                        mir.inst(
                            Inst::addrr32,
                            [Operand::Register(lhs), Operand::Register(rhs)],
                        );
                        MCValue::Register(lhs)
                    }
                    (MCValue::Register(reg), MCValue::Imm(imm))
                    | (MCValue::Imm(imm), MCValue::Register(reg)) => {
                        todo!()
                        //mir.inst(Inst::add, [Operand::Register(reg), Operand::Immediate(imm)]);
                        //MCValue::Register(reg)
                    }
                    _ => todo!(),
                }
            }
            ir::Tag::Ret => {
                let val = get_ref(&values, unsafe { inst.data.un_op });
                match val {
                    MCValue::Register(Register::eax) => {}
                    MCValue::Register(reg) => {
                        assert_eq!(reg.size(), RegSize::S4, "TODO");
                        mir.inst(
                            Inst::movrr32,
                            [Operand::Register(reg), Operand::Register(Register::eax)],
                        );
                    }
                    MCValue::Imm(imm) => {
                        mir.inst(
                            Inst::movri32,
                            [Operand::Register(Register::eax), Operand::Immediate(imm)],
                        );
                    }
                    MCValue::None | MCValue::Undef => {}
                }
                mir.inst(Inst::ret, []);
                MCValue::None
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
