use ir::{IrType, IrTypes, TypeRefs};

use crate::isa::Reg;

use super::{Abi, ParamStorage, ReturnPlace};

const ABI_PARAM_REGISTERS: [[Reg; 4]; 6] = [
    [Reg::rdi, Reg::edi, Reg::di, Reg::dl],
    [Reg::rsi, Reg::esi, Reg::si, Reg::sil],
    [Reg::rdx, Reg::edx, Reg::dx, Reg::dl],
    [Reg::rcx, Reg::ecx, Reg::cx, Reg::cl],
    [Reg::r8, Reg::r8d, Reg::r8w, Reg::r8b],
    [Reg::r9, Reg::r9d, Reg::r9w, Reg::r9b],
];

pub struct FunctionAbi {
    params: Vec<ParamStorage>,
    registers: Vec<Reg>,
    return_place: ReturnPlace,
}
impl Abi for FunctionAbi {
    fn from_function(types: &IrTypes, params: TypeRefs, return_ty: IrType) -> Self {
        let mut next_gp_reg = 0;

        let mut registers = Vec::new();

        let params = params
            .iter()
            .map(|param_ty| match types[param_ty] {
                IrType::Unit => ParamStorage::None,
                ty @ (IrType::U1
                | IrType::I8
                | IrType::U8
                | IrType::I16
                | IrType::U16
                | IrType::I32
                | IrType::U32
                | IrType::I64
                | IrType::U64
                | IrType::Ptr) => {
                    let size_idx = match ty {
                        IrType::U1 | IrType::I8 | IrType::U8 => 3,
                        IrType::I16 | IrType::U16 => 2,
                        IrType::I32 | IrType::U32 => 1,
                        IrType::I64 | IrType::U64 | IrType::Ptr => 0,
                        _ => unreachable!(),
                    };
                    if let Some(&reg) = ABI_PARAM_REGISTERS.get(next_gp_reg) {
                        next_gp_reg += 1;
                        let idx = registers.len() as _;
                        registers.push(reg[size_idx]);
                        ParamStorage::Reg(idx)
                    } else {
                        todo!("handle stack passed parameters")
                    }
                }
                IrType::I128 | IrType::U128 => {
                    if next_gp_reg + 1 < ABI_PARAM_REGISTERS.len() {
                        let r1 = ABI_PARAM_REGISTERS[next_gp_reg][0];
                        let r2 = ABI_PARAM_REGISTERS[next_gp_reg + 1][0];
                        next_gp_reg += 2;
                        let idx = registers.len() as _;
                        registers.extend([r1, r2]);
                        ParamStorage::TwoRegs(idx)
                    } else {
                        todo!("handle stack passed parameters")
                    }
                }
                aggregate_ty @ (IrType::Tuple(_) | IrType::Array(_, _)) => {
                    let layout = ir::type_layout(aggregate_ty, types);
                    if layout.size == 0 {
                        ParamStorage::None
                    } else if layout.size <= 8 {
                        if let Some(&reg) = ABI_PARAM_REGISTERS.get(next_gp_reg) {
                            next_gp_reg += 1;
                            let idx = registers.len() as _;
                            registers.push(reg[0]);
                            ParamStorage::Reg(idx)
                        } else {
                            todo!("handle stack passed parameters")
                        }
                    } else if layout.size <= 16 {
                        if next_gp_reg + 1 < ABI_PARAM_REGISTERS.len() {
                            let r1 = ABI_PARAM_REGISTERS[next_gp_reg][0];
                            let r2 = ABI_PARAM_REGISTERS[next_gp_reg + 1][0];
                            next_gp_reg += 2;
                            let idx = registers.len() as _;
                            registers.extend([r1, r2]);
                            ParamStorage::TwoRegs(idx)
                        } else {
                            todo!("handle stack passed parameters")
                        }
                    } else {
                        todo!("handle larger aggregates")
                    }
                }
                IrType::F32 | IrType::F64 => todo!("handle floating point params"),
                IrType::Const(_) => unreachable!(),
            })
            .collect();

        let return_layout = ir::type_layout(return_ty, types);
        let return_place = match return_layout.size {
            0 => ReturnPlace::None,
            1 => ReturnPlace::Reg(Reg::al),
            2 => ReturnPlace::Reg(Reg::ax),
            4 => ReturnPlace::Reg(Reg::eax),
            8 => ReturnPlace::Reg(Reg::rax),
            16 => ReturnPlace::TwoRegs(Reg::rax, Reg::rdx),
            _ => todo!("handle stack passed return values"),
        };
        Self {
            params,
            registers,
            return_place,
        }
    }

    fn arg_registers(&self) -> &[Reg] {
        &self.registers
    }

    fn get_param(&self, param: u32) -> ParamStorage {
        self.params[param as usize]
    }

    fn return_place(&self) -> ReturnPlace {
        self.return_place
    }
}
