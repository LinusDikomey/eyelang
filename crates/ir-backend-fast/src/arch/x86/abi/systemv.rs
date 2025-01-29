use ir::{Primitive, PrimitiveInfo, Type, TypeIds, Types};

use crate::arch::x86::isa::Reg;

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
    fn from_function(
        types: &Types,
        params: TypeIds,
        return_ty: Type,
        primitives: &[PrimitiveInfo],
    ) -> Self {
        let mut next_gp_reg = 0;

        let mut registers = Vec::new();

        let params = params
            .iter()
            .map(|param_ty| match types[param_ty] {
                Type::Primitive(p) => match Primitive::try_from(p).unwrap() {
                    Primitive::Unit => ParamStorage::None,
                    ty @ (Primitive::I1
                    | Primitive::I8
                    | Primitive::U8
                    | Primitive::I16
                    | Primitive::U16
                    | Primitive::I32
                    | Primitive::U32
                    | Primitive::I64
                    | Primitive::U64
                    | Primitive::Ptr) => {
                        let size_idx = match ty {
                            Primitive::I1 | Primitive::I8 | Primitive::U8 => 3,
                            Primitive::I16 | Primitive::U16 => 2,
                            Primitive::I32 | Primitive::U32 => 1,
                            Primitive::I64 | Primitive::U64 | Primitive::Ptr => 0,
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
                    Primitive::I128 | Primitive::U128 => {
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
                    Primitive::F32 | Primitive::F64 => todo!("handle floating point params"),
                },
                aggregate_ty @ (Type::Tuple(_) | Type::Array(_, _)) => {
                    let layout = ir::type_layout(aggregate_ty, types, primitives);
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
            })
            .collect();

        let return_layout = ir::type_layout(return_ty, types, primitives);
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
