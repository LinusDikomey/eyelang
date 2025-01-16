use ir2::{PrimitiveInfo, Type, TypeIds, Types};

use crate::isa::Reg;

mod systemv;

pub trait Abi {
    fn from_function(
        types: &Types,
        params: TypeIds,
        return_ty: Type,
        primitives: &[PrimitiveInfo],
    ) -> Self
    where
        Self: Sized;
    fn arg_registers(&self) -> &[Reg];
    fn get_param(&self, param: u32) -> ParamStorage;
    fn return_place(&self) -> ReturnPlace;
}

pub fn get_function_abi(
    types: &Types,
    params: TypeIds,
    return_ty: Type,
    primitives: &[PrimitiveInfo],
) -> Box<dyn Abi> {
    // TODO: decide abi from target
    Box::new(systemv::FunctionAbi::from_function(
        types, params, return_ty, primitives,
    ))
}

#[derive(Debug, Clone, Copy)]
pub enum ParamStorage {
    None,
    Reg(u32),
    TwoRegs(u32),
    PtrReg(u32),
}

#[derive(Debug, Clone, Copy)]
pub enum ReturnPlace {
    None,
    Reg(Reg),
    TwoRegs(Reg, Reg),
}
