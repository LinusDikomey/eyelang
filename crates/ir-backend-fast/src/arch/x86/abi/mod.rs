use ir::{
    Environment, MCReg, ModuleOf, Ref, Refs, TypeId, Types, mc::Mc, modify::IrModify, slots::Slots,
};

mod systemv;

pub trait Abi {
    fn implement_params(
        &self,
        args: Refs,
        ir: &mut IrModify,
        env: &Environment,
        mc: ModuleOf<Mc>,
        types: &Types,
        regs: &Slots<MCReg>,
        unit: TypeId,
    );
    fn implement_return(
        &self,
        value: Ref,
        ir: &mut IrModify,
        env: &Environment,
        mc: ModuleOf<Mc>,
        types: &Types,
        regs: &Slots<MCReg>,
        before: Ref,
        unit: TypeId,
    );
}

pub fn get_target_abi() -> &'static dyn Abi {
    // TODO: decide abi based on target
    &systemv::SystemV
}
