use crate::{
    Environment, MCReg, ModuleOf, Ref, Refs, TypeId, Types,
    mc::{Mc, McInst, Register},
    modify::IrModify,
    slots::Slots,
};

pub trait Abi<I: McInst> {
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
    fn implement_call(
        &self,
        call_inst: Ref,
        ir: &mut IrModify,
        env: &Environment,
        mc: ModuleOf<Mc>,
        i: ModuleOf<I>,
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
        i: ModuleOf<I>,
        types: &Types,
        regs: &Slots<MCReg>,
        r: Ref,
        unit: TypeId,
    );
    fn callee_saved(&self) -> <I::Reg as Register>::RegisterBits;
    fn caller_saved(&self) -> <I::Reg as Register>::RegisterBits;
    fn return_regs(&self, value_count: u32) -> <I::Reg as Register>::RegisterBits;
}
