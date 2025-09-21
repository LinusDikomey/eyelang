use std::fmt;

use ir::{
    BlockId, MCReg, ModuleOf, Type, TypeIds,
    mc::{Abi, BackendState},
    modify::IrModify,
    pipeline::FunctionPass,
};

use crate::arch::x86::{Reg, X86};

pub struct PrologueEpilogueInsertion {
    pub x86: ModuleOf<X86>,
    pub abi: &'static dyn Abi<X86>,
}
impl fmt::Debug for PrologueEpilogueInsertion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x86::PrologueEpilogueInsertion")
    }
}
impl FunctionPass<BackendState> for PrologueEpilogueInsertion {
    fn run(
        &self,
        env: &ir::Environment,
        types: &ir::Types,
        ir: ir::FunctionIr,
        _name: &str,
        state: &mut BackendState,
    ) -> (ir::FunctionIr, Option<ir::Types>) {
        let mut ir = IrModify::new(ir);
        let used_regs = ir::mc::used_physical_registers::<Reg>(&ir, env);
        let to_save = used_regs & self.abi.callee_saved() & !(Reg::rsp.bit() | Reg::rbp.bit());

        // PERF: avoid cloning the entire types table after reworking ir types
        let mut types = types.clone();
        let unit = types.add(Type::Tuple(TypeIds::EMPTY));

        let start = ir.get_original_block_start(BlockId::ENTRY);
        let x86 = self.x86;

        if state.stack_size > 0 {
            ir.add_before(env, start, x86.push_r64(MCReg::from_phys(Reg::rbp), unit));
            ir.add_before(
                env,
                start,
                x86.mov_rr64(MCReg::from_phys(Reg::rbp), MCReg::from_phys(Reg::rsp), unit),
            );
            state.stack_size = state.stack_size.next_multiple_of(16);
            ir.add_before(
                env,
                start,
                x86.sub_ri64(MCReg::from_phys(Reg::rsp), state.stack_size, unit),
            );
        }

        for reg in Reg::UNIQUE_BITS {
            if to_save & reg.bit() != super::isa::RegisterBits::default() {
                ir.add_before(env, start, x86.push_r64(MCReg::from_phys(reg), unit));
            }
        }

        for r in ir.refs() {
            let inst = ir.get_inst(r);
            if inst
                .as_module(self.x86)
                .is_some_and(|inst| inst.op().is_ret())
            {
                // insert epilogue before return
                for reg in Reg::UNIQUE_BITS.into_iter().rev() {
                    if to_save & reg.bit() != super::isa::RegisterBits::default() {
                        ir.add_before(env, r, x86.pop_r64(MCReg::from_phys(reg), unit));
                    }
                }
                if state.stack_size != 0 {
                    ir.add_before(
                        env,
                        r,
                        x86.add_ri64(MCReg::from_phys(Reg::rsp), state.stack_size, unit),
                    );
                    ir.add_before(env, r, x86.pop_r64(MCReg::from_phys(Reg::rbp), unit));
                }
            }
        }

        (ir.finish_and_compress(env), Some(types))
    }
}
