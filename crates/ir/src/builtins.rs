//! Builtin dialect, instructions that users never directly interact with

use crate::{Instruction, ModuleId, ModuleOf, instructions};

instructions! {
    Builtin "builtin" BuiltinInsts

    Nothing;
    BlockArg;
    Undef;
}

pub const BUILTIN: ModuleOf<Builtin> = ModuleOf(ModuleId::BUILTINS, std::marker::PhantomData);

pub(crate) fn block_arg_inst(ty: crate::TypeId) -> Instruction {
    Instruction {
        function: crate::FunctionId {
            module: ModuleId::BUILTINS,
            function: Builtin::BlockArg.id(),
        },
        args: [0, 0],
        ty,
    }
}
