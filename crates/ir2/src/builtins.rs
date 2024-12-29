//! Builtin dialect, instructions that users never directly interact with

use crate::{instructions, ModuleId, ModuleOf};

instructions! {
    Builtin "builtin" BuiltinInsts

    Nothing;
    BlockArg;
    Undef;
}

pub const BUILTIN: ModuleOf<Builtin> = ModuleOf(ModuleId::BUILTINS, std::marker::PhantomData);
