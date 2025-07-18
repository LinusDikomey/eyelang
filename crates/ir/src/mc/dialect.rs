use crate::{Parameter, Usage, instructions};

instructions! {
    Mc "mc" McInsts

    IncomingBlockArgs !varargs = Some(Parameter::MCReg(Usage::DefUse));

    /// usage is special-cased in register allocator, used in pairs where each first register
    /// is assigned to the second one.
    Copy !varargs = Some(Parameter::MCReg(Usage::Use));
}
