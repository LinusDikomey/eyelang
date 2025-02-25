use crate::{instructions, Parameter, Usage};

instructions! {
    Mc "mc" McInsts

    IncomingBlockArgs !varargs = Some(Parameter::MCReg(Usage::Def));

    /// usage is special-cased in register allocator, used in pairs where each first register
    /// is assigned to the second one.
    Copy !varargs = Some(Parameter::MCReg(Usage::Use));
}
