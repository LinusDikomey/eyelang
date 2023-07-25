use std::fmt::{self, Display};

use color_format::cwrite;

use crate::ir;

/// Emits C code
pub mod c;

#[cfg(feature = "llvm-backend")]
/// Uses the LLVM library to emit LLVM IR
pub mod llvm;

pub mod x86_64;

/// Represents the machine code of a single function
pub struct MachineCode<I: Inst> {
    /// the instructions along with a start index into `arguments`
    instructions: Vec<(I, u32)>,
    arguments: Vec<Arg<I::Register>>,
}
impl<I: Inst> MachineCode<I> {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            arguments: Vec::new(),
        }
    }

    pub fn inst<const N: usize>(&mut self, i: I, args: [Arg<I::Register>; N]) {
        debug_assert_eq!(i.arg_types().len(), N);
        let argument_index = self.arguments.len() as u32;
        self.arguments.extend(args);
        self.instructions.push((i, argument_index));
    }
}
impl<I: Inst + Display> Display for MachineCode<I> where I::Register: Display {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Machine Code:")?;
        for inst in &self.instructions {
            write!(f, "  ")?;
            let arg_types = inst.0.arg_types();
            let args = &self.arguments[inst.1 as usize .. inst.1 as usize + arg_types.len()];
            let defs = args
                .iter()
                .zip(arg_types.iter().copied())
                .map_while(|(arg, ty)| (ty != ArgType::Use).then_some(arg));

            let uses = args
                .iter()
                .zip(arg_types.iter().copied())
                .skip_while(|(_, ty)| *ty == ArgType::Def)
                .map(|x| x.0);

            let mut has_defs = false;
            for def in defs {
                has_defs = true;
                write!(f, "{} ", def)?;
            }

            if has_defs {
                write!(f, "= ")?;
            }
            cwrite!(f, "#y<{}>", inst.0)?;
            for arg in uses {
                write!(f, " {}", arg)?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

pub enum Arg<R> {
    Virtual(VirtualRegister),
    Physical(R),
    Imm(u64),
}
impl<R: Display> Display for Arg<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Virtual(virt) => cwrite!(f, "#cyan<%{}>", virt.0),
            Self::Physical(phys) => cwrite!(f, "#green<{}>", phys),
            Self::Imm(x) => cwrite!(f, "#red<{}>", x),
        }
    }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirtualRegister(u32);

pub trait Inst {
    type Register;
    /// (number of result args, number of input args)
    fn arg_types(&self) -> &'static [ArgType];
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ArgType {
    Use,
    Def,
    UseDef,
}

pub fn generate(module: &ir::Module) {
    x86_64::generate(module);
}

//pub mod x86;
