use std::fmt::{self, Display};

use color_format::{cwriteln, cwrite};

use crate::ir;

pub enum Instruction<I> {
    Specific {
        instruction: I,
        arguments_index: u32,
    },
    Label(ir::BlockIndex),
}

/// Represents the machine code of a single function
pub struct MachineCode<I: Inst> {
    /// the instructions along with a start index into `arguments`
    instructions: Vec<Instruction<I>>,
    arguments: Vec<Arg<I::Register>>,
}
impl<I: Inst> MachineCode<I> {
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            arguments: Vec::new(),
        }
    }

    pub fn label(&mut self, index: ir::BlockIndex) {
        self.instructions.push(Instruction::Label(index));
    }

    pub fn inst<const N: usize>(&mut self, instruction: I, args: [Arg<I::Register>; N]) {
        debug_assert_eq!(instruction.arg_types().len(), N);
        let arguments_index = self.arguments.len() as u32;
        self.arguments.extend(args);
        self.instructions.push(Instruction::Specific { instruction, arguments_index });
    }
}
impl<I: Inst + Display> Display for MachineCode<I> where I::Register: Display {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Machine Code:")?;
        for inst in &self.instructions {
            match inst {
                Instruction::Label(i) => cwriteln!(f, "#blue<block{}>:", i.idx())?,
                Instruction::Specific { instruction, arguments_index: arg_idx } => {
                    write!(f, "  ")?;
                    let arg_types = instruction.arg_types();
                    let args = &self.arguments[*arg_idx as usize .. *arg_idx as usize + arg_types.len()];
                    let defs = args
                        .iter()
                        .zip(arg_types.iter().copied())
                        .map_while(|(arg, ty)| (!matches!(ty, ArgType::Use | ArgType::Label)).then_some(arg));

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
                    cwrite!(f, "#y<{}>", instruction)?;
                    for arg in uses {
                        write!(f, " {}", arg)?;
                    }
                    writeln!(f)?;
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Arg<R> {
    Virtual(VirtualRegister),
    Physical(R),
    Imm(u64),
    Label(ir::BlockIndex),
}
impl<R: Display> Display for Arg<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Virtual(virt) => cwrite!(f, "#cyan<%{}>", virt.0),
            Self::Physical(phys) => cwrite!(f, "#green<{}>", phys),
            Self::Imm(x) => cwrite!(f, "#red<{}>", x),
            Self::Label(i) => cwrite!(f, "#blue<block{}>", i.idx()),
        }
    }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VirtualRegister(u32);
impl VirtualRegister {
    pub const UNASSIGNED: Self = Self(0);
    pub const FIRST: Self = Self(0);

    pub fn next(self) -> Self {
        Self(self.0 + 1)
    }
}

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
    Label,
}
