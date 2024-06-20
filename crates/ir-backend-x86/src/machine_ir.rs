use std::fmt;

use crate::elf::{self, ElfObjectWriter};

pub struct MachineIR {
    insts: Vec<(Inst, [Operand; 4])>,
}
impl MachineIR {
    pub fn new() -> Self {
        Self { insts: Vec::new() }
    }

    pub fn inst<const N: usize>(&mut self, inst: Inst, operands: [Operand; N]) {
        let mut all_operands = [Operand::None; 4];
        all_operands[..operands.len()].copy_from_slice(&operands);
        self.insts.push((inst, all_operands));
    }

    pub fn write(&self, text: &mut Vec<u8>) {
        for (inst, operands) in &self.insts {
            match inst {
                Inst::addrr32 => {
                    let [Operand::Register(a), Operand::Register(b), _, _] = operands else {
                        panic!()
                    };
                    text.extend([0x03, 0b11_000_000 | a.encode() << 3 | b.encode()]);
                }
                Inst::movrr32 => {
                    let [Operand::Register(a), Operand::Register(b), _, _] = operands else {
                        panic!()
                    };
                    text.extend([0x89, 0b11_000_000 | a.encode() << 3 | b.encode()]);
                }
                Inst::ret => {
                    text.push(0xc3);
                }
                _ => todo!(),
            }
        }
    }
}
impl fmt::Display for MachineIR {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (inst, operands) in &self.insts {
            write!(f, "  {}", inst.to_str())?;
            for op in operands
                .iter()
                .copied()
                .take_while(|&op| op != Operand::None)
            {
                write!(f, " {}", op)?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

#[allow(non_camel_case_types)]
pub enum Ops {
    None,
    r,
    rr,
    rrr,
    rrrr,
    ri,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Operand {
    None,
    Register(Register),
    Memory, // TODO
    Immediate(u64),
}
impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::None => write!(f, "none"),
            Self::Register(reg) => write!(f, "{}", reg.to_str()),
            Self::Memory => write!(f, "TODO(memory)"),
            Self::Immediate(imm) => write!(f, "{imm}"),
        }
    }
}

macro_rules! value_enum {
    ($name: ident $($variant: ident)*) => {
        #[rustfmt::skip]
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        pub enum $name {
            $($variant, )*
        }

        impl $name {
            fn to_str(self) -> &'static str {
                match self {
                    $(Self::$variant => stringify!($variant),)*
                }
            }
        }
    };
}
value_enum! { Register
        rax rcx rdx rbx rsp rbp rsi rdi
        eax ecx edx ebx esp ebp esi edi
        r8 r9 r10 r11 r12 r13 r14 r15
        e8 e9 e10 e11 e12 e13 e14 e15
}
impl Register {
    pub fn size(self) -> RegSize {
        match self {
            Self::rax
            | Self::rcx
            | Self::rdx
            | Self::rbx
            | Self::rsp
            | Self::rbp
            | Self::rsi
            | Self::rdi
            | Self::r8
            | Self::r9
            | Self::r10
            | Self::r11
            | Self::r12
            | Self::r13
            | Self::r14
            | Self::r15 => RegSize::S8,
            Self::eax
            | Self::ecx
            | Self::edx
            | Self::ebx
            | Self::esp
            | Self::ebp
            | Self::esi
            | Self::edi
            | Self::e8
            | Self::e9
            | Self::e10
            | Self::e11
            | Self::e12
            | Self::e13
            | Self::e14
            | Self::e15 => RegSize::S4,
        }
    }

    pub fn encode(self) -> u8 {
        match self {
            Self::rax | Self::eax => 0b_000,
            Self::rcx => 0b_001,
            Self::rdx => 0b_010,
            Self::rbx => 0b_011,
            Self::esi => 0b_110,
            Self::edi => 0b_111,
            reg => todo!("encode {reg:?}"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegSize {
    S1,
    S2,
    S4,
    S8,
}

value_enum! { Inst
    addrr32
    movrr32
    movri32
    call
    cmp
    ret
}

#[derive(Clone, Copy)]
pub enum MCValue {
    None,
    Undef,
    Imm(u64),
    Register(Register),
}
