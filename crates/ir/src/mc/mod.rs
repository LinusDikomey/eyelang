mod dialect;
mod parcopy;
mod regalloc;

pub use dialect::{Mc, McInsts};
pub use parcopy::ParcopySolver;
pub use regalloc::regalloc;

use std::ops::{BitAnd, BitOr, Not};

pub trait Register: 'static + Copy {
    const DEFAULT: Self;
    type RegisterBits: Copy
        + BitAnd<Output = Self::RegisterBits>
        + Not<Output = Self::RegisterBits>
        + BitOr<Output = Self::RegisterBits>;
    const NO_BITS: Self::RegisterBits;
    const ALL_BITS: Self::RegisterBits;

    fn to_str(self) -> &'static str;
    fn encode(self) -> u32;
    fn decode(value: u32) -> Self;

    fn get_bit(self, bits: &Self::RegisterBits) -> bool;
    fn set_bit(self, bits: &mut Self::RegisterBits, bit: bool);
    fn allocate_reg(free_bits: Self::RegisterBits, class: RegClass) -> Option<Self>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UnknownRegister(u32);
impl Register for UnknownRegister {
    const DEFAULT: Self = Self(0);

    type RegisterBits = u8;
    const NO_BITS: Self::RegisterBits = 0;
    const ALL_BITS: Self::RegisterBits = 0;

    fn to_str(self) -> &'static str {
        "unknown"
    }

    fn encode(self) -> u32 {
        self.0
    }

    fn decode(value: u32) -> Self {
        Self(value)
    }

    fn get_bit(self, _bits: &Self::RegisterBits) -> bool {
        false
    }

    fn set_bit(self, _bits: &mut Self::RegisterBits, _bit: bool) {}

    fn allocate_reg(_free_bits: Self::RegisterBits, _class: RegClass) -> Option<Self> {
        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpType {
    Non,
    Reg,
    Mem,
    Imm,
    Blk,
    Fun,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpUsage {
    Def = 0b01,
    Use = 0b10,
    DefUse = 0b11,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegClass {
    GP8,
    GP16,
    GP32,
    GP64,
    F32,
    F64,
    Flags,
}

pub struct StackSlot {
    pub offset: u32,
    pub size: u32,
}

pub fn parallel_copy(
    mc: ModuleOf<Mc>,
    args: &[MCReg],
    unit: crate::TypeId,
) -> (FunctionId, impl crate::IntoArgs<'_>, crate::TypeId) {
    let f = crate::FunctionId {
        module: mc.id(),
        function: Mc::Copy.id(),
    };
    (f, ((), args), unit)
}

pub fn parallel_copy_args(
    mc: ModuleOf<Mc>,
    args: &[MCReg],
    unit: crate::TypeId,
) -> (FunctionId, impl crate::IntoArgs<'_>, crate::TypeId) {
    let f = crate::FunctionId {
        module: mc.id(),
        function: Mc::AssignBlockArgs.id(),
    };
    (f, ((), args), unit)
}

#[macro_export]
macro_rules! ident_count {
    () => {
        0
    };
    ($i: ident $($rest: ident)*) => {
        1 + $crate::mc::ident_count!($($rest)*)
    };
}
pub use crate::ident_count;

#[macro_export]
macro_rules! first_reg {
    () => {
        compile_error!("Register list can't be empty");
    };
    ($id: ident $($rest: ident)*) => {
        Self::$id
    };
}
pub use crate::first_reg;

#[macro_export]
macro_rules! registers {
    ($name: ident $bits: ident $($size: ident => $($variant: ident)*;)*) => {
        #[rustfmt::skip]
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        #[repr(u8)]
        pub enum $name {
            $($($variant,)*)*
        }

        impl $name {
            pub fn class(self) -> $crate::mc::RegClass {
                match self {
                    $($(Self::$variant => $crate::mc::RegClass::$size,)*)*
                }
            }
        }
        impl $crate::mc::Register for $name {
            const DEFAULT: Self = $crate::mc::first_reg!($($($variant)*)*);
            const NO_BITS: $bits = $bits::new();
            const ALL_BITS: $bits = $bits::all();
            type RegisterBits = $bits;

            fn to_str(self) -> &'static str {
                match self {
                    $($(Self::$variant => stringify!($variant),)*)*
                }
            }

            fn encode(self) -> u32 {
                self as u32
            }

            fn decode(value: u32) -> Self {
                let count = $crate::mc::ident_count!($($($variant)*)*);
                assert!(value < count, "can't decode invalid physical register {}", value);
                unsafe { std::mem::transmute(value as u8) }
            }

            fn get_bit(self, bits: &$bits) -> bool {
                bits.get(self)
            }

            fn set_bit(self, bits: &mut $bits, set: bool) {
                bits.set(self, set);
            }

            fn allocate_reg(free: Self::RegisterBits, class: $crate::mc::RegClass) -> Option<Self> {
                $(
                    if class == $crate::mc::RegClass::$size {
                        $(if Self::$variant.get_bit(&free) {
                            return Some(Self::$variant)
                        })*
                    }
                )*
                None
            }
        }


        impl ::core::convert::TryFrom<$crate::Argument<'_>> for $name {
            type Error = $crate::ArgError;
            fn try_from(value: $crate::Argument<'_>) -> Result<Self, Self::Error> {
                let $crate::Argument::MCReg(value) = value else {
                    return Err($crate::ArgError {
                        expected: $crate::Parameter::MCReg($crate::Usage::Def),
                        found: value.parameter_ty(),
                    });
                };
                Ok(value
                    .phys()
                    .expect("expected physical register, found virtual"))
            }
        }

    };
}
use crate::FunctionId;
use crate::MCReg;
use crate::ModuleOf;
pub use crate::registers;
