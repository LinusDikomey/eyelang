#[macro_export]
macro_rules! ident_count {
    () => {
        0
    };
    ($i: ident $($rest: ident)*) => {
        1 + $crate::mc::macros::ident_count!($($rest)*)
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
            const DEFAULT: Self = $crate::mc::macros::first_reg!($($($variant)*)*);
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
                let count = $crate::mc::macros::ident_count!($($($variant)*)*);
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
pub use crate::registers;
