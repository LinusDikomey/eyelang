use std::fmt;

use crate::ast::{Repr, Representer};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Primitive {
    Integer(IntType),
    Float(FloatType),
    String,
    Bool,
    Unit
}
impl Primitive {
    pub fn _size(&self) -> u32 {
        use Primitive::*;
        match self {
            Integer(i) => i.size(),
            Float(f) => f.size(),
            Primitive::String => todo!(),
            Primitive::Bool => 1,
            Primitive::Unit => 0            
        }
    }
}
impl fmt::Display for Primitive {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Primitive::Integer(int) => int.display(),
            Primitive::Float(float) => float.display(),
            Primitive::String => "string",
            Primitive::Bool => "bool",
            Primitive::Unit => "()"
        };
        write!(f, "{}", s)
    }
}
impl<C: Representer> Repr<C> for Primitive {
    fn repr(&self, c: &C) {
        match self { 
            Primitive::Integer(int) => int.repr(c),
            Primitive::Float(float) => float.repr(c),
            Primitive::String => c.write_add("string"),
            Primitive::Bool => c.write_add("bool"),
            Primitive::Unit => c.write_add("()"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum IntType {
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
}
impl<C: Representer> Repr<C> for IntType {
    fn repr(&self, c: &C) {
        use IntType::*;
        c.write_add(match self {
            I8 => "i8",
            I16 => "i16",
            I32 => "i32",
            I64 => "i64",
            I128 => "i128",
            U8 => "u8",
            U16 => "u16",
            U32 => "u32",
            U64 => "u64",
            U128 => "u128",
        });
    }
}

impl IntType {
    pub fn display(&self) -> &str {
        use IntType::*;
        match self {
            I8 => "i8",
            U8 => "u8",
            I16 => "i16",
            U16 => "u16",
            I32 => "i32",
            U32 => "u32",
            I64 => "i64",
            U64 => "u64",
            I128 => "i128",
            U128 => "u128",
        }
    }
    pub fn size(&self) -> u32 {
        use IntType::*;
        match self {
            I8 | U8 => 1,
            I16 | U16 => 2,
            I32 | U32 => 4,
            I64 | U64 => 8,
            I128 | U128 => 16
        }
    }

    pub fn is_signed(&self) -> bool {
        match self {
            IntType::I8 | IntType::I16 | IntType::I32 | IntType::I64 | IntType::I128 => true,
            IntType::U8 | IntType::U16 | IntType::U32 | IntType::U64 | IntType::U128 => false,
        }
    }

    pub fn bit_count(&self) -> u8 {
        self.size() as u8 * 8
    }

    /// returns the smallest possible value
    pub fn min_val(&self) -> u128 {
        if self.is_signed() {
            2_u128.pow(self.bit_count() as u32 - 1)
        } else {
            0
        }
    }

    /// returns the largest possible value
    pub fn max_val(&self) -> u128 {
        if self.is_signed() {
            2_u128.pow(self.bit_count() as u32 - 1) - 1
        } else {
            2_u128.pow(self.bit_count() as u32) - 1
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum FloatType {
    F32, F64,
}
impl FloatType {
    pub fn display(&self) -> &str {
        use FloatType::*;
        match self {
            F32 => "f32",
            F64 => "f64"
        }
    }
    pub fn size(&self) -> u32 {
        use FloatType::*;
        match self {
            F32 => 4,
            F64 => 8
        }
    }
}

impl<C: Representer> Repr<C> for FloatType {
    fn repr(&self, c: &C) {
        c.write_add(match self {
            Self::F32 => "f32",
            Self::F64 => "f64"
        });
    }
}