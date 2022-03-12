use std::fmt;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Primitive {
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
    F32, F64,
    String,
    Bool,
    Unit,
    Never
}
impl Primitive {
    pub fn _size(&self) -> u32 {
        use Primitive::*;
        match self {
            I8   | U8        => 1,
            I16  | U16       => 2,
            I32  | U32 | F32 => 4,
            I64  | U64 | F64 => 8,
            I128 | U128      => 16,
            String => todo!(),
            Bool => 1,
            Unit | Never => 0,           
        }
    }

    pub fn as_int(&self) -> Option<IntType> {
        use Primitive::*;
        Some(match self {
            I8 => IntType::I8,
            I16 => IntType::I16,
            I32 => IntType::I32,
            I64 => IntType::I64,
            I128 => IntType::I128,
            U8 => IntType::U8,
            U16 => IntType::U16,
            U32 => IntType::U32,
            U64 => IntType::U64,
            U128 => IntType::U128,
            _ => return None
        })
    }

    pub fn as_float(&self) -> Option<FloatType> {
        use Primitive::*;
        Some(match self {
            F32 => FloatType::F32,
            F64 => FloatType::F64,
            _ => return None
        })
    }
}
impl fmt::Display for Primitive {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Primitive::*;
        let s = match self {
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
            F32 => "f32",
            F64 => "f64",
            Primitive::String => "string",
            Primitive::Bool => "bool",
            Primitive::Unit => "()",
            Primitive::Never => "!"
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum IntType {
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
}
impl Into<Primitive> for IntType {
    fn into(self) -> Primitive {
        match self {
            Self::I8 => Primitive::I8,
            Self::I16 => Primitive::I16,
            Self::I32 => Primitive::I32,
            Self::I64 => Primitive::I64,
            Self::I128 => Primitive::I128,
            Self::U8 => Primitive::U8,
            Self::U16 => Primitive::U16,
            Self::U32 => Primitive::U32,
            Self::U64 => Primitive::U64,
            Self::U128 => Primitive::U128,
        }
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
            I128 | U128 => 16,
        }
    }

    pub fn is_signed(&self) -> bool {
        match self {
            IntType::I8 | IntType::I16 | IntType::I32 | IntType::I64 | IntType::I128 => true,
            IntType::U8 | IntType::U16 | IntType::U32 | IntType::U64 | IntType::U128 => false,
        }
    }

    pub fn bit_count(&self) -> u32 {
        self.size() * 8
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
impl Into<Primitive> for FloatType {
    fn into(self) -> Primitive {
        match self {
            Self::F32 => Primitive::F32,
            Self::F64 => Primitive::F64
        }
    }
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

    pub fn bit_count(&self) -> u32 {
        self.size() * 8
    }
}