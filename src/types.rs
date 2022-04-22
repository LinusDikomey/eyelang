use std::fmt;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Primitive {
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
    F32, F64,
    Bool,
    Unit,
    Never
}
impl Primitive {
    pub fn as_int(self) -> Option<IntType> {
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

    pub fn as_float(self) -> Option<FloatType> {
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
            Bool => "bool",
            Unit => "()",
            Never => "!"
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum IntType {
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
}
impl From<IntType> for Primitive {
    fn from(i: IntType) -> Self {
        match i {
            IntType::I8 => Self::I8,
            IntType::I16 => Self::I16,
            IntType::I32 => Self::I32,
            IntType::I64 => Self::I64,
            IntType::I128 => Self::I128,
            IntType::U8 => Self::U8,
            IntType::U16 => Self::U16,
            IntType::U32 => Self::U32,
            IntType::U64 => Self::U64,
            IntType::U128 => Self::U128,
        }
    }
}

impl IntType {
    pub fn size(self) -> u32 {
        use IntType::*;
        match self {
            I8 | U8 => 1,
            I16 | U16 => 2,
            I32 | U32 => 4,
            I64 | U64 => 8,
            I128 | U128 => 16,
        }
    }

    pub fn is_signed(self) -> bool {
        match self {
            IntType::I8 | IntType::I16 | IntType::I32 | IntType::I64 | IntType::I128 => true,
            IntType::U8 | IntType::U16 | IntType::U32 | IntType::U64 | IntType::U128 => false,
        }
    }

    pub fn bit_count(self) -> u32 {
        self.size() * 8
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum FloatType {
    F32, F64,
}
impl From<FloatType> for Primitive {
    fn from(f: FloatType) -> Self {
        match f {
            FloatType::F32 => Self::F32,
            FloatType::F64 => Self::F64
        }
    }
}
impl FloatType {
    pub fn size(self) -> u32 {
        use FloatType::*;
        match self {
            F32 => 4,
            F64 => 8
        }
    }

    pub fn bit_count(self) -> u32 {
        self.size() * 8
    }
}