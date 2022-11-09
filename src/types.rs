use std::fmt;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Primitive {
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
    F32, F64,
    Bool,
    Unit,
    Never,
    Type,
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
    pub fn is_int(self) -> bool {
        self.as_int().is_some()
    }

    pub fn as_float(self) -> Option<FloatType> {
        use Primitive::*;
        Some(match self {
            F32 => FloatType::F32,
            F64 => FloatType::F64,
            _ => return None
        })
    }
    pub fn is_float(self) -> bool {
        self.as_float().is_some()
    }

    pub fn layout(self) -> Layout {
        use Primitive::*;
        let size_and_align = match self {
            Unit | Never | Type => 0,
            I8 | U8 | Bool => 1,
            I16 | U16 => 2,
            I32 | U32 | F32 => 4,
            I64 | U64 | F64 => 8,
            I128 | U128 => 16,
        };
        Layout { size: size_and_align, alignment: size_and_align.max(1) }
    }
}
impl From<Primitive> for &'static str {
    fn from(p: Primitive) -> Self {
        use Primitive::*;
        match p {
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
            Never => "!",
            Type => "type",
        }
    }
}
impl fmt::Display for Primitive {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Into::<&'static str>::into(*self))
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

    pub fn max(self) -> u128 {
        match self {
            IntType::I8 => i8::MAX as u128,
            IntType::I16 => i16::MAX as u128,
            IntType::I32 => i32::MAX as u128,
            IntType::I64 => i64::MAX as u128,
            IntType::I128 => i128::MAX as u128,
            IntType::U8 => u8::MAX as u128,
            IntType::U16 => u16::MAX as u128,
            IntType::U32 => u32::MAX as u128,
            IntType::U64 => u64::MAX as u128,
            IntType::U128 => u128::MAX as u128,
        }
    }
    pub fn min(self) -> u128 {
        match self {
            IntType::U8
            | IntType::U16
            | IntType::U32
            | IntType::U64
            | IntType::U128 => 0,
            IntType::I8 => 2u128.pow(7),
            IntType::I16 => 2u128.pow(15),
            IntType::I32 => 2u128.pow(31),
            IntType::I64 => 2u128.pow(63),
            IntType::I128 => 2u128.pow(127),
        }
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layout {
    pub size: u64,
    pub alignment: u64,
}
impl Layout {
    pub const ZERO: Self = Self { size: 0, alignment: 1 };
    pub const PTR: Self = Self { size: 8, alignment: 8 };

    pub fn align(offset: u64, alignment: u64) -> u64 {
        let misalignment = offset % alignment;
        if misalignment > 0 {
            offset + alignment - misalignment
        } else {
            offset
        }
    }
    #[must_use]
    pub fn accumulate(self, other: Self) -> Self {
        Self {
            size: Self::align(self.size, other.alignment),
            alignment: self.alignment.max(other.alignment),
        }
    }
    #[must_use]
    pub fn mul_size(self, factor: u64) -> Self {
        Self {
            size: self.size * factor,
            alignment: self.alignment,
        }
    }
}