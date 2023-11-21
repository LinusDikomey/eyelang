use crate::Primitive;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum IntType {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
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
            IntType::U128 => u128::MAX,
        }
    }
    pub fn min(self) -> u128 {
        match self {
            IntType::U8 | IntType::U16 | IntType::U32 | IntType::U64 | IntType::U128 => 0,
            IntType::I8 => 2u128.pow(7),
            IntType::I16 => 2u128.pow(15),
            IntType::I32 => 2u128.pow(31),
            IntType::I64 => 2u128.pow(63),
            IntType::I128 => 2u128.pow(127),
        }
    }
}
