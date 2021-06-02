
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Primitive {
    Integer(IntType),
    Float(FloatType),
    String,
    Bool,
    Void
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum IntType {
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
}

impl IntType {
    pub fn is_signed(&self) -> bool {
        match self {
            IntType::I8 | IntType::I16 | IntType::I32 | IntType::I64 | IntType::I128 => true,
            IntType::U8 | IntType::U16 | IntType::U32 | IntType::U64 | IntType::U128 => false,
        }
    }

    pub fn bit_count(&self) -> u8 {
        use IntType::*;
        match self {
            I8 | U8 => 8,
            I16 | U16 => 16,
            I32 | U32 => 32,
            I64 | U64 => 64,
            I128 | U128 => 128,
        }
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

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum FloatType {
    F32, F64,
}