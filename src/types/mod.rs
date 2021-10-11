
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Primitive {
    Integer(IntType),
    Float(FloatType),
    String,
    Bool,
    Void
}
impl Primitive {
    pub fn display(&self) -> &str {
        use Primitive::*;
        match self {
            Integer(i) => i.display(),
            Float(f) => f.display(),
            String => "string",
            Bool => "bool",
            Void => "void"
        }
    }
    pub fn size(&self) -> u32 {
        use Primitive::*;
        match self {
            Integer(i) => i.size(),
            Float(f) => f.size(),
            Primitive::String => todo!(),
            Primitive::Bool => 1,
            Primitive::Void => 0            
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum IntType {
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
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

#[derive(Debug, PartialEq, Clone, Copy)]
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