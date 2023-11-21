use crate::Primitive;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum FloatType {
    F32,
    F64,
}
impl From<FloatType> for Primitive {
    fn from(f: FloatType) -> Self {
        match f {
            FloatType::F32 => Self::F32,
            FloatType::F64 => Self::F64,
        }
    }
}
impl FloatType {
    pub fn size(self) -> u32 {
        use FloatType::*;
        match self {
            F32 => 4,
            F64 => 8,
        }
    }

    pub fn bit_count(self) -> u32 {
        self.size() * 8
    }
}
