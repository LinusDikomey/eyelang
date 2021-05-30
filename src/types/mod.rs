
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

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum FloatType {
    F32, F64,
}