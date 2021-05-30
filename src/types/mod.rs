
#[derive(Debug)]
pub enum Type {
    Integer(IntType),
    Float(FloatType),
    String,
}

#[derive(Debug)]
pub enum IntType {
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
}

#[derive(Debug)]
pub enum FloatType {
    F32, F64,
}