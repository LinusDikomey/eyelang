use crate::types::{FloatType, IntType, Type};


#[derive(Debug)]
pub struct SourcePos {
    pub line: u64,
    pub col: u64
}

impl SourcePos {
    pub fn new(line: u64, col: u64) -> Self {
        Self { line, col }
    }
}

#[derive(Debug)]
pub struct Token {
    pub ty: TokenType,
    pub start: SourcePos,
    pub end: SourcePos
}

impl Token {
    pub fn new(ty: TokenType, start: SourcePos, end: SourcePos) -> Self {
        Self { ty, start, end }
    }
}

#[derive(Debug)]
pub enum TokenType {
    Semicolon,
    Colon,
    DoubleColon,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    StringLiteral(String),
    IntLiteral(IntLiteral),
    FloatLiteral(FloatLiteral),
    
    Keyword(Keyword),
    Ident(String),
}

#[derive(Debug)]
pub struct IntLiteral {
    pub val: String,
    pub ty: Option<IntType>
}

#[derive(Debug)]
pub struct FloatLiteral {
    pub val: String,
    pub ty: Option<FloatType>
}

#[derive(Debug)]
pub enum Keyword {
    Type(Type)
}

impl Keyword {

    pub fn from_string(s: &str) -> Option<Keyword> {
        match s {
            "i8"   => Some(Keyword::Type(Type::Integer(IntType::I8))),
            "i16"  => Some(Keyword::Type(Type::Integer(IntType::I16))),
            "i32"  => Some(Keyword::Type(Type::Integer(IntType::I32))),
            "i64"  => Some(Keyword::Type(Type::Integer(IntType::I64))),
            "i128" => Some(Keyword::Type(Type::Integer(IntType::I128))),
            
            "u8"   => Some(Keyword::Type(Type::Integer(IntType::U8))),
            "u16"  => Some(Keyword::Type(Type::Integer(IntType::U16))),
            "u32"  => Some(Keyword::Type(Type::Integer(IntType::U32))),
            "u64"  => Some(Keyword::Type(Type::Integer(IntType::U64))),
            "u128" => Some(Keyword::Type(Type::Integer(IntType::U128))),
            
            "f32" => Some(Keyword::Type(Type::Float(FloatType::F32))),
            "f64" => Some(Keyword::Type(Type::Float(FloatType::F64))),
            
            _ => None
        }
    }

}