use std::{u128, fmt};

use crate::{types::{Primitive, IntType, FloatType}, parser::TokenTypes};

#[derive(Debug)]
pub struct Token {
    pub start: u32,
    pub end: u32,
    pub ty: TokenType,
}

impl Token {
    pub fn new(ty: TokenType, start: u32, end: u32) -> Self {
        Self { ty, start, end }
    }

    pub fn get_val<'a>(&self, src: &'a str) -> &'a str {
        &src[self.start as usize ..= self.end as usize]
    }

    pub fn is<const N: usize>(&self, types: impl Into<TokenTypes<N>>) -> bool {
        types.into().0.contains(&self.ty)
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum TokenType {
    Colon,
    DoubleColon,
    Comma,
    Dot,
    TripleDot,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    Operator(Operator),
    Assign,
    Declare,

    Arrow,

    StringLiteral,
    IntLiteral,
    FloatLiteral,
    
    Keyword(Keyword),
    Ident,
}

#[derive(Debug, Clone)]
pub struct IntLiteral {
    pub val: u128,
    pub ty: Option<IntType>
}
impl IntLiteral {
    pub fn from_tok(token: &Token, src: &str) -> Self {
        let val = &token.get_val(src);
        let val = val.parse::<u128>().unwrap();

        Self { val, ty: None }
    }

    /*pub fn _fits_into_type(&self, ty: &IntType) -> bool {
        self.unsigned_val <= if self.sign {ty.min_val()} else {ty.max_val()}
    }*/
}
impl fmt::Display for IntLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.val)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FloatLiteral {
    pub val: f64,
    pub ty: Option<FloatType>
}
impl FloatLiteral {
    pub fn from_tok(token: &Token, src: &str) -> Self {
        Self { val: token.get_val(src).parse::<f64>().unwrap(), ty: None }
    }

    pub fn _fits_into_type(&self, ty: &FloatType) -> bool {
        match ty {
            FloatType::F32 => true, //TODO: boundary checks
            FloatType::F64 => true,
        }
    }
}
impl fmt::Display for FloatLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.val)
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Keyword {
    Primitive(Primitive),
    Ret,
    True,
    False,
    Struct,
    If,
    Else,
    While,
    Extern,
    Root
}

impl Keyword {

    pub fn from_str(s: &str) -> Option<Keyword> {
        Some(match s {
            "i8"   => Keyword::Primitive(Primitive::I8),
            "i16"  => Keyword::Primitive(Primitive::I16),
            "i32"  => Keyword::Primitive(Primitive::I32),
            "i64"  => Keyword::Primitive(Primitive::I64),
            "i128" => Keyword::Primitive(Primitive::I128),
            
            "u8"   => Keyword::Primitive(Primitive::U8),
            "u16"  => Keyword::Primitive(Primitive::U16),
            "u32"  => Keyword::Primitive(Primitive::U32),
            "u64"  => Keyword::Primitive(Primitive::U64),
            "u128" => Keyword::Primitive(Primitive::U128),
            
            "f32" => Keyword::Primitive(Primitive::F32),
            "f64" => Keyword::Primitive(Primitive::F64),
            
            "bool" => Keyword::Primitive(Primitive::Bool),
            "string" => Keyword::Primitive(Primitive::String),

            "ret" => Keyword::Ret,
            "true" => Keyword::True,
            "false" => Keyword::False,
            "struct" => Keyword::Struct,
            "if" => Keyword::If,
            "else" => Keyword::Else,
            "while" => Keyword::While,

            "extern" => Keyword::Extern,
            "root" => Keyword::Root,
            _ => return None
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Operator {
    Add,
    Sub,
    Mul,
    Div,

    Equals,     // ==
    LT,
    GT,
    LE,
    GE
}
impl Operator {
    pub fn precedence(&self) -> u8 {
        use Operator::*;
        match self {
            Equals => 20,
            LT | LE | GT | GE => 30,
            Add | Sub => 50,
            Mul | Div => 60,
        }
    }
}