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
    pub unsigned_val: u128,
    pub sign: bool,
    pub ty: Option<IntType>
}
impl IntLiteral {
    pub fn from_tok(token: &Token, src: &str) -> Self {
        let val = &token.get_val(src);
        let (unsigned_val, sign) = if val.starts_with("-") {
            (val[1..].parse::<u128>().unwrap(), true)
        } else {
            (val.parse::<u128>().unwrap(), false)
        };
        Self { unsigned_val, sign, ty: None }
    }

    pub fn _fits_into_type(&self, ty: &IntType) -> bool {
        self.unsigned_val <= if self.sign {ty.min_val()} else {ty.max_val()}
    }
}
impl fmt::Display for IntLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", if self.sign { "-" } else { "" }, self.unsigned_val)
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
    While
}

impl Keyword {

    pub fn from_str(s: &str) -> Option<Keyword> {
        match s {
            "i8"   => Some(Keyword::Primitive(Primitive::I8)),
            "i16"  => Some(Keyword::Primitive(Primitive::I16)),
            "i32"  => Some(Keyword::Primitive(Primitive::I32)),
            "i64"  => Some(Keyword::Primitive(Primitive::I64)),
            "i128" => Some(Keyword::Primitive(Primitive::I128)),
            
            "u8"   => Some(Keyword::Primitive(Primitive::U8)),
            "u16"  => Some(Keyword::Primitive(Primitive::U16)),
            "u32"  => Some(Keyword::Primitive(Primitive::U32)),
            "u64"  => Some(Keyword::Primitive(Primitive::U64)),
            "u128" => Some(Keyword::Primitive(Primitive::U128)),
            
            "f32" => Some(Keyword::Primitive(Primitive::F32)),
            "f64" => Some(Keyword::Primitive(Primitive::F64)),
            
            "bool" => Some(Keyword::Primitive(Primitive::Bool)),
            "string" => Some(Keyword::Primitive(Primitive::String)),

            "ret" => Some(Keyword::Ret),
            "true" => Some(Keyword::True),
            "false" => Some(Keyword::False),
            "struct" => Some(Keyword::Struct),
            "if" => Some(Keyword::If),
            "else" => Some(Keyword::Else),
            "while" => Some(Keyword::While),
            _ => None
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Operator {
    Equals,     // ==
    Add,
    Sub,
    Mul,
    Div,
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