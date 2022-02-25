use std::{u128, fmt, ops::RangeBounds};

use crate::{error::EyeError, types::{FloatType, IntType, Primitive}, ast::{Repr, Representer}, parser::TokenTypes};


#[derive(Debug, Clone, Copy)]
pub struct SourcePos {
    pub line: u64,
    pub col: u64
}

impl SourcePos {
    pub fn new(line: u64, col: u64) -> Self {
        Self { line, col }
    }

    /// returns the next source pos, can be used for single character errors
    pub fn next(&self) -> Self {
        Self { line: self.line, col: self.col + 1 }
    }
}

#[derive(Debug)]
pub struct Token {
    pub ty: TokenType,
    pub val: String,
    pub start: SourcePos,
    pub end: SourcePos
}

impl Token {
    pub fn new(ty: TokenType, val: String, start: SourcePos, end: SourcePos) -> Self {
        Self { ty, val, start, end }
    }

    pub fn get_val(&self) -> String {
        self.val.clone()
    }

    pub fn is<const N: usize>(&self, types: impl Into<TokenTypes<N>>) -> bool {
        types.into().0.contains(&self.ty)
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum TokenType {
    //Semicolon,
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
    pub fn from_tok(token: &Token) -> Result<Self, EyeError> {
        let val = &token.val;
        let (unsigned_val, sign) = if val.starts_with("-") {
            (val[1..].parse::<u128>().unwrap(), true)
        } else {
            (val.parse::<u128>().unwrap(), false)
        };
        Ok(Self { unsigned_val, sign, ty: None })
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
    pub fn from_tok(token: &Token) -> Result<Self, EyeError> {
        Ok(Self { val: token.get_val().parse::<f64>().unwrap(), ty: None })
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
}

impl Keyword {

    pub fn from_string(s: &str) -> Option<Keyword> {
        match s {
            "i8"   => Some(Keyword::Primitive(Primitive::Integer(IntType::I8))),
            "i16"  => Some(Keyword::Primitive(Primitive::Integer(IntType::I16))),
            "i32"  => Some(Keyword::Primitive(Primitive::Integer(IntType::I32))),
            "i64"  => Some(Keyword::Primitive(Primitive::Integer(IntType::I64))),
            "i128" => Some(Keyword::Primitive(Primitive::Integer(IntType::I128))),
            
            "u8"   => Some(Keyword::Primitive(Primitive::Integer(IntType::U8))),
            "u16"  => Some(Keyword::Primitive(Primitive::Integer(IntType::U16))),
            "u32"  => Some(Keyword::Primitive(Primitive::Integer(IntType::U32))),
            "u64"  => Some(Keyword::Primitive(Primitive::Integer(IntType::U64))),
            "u128" => Some(Keyword::Primitive(Primitive::Integer(IntType::U128))),
            
            "f32" => Some(Keyword::Primitive(Primitive::Float(FloatType::F32))),
            "f64" => Some(Keyword::Primitive(Primitive::Float(FloatType::F64))),
            
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
impl<C: Representer> Repr<C> for Operator {
    fn repr(&self, c: &C) {
        c.write_add(match self {
            Operator::Equals => "==",
            Operator::Add => "+",
            Operator::Sub => "-",
            Operator::Mul => "*",
            Operator::Div => "/",
            Operator::LT => "<",
            Operator::GT => ">",
            Operator::LE => "<=",
            Operator::GE => ">=",
        })
    }
}