use std::{u128, fmt, str::FromStr};

use crate::{types::{Primitive, IntType, FloatType}, parser::TokenTypes, ast::TSpan};

#[derive(Debug, Clone, Copy)]
pub struct Token {
    pub start: u32,
    pub end: u32,
    pub ty: TokenType,
}

impl Token {
    pub fn new(ty: TokenType, start: u32, end: u32) -> Self {
        Self { start, end, ty }
    }

    pub fn get_val<'a>(&self, src: &'a str) -> &'a str {
        &src[self.start as usize ..= self.end as usize]
    }

    pub fn span(&self) -> TSpan {
        TSpan::new(self.start, self.end)
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
    Semicolon,
    Dot,
    TripleDot,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    Bang,
    
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    
    Ampersand,
    SnackWave,
    Caret,
    
    Underscore,
    
    Equals,
    DoubleEquals,
    BangEquals,

    PlusEquals,
    MinusEquals,
    StarEquals,
    SlashEquals,
    PercentEquals,

    LessThan,
    GreaterThan,
    LessEquals,
    GreaterEquals,

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
    pub fn parse(s: &str) -> Self {
        let val = s.parse::<u128>().unwrap();
        Self { val, ty: None }
    }
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
    pub fn parse(s: &str) -> Self {
        Self { val: s.parse().unwrap(), ty: None }
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
    Fn,
    Ret,
    True,
    False,
    And,
    Or,
    As,
    Struct,
    If,
    Else,
    While,
    Extern,
    Root,
    Use,
}
impl FromStr for Keyword {
    type Err = ();

    fn from_str(s: &str) -> Result<Keyword, ()> {
        use Keyword::Primitive as P;
        use Primitive::*;
        Ok(match s {
            "i8"   => P(I8),
            "i16"  => P(I16),
            "i32"  => P(I32),
            "i64"  => P(I64),
            "i128" => P(I128),
            
            "u8"   => P(U8),
            "u16"  => P(U16),
            "u32"  => P(U32),
            "u64"  => P(U64),
            "u128" => P(U128),
            
            "f32" => P(F32),
            "f64" => P(F64),
            
            "bool" => P(Bool),
            
            "fn" => Keyword::Fn,
            "ret" => Keyword::Ret,
            "true" => Keyword::True,
            "false" => Keyword::False,
            "and" => Keyword::And,
            "or" => Keyword::Or,
            "as" => Keyword::As,
            "struct" => Keyword::Struct,
            "if" => Keyword::If,
            "else" => Keyword::Else,
            "while" => Keyword::While,

            "extern" => Keyword::Extern,
            "root" => Keyword::Root,
            "use" => Keyword::Use,
            _ => return Err(())
        })
    }
}
impl From<Keyword> for TokenType {
    fn from(k: Keyword) -> Self {
        TokenType::Keyword(k)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operator {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    
    Assignment(AssignType),

    Or,
    And,
    
    Equals,
    NotEquals,

    LT,
    GT,
    LE,
    GE,
}
impl From<TokenType> for Option<Operator> {
    fn from(tok: TokenType) -> Self {
        use Operator::*;
        Some(match tok {
            TokenType::Plus => Add,
            TokenType::Minus => Sub,
            TokenType::Star => Mul,
            TokenType::Slash => Div,
            TokenType::Percent => Mod,

            TokenType::Equals => Assignment(AssignType::Assign),
            TokenType::PlusEquals => Assignment(AssignType::AddAssign),
            TokenType::MinusEquals => Assignment(AssignType::SubAssign),
            TokenType::StarEquals => Assignment(AssignType::MulAssign),
            TokenType::SlashEquals => Assignment(AssignType::DivAssign),
            TokenType::PercentEquals => Assignment(AssignType::ModAssign),
            
            TokenType::Keyword(Keyword::Or) => Or,
            TokenType::Keyword(Keyword::And) => And,

            TokenType::DoubleEquals => Equals,
            TokenType::BangEquals => NotEquals,

            TokenType::LessThan => LT,
            TokenType::GreaterThan => GT,
            TokenType::LessEquals => LE,
            TokenType::GreaterEquals => GE,

            _ => return None
        })
    }
}
impl Operator {
    pub fn precedence(self) -> u8 {
        use Operator::*;
        match self {
            Assignment(_) => 10,
            Or => 20,
            And => 30,
            Equals | NotEquals => 40,
            LT | LE | GT | GE => 50,
            Add | Sub => 60,
            Mul | Div | Mod => 70,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignType {
    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    ModAssign
}