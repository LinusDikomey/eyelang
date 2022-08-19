use std::{u128, fmt, str::FromStr};

use color_format::cwrite;

use crate::{types::{Primitive, IntType, FloatType}, parser::TokenTypes, span::TSpan};

#[derive(Debug, Clone, Copy)]
pub struct  Token {
    pub start: u32,
    pub end: u32,
    pub ty: TokenType,
    /// is this token on a different line than the previous one
    pub new_line: bool,
}

impl Token {
    pub fn new(ty: TokenType, start: u32, end: u32, new_line: bool) -> Self {
        Self { start, end, ty, new_line }
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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
impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (s, is_text) = self.text_repr();
        if is_text {
            cwrite!(f, "#i;c<{}>", s)
        } else {
            cwrite!(f, "#c<{}>", s)
        }
    }
}
impl TokenType {
    /// returns a raw text representation of the token type and wether it is a text
    fn text_repr(&self) -> (&'static str, bool) {
        let mut is_text = false;
        let s = match self {
            TokenType::Colon => ":",
            TokenType::DoubleColon => "::",
            TokenType::Comma => ",",
            TokenType::Semicolon => ";",
            TokenType::Dot => ".",
            TokenType::TripleDot => "...",
            TokenType::LParen => "(",
            TokenType::RParen => ")",
            TokenType::LBrace => "{",
            TokenType::RBrace => "}",
            TokenType::LBracket => "[",
            TokenType::RBracket => "]",
            TokenType::Bang => "!",
            TokenType::Plus => "+",
            TokenType::Minus => "-",
            TokenType::Star => "*",
            TokenType::Slash => "/",
            TokenType::Percent => "%",
            TokenType::Ampersand => "&",
            TokenType::SnackWave => "~",
            TokenType::Caret => "^",
            TokenType::Underscore => "_",
            TokenType::Equals => "=",
            TokenType::DoubleEquals => "==",
            TokenType::BangEquals => "!=",
            TokenType::PlusEquals => "+=",
            TokenType::MinusEquals => "-=",
            TokenType::StarEquals => "*=",
            TokenType::SlashEquals => "/=",
            TokenType::PercentEquals => "%=",
            TokenType::LessThan => "<",
            TokenType::GreaterThan => ">",
            TokenType::LessEquals => "<=",
            TokenType::GreaterEquals => ">=",
            TokenType::Declare => ":=",
            TokenType::Arrow => "->",
            TokenType::StringLiteral => "string literal",
            TokenType::IntLiteral => "int literal",
            TokenType::FloatLiteral => "float literal",
            &TokenType::Keyword(kw) => { is_text = true; kw.into() },
            TokenType::Ident => "identifier",
        };
        (s, is_text)
    }
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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
    Enum,
    Trait,
    If,
    Else,
    Match,
    While,
    Extern,
    Root,
    Use,
    Asm,
}
impl Into<&'static str> for Keyword {
    fn into(self) -> &'static str {
        match self {
            Keyword::Primitive(p) => p.into(),
            Keyword::Fn => "fn",
            Keyword::Ret => "ret",
            Keyword::True => "true",
            Keyword::False => "false",
            Keyword::And => "and",
            Keyword::Or => "or",
            Keyword::As => "as",
            Keyword::Struct => "struct",
            Keyword::Enum => "enum",
            Keyword::Trait => "trait",
            Keyword::If => "if",
            Keyword::Else => "else",
            Keyword::Match => "match",
            Keyword::While => "while",
            Keyword::Extern => "extern",
            Keyword::Root => "root",
            Keyword::Use => "use",
            Keyword::Asm => "asm",
        }
    }
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
            
            "type" => P(Type),
            
            "fn" => Keyword::Fn,
            "ret" => Keyword::Ret,
            "true" => Keyword::True,
            "false" => Keyword::False,
            "and" => Keyword::And,
            "or" => Keyword::Or,
            "as" => Keyword::As,
            "struct" => Keyword::Struct,
            "enum" => Keyword::Enum,
            "trait" => Keyword::Trait,
            "if" => Keyword::If,
            "else" => Keyword::Else,
            "match" => Keyword::Match,
            "while" => Keyword::While,

            "extern" => Keyword::Extern,
            "root" => Keyword::Root,
            "use" => Keyword::Use,

            "asm" => Keyword::Asm,
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
    pub fn is_boolean(self) -> bool {
        matches!(
            self,
            Operator::Or | Operator::And
        )
    }
    pub fn is_logical(self) -> bool {
        matches!(
            self,
            Operator::Equals |Operator::NotEquals 
            | Operator::LT | Operator::GT | Operator::LE | Operator::GE
        )
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