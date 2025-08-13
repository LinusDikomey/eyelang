use color_format::cwrite;
use span::TSpan;
use std::fmt;
use types::{FloatType, IntType, Primitive};

#[derive(Debug, Clone, Copy)]
pub struct Token {
    pub start: u32,
    pub end: u32,
    pub ty: TokenType,
    /// is this token on a different line than the previous one
    pub new_line: bool,
}

impl Token {
    pub fn new(ty: TokenType, start: u32, end: u32, new_line: bool) -> Self {
        Self {
            start,
            end,
            ty,
            new_line,
        }
    }

    pub fn get_val<'a>(&self, src: &'a str) -> &'a str {
        &src[self.start as usize..self.end as usize]
    }

    pub fn span(&self) -> TSpan {
        TSpan::new(self.start, self.end)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TokenType {
    Eof,

    Colon,
    DoubleColon,
    Comma,
    Semicolon,
    Dot,
    DotDot,
    DotDotLessThan,
    TripleDot,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    Bang,
    At,

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
        let (s, is_keyword) = self.text_repr();
        if is_keyword {
            cwrite!(f, "keyword #i;m<{}>", s)
        } else {
            cwrite!(f, "#c<{}>", s)
        }
    }
}
impl TokenType {
    /// returns a raw text representation of the token type and wether it is a text
    fn text_repr(self) -> (&'static str, bool) {
        let mut is_keyword = false;
        let s = match self {
            TokenType::Colon => ":",
            TokenType::DoubleColon => "::",
            TokenType::Comma => ",",
            TokenType::Semicolon => ";",
            TokenType::Dot => ".",
            TokenType::DotDot => "..",
            TokenType::DotDotLessThan => "..<",
            TokenType::TripleDot => "...",
            TokenType::LParen => "(",
            TokenType::RParen => ")",
            TokenType::LBrace => "{",
            TokenType::RBrace => "}",
            TokenType::LBracket => "[",
            TokenType::RBracket => "]",
            TokenType::Bang => "!",
            TokenType::At => "@",
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
            TokenType::Keyword(kw) => {
                is_keyword = true;
                kw.into()
            }
            TokenType::Ident => "identifier",
            TokenType::Eof => "<end of file>",
        };
        (s, is_keyword)
    }
}

#[derive(Debug, Clone)]
pub enum ExpectedTokens {
    Specific(TokenType),
    AnyOf(Box<[TokenType]>),
    Expr,
    Type,
    Item,
    EndOfMultilineComment,
    EndOfStringLiteral,
}
impl std::fmt::Display for ExpectedTokens {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            &Self::Specific(tok) => {
                write!(f, "{tok}")
            }
            Self::AnyOf(toks) => {
                for (i, tok) in toks.iter().enumerate() {
                    match i {
                        0 => {}
                        i if i != 0 || i == toks.len() - 1 => {
                            write!(f, " or ")?;
                        }
                        _ => write!(f, ", ")?,
                    }
                    write!(f, "{tok}")?;
                }
                Ok(())
            }
            Self::Expr => write!(f, "an expression"),
            Self::Type => write!(f, "a type"),
            Self::Item => write!(f, "an item"),
            Self::EndOfMultilineComment => write!(f, "end of comment"),
            Self::EndOfStringLiteral => write!(f, "end of string literal"),
        }
    }
}

#[derive(Clone, Copy)]
pub struct TokenTypes<const N: usize>(pub [TokenType; N]);
impl From<TokenType> for TokenTypes<1> {
    fn from(x: TokenType) -> Self {
        Self([x])
    }
}
impl<const N: usize> From<[TokenType; N]> for TokenTypes<N> {
    fn from(x: [TokenType; N]) -> Self {
        Self(x)
    }
}

impl<const N: usize> From<TokenTypes<N>> for ExpectedTokens {
    fn from(t: TokenTypes<N>) -> Self {
        match t.0.as_slice() {
            [t] => Self::Specific(*t),
            other => Self::AnyOf(other.into()),
        }
    }
}
impl From<TokenType> for ExpectedTokens {
    fn from(value: TokenType) -> Self {
        Self::Specific(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct IntLiteral {
    pub val: u128,
    pub ty: Option<IntType>,
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
    pub ty: Option<FloatType>,
}
impl FloatLiteral {
    pub fn parse(s: &str) -> Self {
        Self {
            val: s.parse().unwrap(),
            ty: None,
        }
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
    And,
    Or,
    As,
    Struct,
    Enum,
    Trait,
    Impl,
    If,
    Else,
    Match,
    While,
    For,
    Extern,
    Root,
    Use,
    Asm,
    Break,
    Continue,
    In,
}
impl From<Keyword> for &'static str {
    fn from(k: Keyword) -> Self {
        match k {
            Keyword::Primitive(p) => p.into(),
            Keyword::Fn => "fn",
            Keyword::Ret => "ret",
            Keyword::And => "and",
            Keyword::Or => "or",
            Keyword::As => "as",
            Keyword::Struct => "struct",
            Keyword::Enum => "enum",
            Keyword::Trait => "trait",
            Keyword::Impl => "impl",
            Keyword::If => "if",
            Keyword::Else => "else",
            Keyword::Match => "match",
            Keyword::While => "while",
            Keyword::For => "for",
            Keyword::Extern => "extern",
            Keyword::Root => "root",
            Keyword::Use => "use",
            Keyword::Asm => "asm",
            Keyword::Break => "break",
            Keyword::Continue => "continue",
            Keyword::In => "in",
        }
    }
}
impl Keyword {
    pub fn parse(s: &str) -> Option<Keyword> {
        use Keyword::Primitive as P;
        use Primitive::*;
        Some(match s {
            "i8" => P(I8),
            "i16" => P(I16),
            "i32" => P(I32),
            "i64" => P(I64),
            "i128" => P(I128),

            "u8" => P(U8),
            "u16" => P(U16),
            "u32" => P(U32),
            "u64" => P(U64),
            "u128" => P(U128),

            "f32" => P(F32),
            "f64" => P(F64),

            "type" => P(Type),

            "fn" => Keyword::Fn,
            "ret" => Keyword::Ret,
            "and" => Keyword::And,
            "or" => Keyword::Or,
            "as" => Keyword::As,
            "struct" => Keyword::Struct,
            "enum" => Keyword::Enum,

            "trait" => Keyword::Trait,
            "impl" => Keyword::Impl,

            "if" => Keyword::If,
            "else" => Keyword::Else,
            "match" => Keyword::Match,
            "while" => Keyword::While,
            "for" => Keyword::For,

            "extern" => Keyword::Extern,
            "root" => Keyword::Root,
            "use" => Keyword::Use,

            "asm" => Keyword::Asm,

            "break" => Keyword::Break,
            "continue" => Keyword::Continue,
            "in" => Keyword::In,
            _ => return None,
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

    Range,
    RangeExclusive,
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

            //TokenType::Equals => Assignment(AssignType::Assign),
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

            TokenType::DotDot => Range,
            TokenType::DotDotLessThan => RangeExclusive,

            _ => return None,
        })
    }
}
impl Operator {
    pub fn precedence(self) -> u8 {
        use Operator::*;
        match self {
            Assignment(_) => 10,
            Range | RangeExclusive => 20,
            Or => 30,
            And => 40,
            Equals | NotEquals => 50,
            LT | LE | GT | GE => 60,
            Add | Sub => 70,
            Mul | Div | Mod => 80,
        }
    }
    pub fn is_boolean(self) -> bool {
        matches!(self, Operator::Or | Operator::And)
    }
    pub fn is_logical(self) -> bool {
        matches!(
            self,
            Operator::Equals
                | Operator::NotEquals
                | Operator::LT
                | Operator::GT
                | Operator::LE
                | Operator::GE
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
    ModAssign,
}
