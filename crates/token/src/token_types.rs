use std::fmt;

use color_format::cwrite;

use crate::Keyword;

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
