use id::ModuleId;
use span::Span;

use crate::{
    error::{CompileError, Error},
    parser::token::{Token, TokenType},
};

pub struct TokenReader {
    tokens: Vec<Token>,
    index: usize,
    len: usize,
    pub module: ModuleId,
}

impl TokenReader {
    pub fn new(tokens: Vec<Token>, module: ModuleId) -> Self {
        let len = tokens.len();
        Self {
            tokens,
            index: 0,
            len,
            module,
        }
    }
    pub fn current(&self, expected: impl Into<ExpectedTokens>) -> Result<&Token, CompileError> {
        if self.index < self.len {
            Ok(&self.tokens[self.index])
        } else {
            let end = self.last_src_pos();
            Err(CompileError {
                err: Error::UnexpectedEndOfFile {
                    expected: expected.into(),
                },
                span: Span::new(end, end, self.module),
            })
        }
    }
    pub fn previous(&self) -> Option<&Token> {
        (self.index > 0).then(|| &self.tokens[self.index - 1])
    }

    pub fn last_src_pos(&self) -> u32 {
        self.tokens.last().map_or(0, |tok| tok.end)
    }

    pub fn current_end_pos(&self) -> u32 {
        self.tokens
            .get(self.index)
            .or_else(|| self.tokens.last())
            .map_or(0, |tok| tok.end)
    }

    pub fn try_step(&mut self) -> Option<Token> {
        if self.index < self.len {
            let i = self.index;
            self.index += 1;
            Some(self.tokens[i])
        } else {
            None
        }
    }

    /// Steps over the current token and returns it. Token type checks only happen in debug mode.
    /// This should only be used if the type is known.
    pub fn step_assert(&mut self, ty: impl Into<TokenType>) -> Token {
        let tok = *unsafe { self.tokens.get_unchecked(self.index) };
        self.index += 1;
        debug_assert_eq!(tok.ty, ty.into());
        tok
    }

    pub fn step_expect<const N: usize, T: Into<TokenTypes<N>>>(
        &mut self,
        expected: T,
    ) -> Result<Token, CompileError> {
        let expected = expected.into();
        let module = self.module;
        if self
            .tokens
            .get(self.index)
            .is_some_and(|tok| expected.0.contains(&tok.ty))
        {
            let i = self.index;
            self.index += 1;
            Ok(self.tokens[i])
        } else {
            Err(if let Some(tok) = self.tokens.get(self.index) {
                CompileError {
                    err: Error::UnexpectedToken {
                        expected: expected.into(),
                        found: tok.ty,
                    },
                    span: Span::new(tok.start, tok.end, module),
                }
            } else {
                let end = self.last_src_pos();
                Error::UnexpectedEndOfFile {
                    expected: expected.into(),
                }
                .at_span(Span::new(end, end, module))
            })
        }
    }

    pub fn step_if<const N: usize, T: Into<TokenTypes<N>>>(
        &mut self,
        expected: T,
    ) -> Option<Token> {
        if let Some(next) = self.peek() {
            next.is(expected).then(|| {
                let i = self.index;
                self.index += 1;
                self.tokens[i]
            })
        } else {
            None
        }
    }

    pub fn more_on_line(&self) -> bool {
        self.peek().is_some_and(|tok| !tok.new_line)
    }

    pub fn peek(&self) -> Option<Token> {
        if self.index < self.tokens.len() {
            Some(self.tokens[self.index])
        } else {
            None
        }
    }

    pub fn is_at_end(&self) -> bool {
        self.index >= self.len
    }
}

macro_rules! step_or_unexpected {
    ($parser: ident, $($tok_ty: ident $($kw: ident $(($kw_val: ident))? )? $(#as $tok: ident)? => $res: expr),*) => {{
        let tok = $parser.toks.try_step();
        match tok.map(|t| (t, t.ty)) {
            $(
                #[allow(clippy::redundant_pattern)]
                Some(($($tok @)* _, TokenType::$tok_ty $((Keyword::$kw $(($kw_val))* ))* )) => $res,
            )*
            Some((tok, _)) => {
                return Err(CompileError {
                    err: Error::UnexpectedToken {
                        expected: ExpectedTokens::AnyOf(vec![$(TokenType::$tok_ty $((Keyword::$kw))*),*]),
                        found: tok.ty
                    },
                    span: Span::new(tok.start, tok.end, $parser.toks.module),
                })
            }
            None => {
                let end = $parser.toks.last_src_pos();
                return Err(CompileError {
                    err: Error::UnexpectedEndOfFile {
                        expected: ExpectedTokens::AnyOf(vec![$(TokenType::$tok_ty $((Keyword::$kw))*),*]),
                    },
                    span: Span::new(end, end, $parser.toks.module),
                })
            }
        }
    }};
}
pub(crate) use step_or_unexpected;

macro_rules! step_or_unexpected_value {
    ($parser: ident, $expected: expr, $($tok_ty: ident $($kw: ident $(($kw_val: ident))? )? $(#as $tok: ident)? => $res: expr),* $(,)?) => {{
        let tok = $parser.toks.try_step();
        match tok.map(|t| (t, t.ty)) {
            $(
                #[allow(clippy::redundant_pattern)]
                Some(($($tok @)* _, TokenType::$tok_ty $((Keyword::$kw $(($kw_val))* ))* )) => $res,
            )*
            Some((tok, _)) => {
                return Err(CompileError {
                    err: Error::UnexpectedToken {
                        expected: $expected,
                        found: tok.ty
                    },
                    span: Span::new(tok.start, tok.end, $parser.toks.module),
                })
            }
            None => {
                let end = $parser.toks.last_src_pos();
                return Err(CompileError {
                    err: Error::UnexpectedEndOfFile {
                        expected: $expected,
                    },
                    span: Span::new(end, end, $parser.toks.module),
                })
            }
        }
    }};
}
pub(crate) use step_or_unexpected_value;

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

/// Represents the necessity of delimiters in delimited lists
pub enum Delimit {
    /// Require a delimiter between elements
    Yes,
    /// Don't expect a delimiter
    No,
    /// The delimiter may be omitted
    Optional,
    /// delimiter may be omitted if the next entry starts on a new line
    OptionalIfNewLine,
}
impl From<()> for Delimit {
    fn from((): ()) -> Self {
        Self::Yes
    }
}

#[derive(Debug, Clone)]
pub enum ExpectedTokens {
    Specific(TokenType),
    AnyOf(Vec<TokenType>),
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
impl<const N: usize> From<TokenTypes<N>> for ExpectedTokens {
    fn from(t: TokenTypes<N>) -> Self {
        match t.0.as_slice() {
            [t] => Self::Specific(*t),
            other => Self::AnyOf(other.to_vec()),
        }
    }
}
impl From<TokenType> for ExpectedTokens {
    fn from(value: TokenType) -> Self {
        Self::Specific(value)
    }
}
