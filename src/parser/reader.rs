use crate::{token::{TokenType, Token}, ast::ModuleId, error::{CompileError, Error}, span::Span};


pub struct TokenReader {
    tokens: Vec<Token>,
    index: usize,
    len: usize,
    pub module: ModuleId
}

impl TokenReader {
    pub fn new(tokens: Vec<Token>, module: ModuleId) -> Self {
        let len = tokens.len();
        Self { tokens, index: 0, len, module }
    }
    pub fn current(&self) -> Result<&Token, CompileError> {
        if self.index < self.len {
            Ok(&self.tokens[self.index])
        } else {
            let end = self.last_src_pos();
            Err(CompileError {
                err: Error::UnexpectedEndOfFile,
                span: Span::new(end, end, self.module)
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
        self.current()
            .map(|tok| tok.end)
            .ok()
            .or_else(|| self.tokens.last().map(|last| last.end))
            .unwrap_or(0)
    }

    /// steps over the current token and returns it
    pub fn step(&mut self) -> Result<Token, CompileError> {
        self.index += 1;
        if self.index <= self.len { // <= because we are only getting the previous token
            Ok(self.tokens[self.index - 1])
        } else {
            let end = self.last_src_pos();
            Err(CompileError {
                err: Error::UnexpectedEndOfFile,
                span: Span::new(end, end, self.module),
            })
        }
    }

    pub fn step_back(&mut self) {
        self.index -= 1;
    }

    /// Steps over the current token and returns it. Token type checks only happen in debug mode.
    /// This should only be used if the type is known.
    pub fn step_assert(&mut self, ty: impl Into<TokenType>) -> Token {
        let tok = unsafe { self.step().unwrap_unchecked() };
        debug_assert_eq!(tok.ty, ty.into());
        tok
    }

    pub fn step_expect<const N: usize, T: Into<TokenTypes<N>>>(&mut self, expected: T)
    -> Result<Token, CompileError> {
        let expected = expected.into();
        let module = self.module;
        let tok = self.step()?;
        if !expected.0.iter().any(|expected_tok| *expected_tok == tok.ty) {
            return Err(CompileError {
                err: Error::UnexpectedToken { expected: expected.into(), found: tok.ty },
                span: Span::new(tok.start, tok.end, module)
            });
        }
        Ok(tok)
    }

    pub fn step_if<const N: usize, T: Into<TokenTypes<N>>>(&mut self, expected: T) -> Option<Token> {
        if let Some(next) = self.peek() {
            next.is(expected).then(|| self.step().unwrap())
        } else {
            None
        }
    }

    pub fn more_on_line(&self) -> bool {
        self.peek().map_or(false, |tok| !tok.new_line)
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

macro_rules! match_or_unexpected {
    ($tok_expr: expr, $module: expr, $($match_arm: pat = $match_expr: expr => $res: expr),*) => {{
        let tok = $tok_expr;
        match tok.ty {
            $($match_arm => $res,)*
            _ => return Err(CompileError {
                err: Error::UnexpectedToken {
                    expected: ExpectedTokens::AnyOf(vec![$($match_expr),*]),
                    found: tok.ty
                },
                span: Span::new(tok.start, tok.end, $module),
            })
        }
    }};
}
pub(crate) use match_or_unexpected;
macro_rules! match_or_unexpected_value {
    ($tok_expr: expr, $module: expr, $expected_tokens: expr, $($match_arm: pat => $res: expr),*) => {{
        let tok = $tok_expr;
        match tok.ty {
            $($match_arm => $res,)*
            _ => return Err(CompileError {
                err: Error::UnexpectedToken {
                    expected: $expected_tokens,
                    found: tok.ty
                },
                span: Span::new(tok.start, tok.end, $module),
            })
        }
    }};
}
pub(crate) use match_or_unexpected_value;

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
    fn from((): ()) -> Self { Self::Yes }
}
