use error::{CompileError, Error, Errors, span::TSpan};
use token::{ExpectedTokens, Keyword, Token, TokenType, TokenTypes};

pub struct Tokenizer<'a> {
    pub src: &'a str,
    pub errors: &'a mut Errors,
    cached: Option<Token>,
    pos: u32,
}
impl<'a> Tokenizer<'a> {
    pub fn new(src: &'a str, errors: &'a mut Errors) -> Self {
        if src.len() > u32::MAX as usize {
            panic!("Can't handle parsing of files larger than 2**32 bytes = 4GiB");
        }
        Self {
            src,
            errors,
            cached: None,
            pos: 0,
        }
    }

    pub fn step(&mut self) -> Token {
        self.cached.take().unwrap_or_else(|| self.next_token())
    }

    pub fn step_if(&mut self, ty: TokenType) -> Option<Token> {
        if let Some(token) = self.cached {
            if token.ty == ty {
                self.cached = None;
                Some(token)
            } else {
                None
            }
        } else {
            let token = self.next_token();
            if token.ty == ty {
                Some(token)
            } else {
                self.cached = Some(token);
                None
            }
        }
    }

    pub fn step_expect<const N: usize>(
        &mut self,
        expected: impl Into<TokenTypes<N>>,
    ) -> Result<Token, CompileError> {
        let expected: TokenTypes<N> = expected.into();
        let token = self.step();
        if expected.0.contains(&token.ty) {
            Ok(token)
        } else {
            Err(CompileError {
                err: Error::UnexpectedToken {
                    expected: expected.into(),
                    found: token.ty,
                },
                span: TSpan::new(token.start, token.end),
            })
        }
    }

    pub fn step_assert(&mut self, ty: TokenType) -> Token {
        let token = self.step();
        debug_assert_eq!(token.ty, ty, "Asserted that a {ty} token would follow");
        token
    }

    pub fn peek(&mut self) -> Token {
        if let Some(token) = self.cached {
            token
        } else {
            let token = self.next_token();
            self.cached = Some(token);
            token
        }
    }

    fn next_byte(&mut self) -> Option<u8> {
        ((self.pos as usize) < self.src.len()).then(|| {
            let c = self.src.as_bytes()[self.pos as usize];
            self.pos += 1;
            c
        })
    }

    fn next_byte_if_eq(&mut self, expected: u8) -> bool {
        (self.pos as usize) < self.src.len() && {
            let c = self.src.as_bytes()[self.pos as usize];
            let eq = c == expected;
            if eq {
                self.pos += 1;
            }
            eq
        }
    }

    fn peek_byte(&self) -> Option<u8> {
        self.src.as_bytes().get(self.pos as usize).copied()
    }

    fn next_token(&mut self) -> Token {
        let emit_invalid = |invalid: &mut Option<(u32, u32)>, errors: &mut Errors| {
            if let Some((start, end)) = invalid.take() {
                errors.emit_err(Error::UnexpectedCharacters.at_span(TSpan::new(start, end)));
            }
        };
        let mut invalid_chars = None;

        let mut start;
        let mut newline = false;
        let ty = loop {
            start = self.pos;
            let Some(c) = self.next_byte() else {
                emit_invalid(&mut invalid_chars, self.errors);
                return Token {
                    start: self.pos,
                    end: self.pos,
                    ty: TokenType::Eof,
                    new_line: false,
                };
            };
            break match c {
                b'\n' => {
                    newline = true;
                    continue;
                }
                b' ' | b'\t' | b'\r' => continue,
                b'#' => {
                    emit_invalid(&mut invalid_chars, self.errors);
                    if self.next_byte_if_eq(b'-') {
                        newline |= self.parse_multiline_comment();
                    } else {
                        while let Some(c) = self.next_byte() {
                            match c {
                                b'#' if self.next_byte_if_eq(b'-') => {
                                    newline |= self.parse_multiline_comment();
                                }
                                b'\n' => {
                                    newline = true;
                                    break;
                                }
                                _ => {}
                            }
                        }
                    }
                    continue;
                }
                b':' => match self.peek_byte() {
                    Some(b':') => {
                        self.next_byte();
                        TokenType::DoubleColon
                    }
                    Some(b'=') => {
                        self.next_byte();
                        TokenType::Declare
                    }
                    _ => TokenType::Colon,
                },
                b',' => TokenType::Comma,
                b';' => TokenType::Semicolon,
                b'.' if self.next_byte_if_eq(b'.') => match self.peek_byte() {
                    Some(b'.') => {
                        self.next_byte();
                        TokenType::TripleDot
                    }
                    Some(b'<') => {
                        self.next_byte();
                        TokenType::DotDotLessThan
                    }
                    _ => TokenType::DotDot,
                },
                b'.' => TokenType::Dot,

                b'(' => TokenType::LParen,
                b')' => TokenType::RParen,
                b'{' => TokenType::LBrace,
                b'}' => TokenType::RBrace,
                b'[' => TokenType::LBracket,
                b']' => TokenType::RBracket,

                b'=' if self.next_byte_if_eq(b'=') => TokenType::DoubleEquals,
                b'=' => TokenType::Equals,
                b'+' if self.next_byte_if_eq(b'=') => TokenType::PlusEquals,
                b'+' => TokenType::Plus,
                b'-' if self.next_byte_if_eq(b'>') => TokenType::Arrow,
                b'-' if self.next_byte_if_eq(b'=') => TokenType::MinusEquals,
                b'-' => TokenType::Minus,
                b'*' if self.next_byte_if_eq(b'=') => TokenType::StarEquals,
                b'*' => TokenType::Star,
                b'/' if self.next_byte_if_eq(b'=') => TokenType::SlashEquals,
                b'/' => TokenType::Slash,
                b'%' if self.next_byte_if_eq(b'=') => TokenType::PercentEquals,
                b'%' => TokenType::Percent,
                b'<' if self.next_byte_if_eq(b'=') => TokenType::LessEquals,
                b'<' => TokenType::LessThan,
                b'>' if self.next_byte_if_eq(b'=') => TokenType::GreaterEquals,
                b'>' => TokenType::GreaterThan,
                b'!' if self.next_byte_if_eq(b'=') => TokenType::BangEquals,
                b'!' => TokenType::Bang,

                b'&' => TokenType::Ampersand,
                b'~' => TokenType::SnackWave,
                b'^' => TokenType::Caret,
                b'@' => TokenType::At,

                b'0'..=b'9' => {
                    // int/float literal
                    let mut is_float = false;
                    while matches!(self.peek_byte(), Some(b'0'..=b'9' | b'.')) {
                        if self.next_byte().unwrap() == b'.' {
                            if let Some(b'.') = self.peek_byte() {
                                self.pos -= 1;
                                break;
                            }
                            if is_float {
                                self.errors.emit_err(
                                    Error::MultipleDotsInFloatLiteral.at(self.pos, self.pos),
                                );
                            }
                            is_float = true;
                        }
                    }
                    if is_float {
                        TokenType::FloatLiteral
                    } else {
                        TokenType::IntLiteral
                    }
                }
                b'"' => {
                    // string literal
                    loop {
                        match self.next_byte() {
                            Some(b'"') => break,
                            Some(_) => {}
                            None => {
                                self.errors.emit_err(
                                    Error::UnexpectedEndOfFile {
                                        expected: ExpectedTokens::EndOfStringLiteral,
                                    }
                                    .at_span(TSpan::new(start, self.pos)),
                                );
                                break;
                            }
                        }
                    }
                    TokenType::StringLiteral
                }
                c @ (b'A'..=b'Z' | b'a'..=b'z' | b'_') => {
                    // keyword/identifier
                    if c == b'_' && !is_ident_byte(self.peek_byte()) {
                        break TokenType::Underscore;
                    }
                    while is_ident_byte(self.peek_byte()) {
                        self.next_byte();
                    }
                    if let Some(keyword) =
                        Keyword::parse(&self.src[start as usize..self.pos as usize])
                    {
                        TokenType::Keyword(keyword)
                    } else {
                        TokenType::Ident
                    }
                }
                _ => {
                    if let Some((_, chars_end)) = &mut invalid_chars {
                        *chars_end = self.pos;
                    } else {
                        invalid_chars = Some((start, self.pos));
                    }
                    continue;
                }
            };
        };
        emit_invalid(&mut invalid_chars, self.errors);
        let end = self.pos;
        Token::new(ty, start, end, newline)
    }

    #[must_use = "newline state shouldn't be ignored"]
    fn parse_multiline_comment(&mut self) -> bool {
        let start = self.pos - 2;
        let mut newline = false;
        let mut comment_depth = 1;
        loop {
            let Some(c) = self.next_byte() else {
                self.errors.emit_err(
                    Error::UnexpectedEndOfFile {
                        expected: ExpectedTokens::EndOfMultilineComment,
                    }
                    .at_span(TSpan::new(start, self.pos)),
                );
                break;
            };
            match c {
                b'\n' => newline = true,
                b'#' if self.next_byte_if_eq(b'-') => comment_depth += 1,
                b'-' if self.next_byte_if_eq(b'#') => {
                    comment_depth -= 1;
                    if comment_depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
        }
        newline
    }

    pub fn pos(&self) -> u32 {
        self.pos
    }
}

fn is_ident_byte(c: Option<u8>) -> bool {
    matches!(c, Some(b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'_'))
}
