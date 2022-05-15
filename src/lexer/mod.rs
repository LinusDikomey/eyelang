pub mod tokens;

use tokens::Token;
use crate::{error::{Errors, Error}, ast::ModuleId};
use self::tokens::TokenType;

pub fn parse(src: &str, errors: &mut Errors, module: ModuleId) -> Option<Vec<Token>> {
    if src.len() > u32::MAX as usize {
        errors.emit(Error::FileSizeExceeeded, 0, 0, module);
        return None;
    }

    let chars = src.char_indices().map(|(i, c)| (i as u32, c)).collect();
    Some(Lexer {
        src,
        chars,
        index: 0,
        tokens: Vec::new(),
        module
    }.parse(errors))
}

struct Lexer<'a> {
    src: &'a str,
    chars: Vec<(u32, char)>,
    index: usize,
    tokens: Vec<Token>,
    module: ModuleId
}

impl<'a> Lexer<'a> {
    fn parse(mut self, errors: &mut Errors) -> Vec<Token> {
        while self.index < self.chars.len() {
            self.skip_junk();
            if self.is_at_end() { break; }

            if let Some(token) = self.parse_token(errors) {
                self.tokens.push(token);
            }
        }
        self.tokens
    }

    fn pos(&self) -> u32 {
        self.chars.get(self.index)
            .map_or_else(
                || self.chars.last()
                    .map_or(0, |(pos, c)| *pos + c.len_utf8() as u32),
                |(x, _)| *x,
            )
    }
    fn parse_token(&mut self, errors: &mut Errors) -> Option<Token> {
        fn emit_invalid(invalid: &mut Option<(u32, u32)>, errors: &mut Errors, module: ModuleId) {
            if let Some((start, end)) = invalid.take() {
                errors.emit(
                    Error::UnexpectedCharacters,
                    start,
                    end,
                    module
                );
            }
        }

        let mut start;
        let mut invalid_chars = None;

        let ty = loop {
            start = self.pos();
            if self.is_at_end() {
                emit_invalid(&mut invalid_chars, errors, self.module);
                return None;
            }
            break match self.current() {
                '#' => {
                    emit_invalid(&mut invalid_chars, errors, self.module);
                    if let Some('-') = self.peek() {
                        self.step();
                        self.parse_multiline_comment(errors);
                    } else {
                        while let Some(c) = self.step() {
                            match c {
                                '#' if matches!(self.peek(), Some('-')) => {
                                    self.step();
                                    if self.parse_multiline_comment(errors) > 0 { break; }
                                }
                                '\n' => break,
                                _ => {}
                            }
                        }
                    }
                    self.step();
                    self.skip_junk();
                    continue;
                }
                ':' => {
                    match self.peek() {
                        Some(':') => { self.step(); TokenType::DoubleColon },
                        Some('=') => { self.step(); TokenType::Declare }
                        _ => TokenType::Colon
                    }
                },
                ',' => TokenType::Comma,
                ';' => TokenType::Semicolon,
                '.' => {
                    if let Some('.') = self.peek() {
                        self.step();
                        if let Some('.') = self.peek() {
                            self.step();
                            TokenType::TripleDot
                        } else {
                            self.unstep();
                            TokenType::Dot
                        }
                    } else {
                        TokenType::Dot
                    }
                }
                
                '(' => TokenType::LParen,
                ')' => TokenType::RParen,
                '{' => TokenType::LBrace,
                '}' => TokenType::RBrace,
                '[' => TokenType::LBracket,
                ']' => TokenType::RBracket,

                '=' => {
                    match self.peek() {
                        Some('=') => { self.step(); TokenType::DoubleEquals }
                        _ => TokenType::Equals
                    }
                },
                '+' => if self.step_if('=') {
                    TokenType::PlusEquals
                } else {
                    TokenType::Plus
                }
                '-' => match self.peek() {
                    Some('>') => { self.step(); TokenType::Arrow }
                    Some('=') => { self.step(); TokenType::MinusEquals }
                    _ => TokenType::Minus,
                }
                '*' => if self.step_if('=') {
                    TokenType::StarEquals
                } else {
                    TokenType::Star
                }
                '/' => if self.step_if('=') {
                    TokenType::SlashEquals
                } else {
                    TokenType::Slash
                }
                '%' => if self.step_if('=') {
                    TokenType::PercentEquals
                } else {
                    TokenType::Percent
                }
                '&' => TokenType::Ampersand,
                '~' => TokenType::SnackWave,
                '^' => TokenType::Caret,
                '_' => TokenType::Underscore,

                '<' => match self.peek() {
                    Some('=') => { self.step(); TokenType::LessEquals },
                    _ => TokenType::LessThan
                }
                '>' => match self.peek() {
                    Some('=') => { self.step(); TokenType::GreaterEquals },
                    _ => TokenType::GreaterThan
                }
                '!' => {
                    match self.peek() {
                        Some('=') => { self.step(); TokenType::BangEquals }
                        _ => TokenType::Bang
                    }
                }

                '0'..='9' => { // int/float literal
                    let mut is_float = false;
                    while match self.peek() {
                        Some('0'..='9') => true,
                        Some('.') => {
                            if is_float {
                                errors.emit(
                                    Error::MultipleDotsInFloatLiteral,
                                    self.pos(),
                                    self.pos(),
                                    self.module
                                );
                            }
                            is_float = true;
                            true
                        },
                        _ => false
                        
                    } {
                        self.step().unwrap();
                    }
                    if is_float {
                        TokenType::FloatLiteral
                    } else {
                        TokenType::IntLiteral
                    }
                }
                '"' => { // string literal
                    while self.peek() != Some('"') {
                        match self.step() {
                            Some(_) => {}
                            None => {
                                errors.emit(
                                    Error::UnexpectedEndOfFile,
                                    start,
                                    self.pos()-1,
                                    self.module
                                );
                                break;
                            }
                        }
                    }
                    self.step();
                    TokenType::StringLiteral
                },
                'A'..='Z' | 'a'..='z' => { // keyword/identifier
                    while let Some('A'..='Z' | 'a'..='z' | '0'..='9' | '_') = self.peek() {
                        self.step().unwrap();
                    }
                    if let Ok(keyword) = self.src[start as usize ..= self.pos() as usize].parse() {
                        TokenType::Keyword(keyword)
                    } else {
                        TokenType::Ident
                    }
                }
                _ => {
                    let start = self.pos();
                    self.step();
                    let end = self.pos() - 1;
                    if let Some((_, chars_end)) = &mut invalid_chars {
                        *chars_end = end;
                    } else {
                        invalid_chars = Some((start, end));
                    }
                    self.skip_junk();
                    continue;
                }
            };
        };
        emit_invalid(&mut invalid_chars, errors, self.module);
        let end = self.pos();
        self.step();
        Some(Token::new(ty, start, end))
    }
    
    fn parse_multiline_comment(&mut self, errors: &mut Errors) -> usize {
        let start = self.pos() - 1;
        let mut newlines = 0;
        loop {
            match self.step() {
                Some('-') if matches!(self.peek(), Some('#')) => {
                    self.step();
                    break;
                }
                Some('#') if matches!(self.peek(), Some('-')) => {
                    self.step();
                    newlines += self.parse_multiline_comment(errors);
                }
                Some('\n') => newlines += 1,
                None => {
                    errors.emit(
                        Error::UnexpectedEndOfFile,
                        start,
                        self.pos()-1,
                        self.module
                    );
                    break;
                }
                _ => {}

            }
        }
        newlines
    }

    fn skip_junk(&mut self) {
        if self.is_at_end() { return; }
        while let ' ' | '\r' | '\n' = self.current() {
            if self.step().is_none() { // end of file, no more checking for junk tokens
                return;
            }
            if self.is_at_end() { return; }
        }
    }

    fn is_at_end(&self) -> bool {
        self.index >= self.chars.len()
    }
    
    fn current(&self) -> char {
        self.chars[self.index].1
    }

    fn step(&mut self) -> Option<char> {
        self.index += 1;
        if self.index < self.chars.len() {
            Some(self.current())
        } else {
            None
        }
    }

    fn step_if(&mut self, c: char) -> bool {
        if self.peek() == Some(c) {
            self.step().unwrap();
            true
        } else {
            false
        }
    }

    fn peek(&self) -> Option<char> {
        (self.index + 1 < self.chars.len()).then(|| self.chars[self.index + 1].1)
    }

    fn unstep(&mut self) {
        self.index -= 1;
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Span {
    pub start: u32,
    pub end: u32,
    pub module: ModuleId
}
impl Span {
    pub fn new(start: u32, end: u32, module: ModuleId) -> Self {
        Self { start, end, module }
    }
    pub fn _todo(module: ModuleId) -> Self {
        Self { start: 0, end: 0, module }
    }
}