pub mod tokens;

use tokens::Token;
use crate::error::{Errors, Error};
use self::tokens::{Keyword, Operator, TokenType};

pub fn parse(src: &str, errors: &mut Errors) -> Option<Vec<Token>> {
    if src.len() > u32::MAX as usize {
        errors.emit(Error::FileSizeExceeeded, 0, 0);
        return None;
    }

    let chars = src.char_indices().map(|(i, c)| (i as u32, c)).collect();
    Some(Lexer {
        src,
        chars,
        index: 0,
        line: 0,
        col: 0,
        tokens: Vec::new()
    }.parse(errors))
}

struct Lexer<'a> {
    src: &'a str,
    chars: Vec<(u32, char)>,
    index: usize,
    line: u64,
    col: u64,
    tokens: Vec<Token>
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
        self.chars.get(self.index).unwrap_or_else(|| self.chars.last().unwrap_or(&(0, '_'))).0
    }
    fn parse_token(&mut self, errors: &mut Errors) -> Option<Token> {
        let mut start;
        
        let ty = loop {
            start = self.pos();
            if self.is_at_end() {
                return None;
            }
            break match self.current() {
                '#' => {
                    if let Some('*') = self.peek() {
                        self.step();
                        self.parse_multiline_comment(errors);
                    } else {
                        while let Some(c) = self.step() {
                            match c {
                                '#' if matches!(self.peek(), Some('*')) => {
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
                //';' => TokenType::Semicolon,
                ':' => {
                    match self.peek() {
                        Some(':') => { self.step(); TokenType::DoubleColon },
                        Some('=') => { self.step(); TokenType::Declare }
                        _ => TokenType::Colon
                    }
                },
                ',' => TokenType::Comma,
                '.' => TokenType::Dot,
                
                '(' => TokenType::LParen,
                ')' => TokenType::RParen,
                '{' => TokenType::LBrace,
                '}' => TokenType::RBrace,
                '[' => TokenType::LBracket,
                ']' => TokenType::RBracket,

                '=' => {
                    match self.peek() {
                        Some('=') => { self.step(); TokenType::Operator(Operator::Equals) }
                        _ => TokenType::Assign
                    }
                },
                '+' => TokenType::Operator(Operator::Add),
                '-' => match self.peek() {
                    Some('>') => { self.step(); TokenType::Arrow }
                    _ => TokenType::Operator(Operator::Sub),
                },
                '*' => TokenType::Operator(Operator::Mul),
                '/' => TokenType::Operator(Operator::Div),
                
                '<' => TokenType::Operator(match self.peek() {
                    Some('=') => { self.step(); Operator::LE },
                    _ => Operator::LT
                }),
                '>' => TokenType::Operator(match self.peek() {
                    Some('=') => { self.step(); Operator::GE },
                    _ => Operator::GT
                }),
                
                '0'..='9' => { // int/float literal
                    let mut is_float = false;
                    while match self.peek() {
                        Some('0'..='9') => true,
                        Some('.') => {
                            if is_float {
                                errors.emit(
                                    Error::MultipleDotsInFloatLiteral,
                                    self.pos(),
                                    self.pos()
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
                            /*Some('\\') => {
                                val.push(match self.step() {
                                    Some('n') => '\n',
                                    Some('t') => '\t',
                                    Some('"') => '"',
                                    Some(_) => return Err(EyeError::CompileError(
                                        CompileError::UnknownEscapeCode,
                                        self.pos(),
                                        self.pos()
                                    )),
                                    None => return Err(EyeError::CompileError(
                                        CompileError::UnexpectedEndOfFile, self.pos(), self.pos())
                                    )
                                });
                            }*/
                            Some(_) => {}
                            None => {
                                errors.emit(
                                    Error::UnexpectedEndOfFile,
                                    start,
                                    self.pos()
                                );
                                break;
                            }
                        }
                    }
                    self.step();
                    TokenType::StringLiteral
                },
                'A'..='Z' | 'a'..='z' => { // keyword/identifier
                    loop {
                        match self.peek() {
                            Some('A'..='Z' | 'a'..='z' | '0'..='9' | '_') => { self.step().unwrap(); }
                            _ => break
                        }
                    }
                    if let Some(keyword) = Keyword::from_str(&self.src[start as usize ..= self.pos() as usize]) {
                        TokenType::Keyword(keyword)
                    } else {
                        TokenType::Ident
                    }
                },
                _ => {
                    let pos = self.pos();
                    self.step();
                    self.skip_junk();
                    errors.emit(
                        Error::UnexpectedCharacter,
                        pos,
                        pos
                    );
                    continue;
                }
            };
        };
        let end = self.pos();
        self.step();
        Some(Token::new(ty, start, end))
    }
    
    fn parse_multiline_comment(&mut self, errors: &mut Errors) -> usize {
        let start = self.pos() - 2;
        let mut newlines = 0;
        loop {
            match self.step() {
                Some('*') if matches!(self.peek(), Some('#')) => {
                    self.step();
                    break;
                }
                Some('#') if matches!(self.peek(), Some('*')) => {
                    self.step();
                    newlines += self.parse_multiline_comment(errors);
                }
                Some('\n') => newlines += 1,
                None => {
                    errors.emit(
                        Error::UnexpectedEndOfFile,
                        start,
                        self.pos()
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
        if self.current() == '\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        self.index += 1;
        if self.index < self.chars.len() {
            Some(self.current())
        } else {
            None
        }
    }

    fn peek(&self) -> Option<char> {
        (self.index + 1 < self.chars.len()).then(|| self.chars[self.index + 1].1)
    }
}