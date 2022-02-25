pub mod tokens;

use tokens::Token;

use crate::error::{CompileError, EyeError, EyeResult};

use self::tokens::{Keyword, Operator, SourcePos, TokenType};

#[derive(Debug)]
pub struct TokenStream {
    pub tokens: Vec<Token>
}

impl TokenStream {

    pub fn from_source(source: &str) -> Result<Self, EyeError> {
        let mut lexer = Lexer { chars: source.chars().collect(), index: 0, line: 1, col: 1, tokens: Vec::new() };
        
        lexer.parse()?;

        Ok(Self { tokens: lexer.tokens })
    }

}

struct Lexer {
    chars: Vec<char>,
    index: usize,
    line: u64,
    col: u64,
    tokens: Vec<Token>
}

impl Lexer {

    fn parse(&mut self) -> Result<(), EyeError> {
        while self.index < self.chars.len() {
            self.skip_junk();
            if self.is_at_end() { break; }

            if let Some(token) = self.parse_token()? {
                self.tokens.push(token);
            }
        }
        Ok(())
    }

    fn pos(&self) -> SourcePos {
        SourcePos::new(self.line, self.col)
    }

    fn parse_token(&mut self) -> Result<Option<Token>, EyeError> {
        let start = SourcePos::new(self.line, self.col);
        
        let mut val = String::new();

        let ty = loop {
            if self.is_at_end() {
                return Ok(None);
            }
            break match self.current() {
                '#' => {
                    if let Some('*') = self.peek() {
                        self.step();
                        self.parse_multiline_comment()?;
                    } else {
                        while let Some(c) = self.step() {
                            match c {
                                '#' if matches!(self.peek(), Some('*')) => {
                                    self.step();
                                    if self.parse_multiline_comment()? > 0 { break; }
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
                    val.push(self.current());
                    let mut is_float = false;
                    while match self.peek() {
                        Some('0'..='9') => true,
                        Some('.') => {
                            if is_float {
                                return Err(EyeError::CompileError(
                                    CompileError::UnexpectedCharacter('.', String::from("Multiple dots in float literal aren't allowed")),
                                    start,
                                    SourcePos::new(self.line, self.col)
                                ));
                            }
                            is_float = true;
                            true
                        },
                        _ => false
                        
                    } {
                        val.push(self.step().unwrap())
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
                            Some('\\') => {
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
                            }
                            Some(c) => val.push(c),
                            None => return Err(EyeError::CompileError(
                                CompileError::UnexpectedEndOfFile,
                                start,
                                self.pos()
                            ))
                        }
                    }
                    self.step();
                    TokenType::StringLiteral
                },
                'A'..='Z' | 'a'..='z' => { // keyword/identifier
                    let mut keyword_or_literal = String::from(self.current());
                    while match self.peek() {
                        Some('A'..='Z' | 'a'..='z' | '0'..='9') => true,
                        _ => false
                        
                    } {
                        keyword_or_literal.push(self.step().unwrap())
                    }

                    if let Some(keyword) = Keyword::from_string(&keyword_or_literal) {
                        TokenType::Keyword(keyword)
                    } else {
                        val = keyword_or_literal;
                        TokenType::Ident
                    }
                },
                _ => return Err(EyeError::CompileError(
                    CompileError::UnexpectedCharacter(self.current(), String::from("Unexpected character")),
                    start,
                    start.next()
                ))
            };
        };
        
        self.step();
        let end = SourcePos::new(self.line, self.col);

        Ok(Some(Token::new(ty, val, start, end)))
    }
    
    fn parse_multiline_comment(&mut self) -> EyeResult<usize> {
        let mut newlines = 0;
        loop {
            match self.step() {
                Some('*') if matches!(self.peek(), Some('#')) => {
                    self.step();
                    break;
                }
                Some('#') if matches!(self.peek(), Some('*')) => {
                    self.step();
                    newlines += self.parse_multiline_comment()?;
                }
                Some('\n') => newlines += 1,
                None => return Err(EyeError::CompileError(CompileError::UnexpectedEndOfFile, self.pos(), self.pos())),
                _ => {}

            }
        }
        Ok(newlines)
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
        self.chars[self.index]
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
        self.peek_count(1)
    }

    fn peek_count(&self, count: usize) -> Option<char> {
        let peek_index = self.index + count;
        if peek_index < self.chars.len() {
            Some(self.chars[peek_index])
        } else {
            None
        }
    }
}