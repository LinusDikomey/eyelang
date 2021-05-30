pub mod tokens;

use tokens::Token;

use crate::error::{CompileError, EyeError};

use self::tokens::{FloatLiteral, IntLiteral, Keyword, SourcePos, TokenType};

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
            self.skip_junk()?;
            if self.index >= self.chars.len() { break }

            let token = self.parse_token()?;
            self.tokens.push(token);
        }
        Ok(())
    }

    fn parse_token(&mut self) -> Result<Token, EyeError> {
        let start = SourcePos::new(self.line, self.col);
        
        let ty = match self.current() {
            ';' => TokenType::Semicolon,
            ':' => {
                if let Some(':') = self.peek() {
                    self.step();
                    TokenType::DoubleColon
                } else {
                    TokenType::Colon
                }
            },
            '(' => TokenType::LParen,
            ')' => TokenType::RParen,
            '{' => TokenType::LBrace,
            '}' => TokenType::RBrace,
            '[' => TokenType::LBracket,
            ']' => TokenType::RBracket,

            '0'..='9' => { // int/float literal
                let mut literal = String::from(self.current());
                let mut is_float = false;
                while match self.peek() {
                    Some('0'..='9') => true,
                    Some('.') => {
                        if is_float {
                            return Err(EyeError::CompileError(CompileError::UnexpectedCharacter('.', String::from("Multiple dots in float literal aren't allowed"))));
                        }
                        is_float = true;
                        true
                    },
                    _ => false
                    
                } {
                    literal.push(self.step().unwrap())
                }
                if is_float {
                    TokenType::FloatLiteral(FloatLiteral { val: literal, ty: None })
                } else {
                    TokenType::IntLiteral(IntLiteral { val: literal, ty: None })
                }
            },
            '"' => { // string literal
                let mut literal = String::new();
                while self.peek() != Some('"') {
                    match self.step() {
                        Some(c) => literal.push(c),
                        None => return Err(EyeError::CompileError(CompileError::UnexpectedEndOfFile))
                    }
                }
                TokenType::StringLiteral(literal)
            },
            'A'..='z' => { // keyword/identifier
                let mut ident = String::from(self.current());
                while match self.peek() {
                    Some('A'..='z' | '0'..='9') => true,
                    _ => false
                    
                } {
                    ident.push(self.step().unwrap())
                }

                if let Some(keyword) = Keyword::from_string(&ident) {
                    TokenType::Keyword(keyword)
                } else {
                    TokenType::Ident(ident)
                }
            },
            _ => return Err(EyeError::CompileError(CompileError::UnexpectedCharacter(self.current(), String::from("Unexpected character"))))
        };
        
        self.step();
        let end = SourcePos::new(self.line, self.col);

        Ok(Token::new(ty, start, end))
    }

    fn skip_junk(&mut self) -> Result<(), EyeError> {
        
        while match self.current() {
            ' ' | '\r' | '\n' => true,
            _ => false
        } { 
            if self.step().is_none() { // end of file, no more checking for junk tokens
                return Ok(())
            }
        }

        Ok(())
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