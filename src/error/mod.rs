use crate::lexer::tokens::{SourcePos, TokenType};




#[derive(Debug)]
pub enum EyeError {
    CompileError(CompileError, SourcePos, SourcePos)
}

#[derive(Debug)]
pub enum CompileError {
    UnexpectedEndOfFile,
    UnexpectedCharacter(char, String),
    UnexpectedToken(TokenType, Vec<String>),
}