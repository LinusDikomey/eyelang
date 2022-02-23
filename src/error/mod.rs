use crate::lexer::tokens::{SourcePos, TokenType};



pub type EyeResult<T> = Result<T, EyeError>;

#[derive(Debug)]
pub enum EyeError {
    CompileError(CompileError, SourcePos, SourcePos),
    CompileErrorNoPos(CompileError) //TODO: improve compiler to make position hints everywhere possible
}

#[derive(Debug)]
pub enum CompileError {
    UnexpectedEndOfFile,
    UnexpectedCharacter(char, String),
    UnexpectedToken(TokenType, Vec<String>),
    UnknownType(String),
    UnknownFunction(String),
    UnknownVariable(String),
    MissingMain,
    UnexpectedType,
    IntLiteralOutOfRange,
    FloatLiteralOutOfRange,
    UseOfUnassignedVariable,
    MissingReturnValue,
    DuplicateDefinition,
    InvalidTopLevelBlockItem,
    UnknownEscapeCode
}