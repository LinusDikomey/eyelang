use crate::lexer::tokens::TokenType;
pub type EyeResult<T> = Result<T, EyeError>;

#[derive(Debug)]
pub enum EyeError {
    FileSizeExceeeded,
    CompileError(CompileError, u32, u32),
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
    UnknownEscapeCode,
    TypeExpectedFoundFunction,
    FunctionExpectedFoundType
}