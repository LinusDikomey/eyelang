


#[derive(Debug)]
pub enum EyeError {
    CompileError(CompileError)
}

#[derive(Debug)]
pub enum CompileError {
    UnexpectedEndOfFile,
    UnexpectedCharacter(char, String)
}