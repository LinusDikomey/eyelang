use std::{iter::{Peekable, Enumerate}, str::Lines};
use color_format::*;
use crate::{ast::{Ast, ModuleId}, span::Span};
pub type EyeResult<T> = Result<T, CompileError>;

#[derive(Debug)]
pub struct Errors {
    errors: Vec<CompileError>,
}
impl Errors {
    pub fn new() -> Self {
        Self {
            errors: Vec::new()
        }
    }

    pub fn emit(&mut self, err: Error, start: u32, end: u32, module: ModuleId) {
        self.errors.push(CompileError { err, span: Span { start, end, module } });
    }
    
    pub fn emit_span(&mut self, err: Error, span: Span) {
        self.errors.push(CompileError { err, span });
    }

    pub fn emit_err(&mut self, err: CompileError) {
        self.errors.push(err);
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    #[cfg(feature = "lsp")]
    pub fn get(&self) -> &[CompileError] {
        &self.errors
    }

    pub fn print(&self, modules: &Ast) {
        for error in &self.errors {
            let (src, file) = modules.src(error.span.module);

            let s = error.span.start as usize;
            let e = error.span.end as usize;

            // calculate line and position in line
            let until_start = if s >= src.len() { src } else { &src[..s] };
            let mut line = 1;
            let mut col = 1;
            let mut start_of_line_byte = 0;
            for (i, c) in until_start.char_indices() {
                if c == '\n' {
                    line += 1;
                    col = 1;

                    start_of_line_byte = i+1;
                } else {
                    col += 1;
                }
            }

            let src_loc: std::borrow::Cow<str> = if e >= src.len() {
                if s >= src.len() {
                    "[no file location]".into()
                } else {
                    (&src[s..]).into()
                }
            } else {
                (&src[s..=e]).into()
            };
            assert!(src_loc.len() > 0, "empty source location in error");

            let pre = &src[start_of_line_byte..s];

            // find end of the line to print the rest of the line
            let post = if e == src.len() || src.as_bytes()[e] == b'\n' {
                ""
            } else {
                let mut surrounding_end = std::cmp::min(src.len(), e);
                while surrounding_end < src.len() && src.as_bytes()[surrounding_end] != b'\n' {
                    surrounding_end += 1;
                }
                &src[(e+1)..surrounding_end]
            };
            

            cprintln!("#r!<error>: #r!<{}>", error.err.conclusion());
            cprintln!("#c<at>: #u<{}:{}:{}>", file.to_string_lossy(), line, col);
            let spaces = std::cmp::max(4, (line + src_loc.lines().count() - 1).to_string().len());
            let p = cformat!("{} #c<|> ", " ".repeat(spaces));

            println!("{p}");

            let mut lines = src_loc.lines().enumerate().peekable();

            let first = lines.next().unwrap();
            
            let post_if_last = |lines: &mut Peekable<Enumerate<Lines>>| {
                if lines.peek().is_some() {
                    println!();
                } else {
                    println!("{post}");
                }
            };

            cprint!("#c<{:#4} | >{}{}", line, pre, first.1);
            post_if_last(&mut lines);

            cprintln!("{}{}#r!<{}>", p, " ".repeat(pre.chars().count()), "^".repeat(first.1.chars().count()));

            while let Some((i, line_str)) = lines.next() {
                let line = line + i;
                
                cprint!("#c<{:#4} | >{}", line, line_str);
                post_if_last(&mut lines);

                cprintln!("{}#r!<{}>", p, "^".repeat(line_str.chars().count()));
            }
            println!();
        }
    }

    pub fn _emit_unwrap<T>(&mut self, res: Result<T, CompileError>, otherwise: T) -> T {
        match res {
            Ok(t) => t,
            Err(err) => {
                self.emit_err(err);
                otherwise
            }
        }
    }

    pub fn _emit_unwrap_or<T>(&mut self, res: Result<T, CompileError>, otherwise: impl Fn() -> T) -> T {
        match res {
            Ok(t) => t,
            Err(err) => {
                self.emit_err(err);
                otherwise()
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CompileError {
    pub err: Error,
    pub span: Span
}
impl CompileError {
    pub fn new(err: Error, span: Span) -> Self {
        Self { err, span }
    }
}

#[derive(Debug, Clone, Copy)]
#[allow(unused)]
pub enum Error {
    FileSizeExceeeded,
    UnexpectedEndOfFile,
    UnexpectedCharacters,
    UnexpectedToken,
    UnknownIdent,
    UnknownType,
    UnknownFunction,
    UnknownVariable,
    UnknownModule,
    MissingMain,
    UnexpectedType,
    IntLiteralOutOfRange,
    FloatLiteralOutOfRange,
    MultipleDotsInFloatLiteral,
    UseOfUnassignedVariable,
    MissingReturnValue,
    DuplicateDefinition,
    InvalidTopLevelBlockItem,
    UnknownEscapeCode,
    TypeExpected,
    ModuleExpected,
    FunctionOrTypeExpected,
    IntExpected,
    FloatExpected,
    MismatchedType,
    ExpectedVarFoundDefinition,
    ExpectedValueFoundDefinition,
    ExpectedValueOrModuleFoundDefiniton,
    InvalidArgCount,
    CantNegateType,
    NonexistantMember,
    NonexistantEnumVariant,
    TypeMustBeKnownHere,
    MissingMainFile,
    CantAssignTo,
    CantTakeRef,
    CantDeref,
    CantUseRootPath,
    InferredTypeNotAllowedHere,
    ArrayTooLarge,
    ArraySizeCantBeInferredHere,
    InvalidArgumentCountForArrayIndex,
    TupleIndexingOnNonValue,
    TupleIndexOutOfRange,
    NotAnInstanceMethod,
    InvalidGenericCount { expected: u8, found: u8 },
    UnexpectedGenerics,
    NotConst,
    FunctionOrStructTypeExpected,
    RecursiveDefinition,
}
impl Error {
    pub fn conclusion(self) -> &'static str {
        match self {
            Error::FileSizeExceeeded => "maximum file size exceeded",
            Error::UnexpectedEndOfFile => "unexpected end of file",
            Error::UnexpectedCharacters => "unexpected characters",
            Error::UnexpectedToken => "token was not expected here",
            Error::UnknownIdent => "identifier not found",
            Error::UnknownType => "type not found",
            Error::UnknownFunction => "function not found",
            Error::UnknownVariable => "variable not found",
            Error::UnknownModule => "module not found",
            Error::MissingMain => "no main function provided",
            Error::UnexpectedType => "type was not expected here",
            Error::IntLiteralOutOfRange => "int literal out of range",
            Error::FloatLiteralOutOfRange => "float literal out of range",
            Error::MultipleDotsInFloatLiteral => "multiple dots in float literal",
            Error::UseOfUnassignedVariable => "variable is uninitialized here",
            Error::MissingReturnValue => "missing return value",
            Error::DuplicateDefinition => "duplicate definition",
            Error::InvalidTopLevelBlockItem => "block item found in top level scope",
            Error::UnknownEscapeCode => "invalid escape code",
            Error::TypeExpected => "expected a type",
            Error::ModuleExpected => "expected a module",
            Error::FunctionOrTypeExpected => "expected a type or function",
            Error::IntExpected => "integer expected",
            Error::FloatExpected => "float expected",
            Error::MismatchedType => "type mismatch",
            Error::ExpectedVarFoundDefinition => "expected variable but found a definition",
            Error::ExpectedValueFoundDefinition => "expected value but found a definition",
            Error::ExpectedValueOrModuleFoundDefiniton => "expected value or module but found a definition",
            Error::InvalidArgCount => "invalid argument count",
            Error::CantNegateType => "can't negate this value",
            Error::NonexistantMember => "member doesn't exist",
            Error::NonexistantEnumVariant => "enum variant doesn't exist",
            Error::TypeMustBeKnownHere => "type of value must be known here",
            Error::MissingMainFile => "no main.eye file found",
            Error::CantAssignTo => "not assignable",
            Error::CantTakeRef => "can't take reference of value",
            Error::CantDeref => "can't dereference value",
            Error::CantUseRootPath => "root path can't be used here",
            Error::InferredTypeNotAllowedHere => "type can't be inferred here",
            Error::ArrayTooLarge => "maximum array size exceeded",
            Error::ArraySizeCantBeInferredHere => "can't infer array size here",
            Error::InvalidArgumentCountForArrayIndex => "single argument for array index expected",
            Error::TupleIndexingOnNonValue => "indexing a non-tuple",
            Error::TupleIndexOutOfRange => "tuple doesn't have this many items",
            Error::NotAnInstanceMethod => "not an instance method",
            Error::InvalidGenericCount { .. } => "invalid generic count",
            Error::UnexpectedGenerics => "no generics expected",
            Error::NotConst => "can't evaluate constantly",
            Error::FunctionOrStructTypeExpected => "expected a struct type or a function",
            Error::RecursiveDefinition => "definition depends on itself recursively"
        }
    }
}
impl Error {
    pub fn at(self, start: u32, end: u32, module: ModuleId) -> CompileError {
        CompileError {
            err: self,
            span: Span::new(start, end, module)
        }
    }
    pub fn at_span(self, span: Span) -> CompileError {
        CompileError { err: self, span }
    }
}