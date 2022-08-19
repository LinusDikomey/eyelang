use core::fmt;
use std::{iter::{Peekable, Enumerate}, str::Lines};
use color_format::*;
use crate::{ast::{Ast, ModuleId}, span::Span, lexer::tokens::TokenType, ir::Type};
pub type EyeResult<T> = Result<T, CompileError>;

#[derive(Debug)]
pub struct Errors {
    errors: Vec<CompileError>,
    warnings: Vec<CompileError>,
}
impl Errors {
    pub fn new() -> Self {
        Self {
            errors: Vec::new(),
            warnings: Vec::new(),
        }
    }

    pub fn emit(&mut self, err: Error, start: u32, end: u32, module: ModuleId) {
        self.emit_span(err, Span { start, end, module });
    }
    
    pub fn emit_span(&mut self, err: Error, span: Span) {
        self.emit_err(CompileError { err, span });
    }

    pub fn emit_err(&mut self, err: CompileError) {
        let list = match err.err.severity() {
            Severity::Error => &mut self.errors,
            Severity::Warn => &mut self.warnings,      
        };
        list.push(err);
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    pub fn warning_count(&self) -> usize {
        self.warnings.len()
    }

    #[cfg(feature = "lsp")]
    pub fn get_errors(&self) -> &[CompileError] {
        &self.errors
    }

    #[cfg(feature = "lsp")]
    pub fn get_warnings(&self) -> &[CompileError] {
        &self.warnings
    }

    pub fn print(&self, modules: &Ast) {
        if self.error_count() != 0 {
            cprintln!("#r<Finished with #u;r!<{}> error{}>",
                self.error_count(), if self.error_count() == 1 { "" } else { "s" });
            for error in &self.errors {
                print(error, modules);
            }
        } else if self.warning_count() != 0 {
            cprintln!("#r<Finished with #u;r!<{}> warning{}>",
                self.warning_count(), if self.warning_count() == 1 { "" } else { "s" });
            for warn in &self.warnings {
                print(warn, modules);
            }
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

#[derive(Debug, Clone)]
pub struct CompileError {
    pub err: Error,
    pub span: Span
}
impl CompileError {
    pub fn new(err: Error, span: Span) -> Self {
        Self { err, span }
    }
}

#[derive(Debug, Clone)]
pub enum ExpectedTokens {
    Specific(TokenType),
    AnyOf(Vec<TokenType>),
    Expr,
    Type,
}
impl fmt::Display for ExpectedTokens {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            &Self::Specific(tok) => {
                write!(f, "{}", tok)
            }
            Self::AnyOf(toks) => {
                for (i, tok) in toks.iter().enumerate() {
                    match i {
                        0 => {}
                        i if i != 0 || i == toks.len() -1 => {
                            write!(f, " or ")?;
                        }
                        _ => write!(f, ", ")?,
                    }
                    write!(f, "{tok}")?;
                }
                Ok(())
            }
            Self::Expr => write!(f, "an expression"),
            Self::Type => write!(f, "a type"),
        }
    }
}
impl<const N: usize> From<crate::parser::TokenTypes<N>> for ExpectedTokens {
    fn from(t: crate::parser::TokenTypes<N>) -> Self {
        match t.0.as_slice() {
            [t] => Self::Specific(*t),
            other => Self::AnyOf(other.to_vec())
        }
    }
}

#[derive(Debug, Clone)]
#[allow(unused)]
pub enum Error {
    FileSizeExceeeded,
    UnexpectedEndOfFile,
    UnexpectedCharacters,
    UnexpectedToken { expected: ExpectedTokens, found: TokenType },
    UnknownIdent,
    UnknownType,
    UnknownFunction,
    UnknownVariable,
    UnknownModule,
    MissingMain,
    InvalidMainReturnType(Type),
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
    ExpectedValueFoundFunction,
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
    CantIndex,
    ExpectedConstValue,
    UnusedStatementValue,
    InfiniteLoop,
    NotAPattern,
}
impl Error {
    pub fn conclusion(&self) -> &'static str {
        match self {
            Error::FileSizeExceeeded => "maximum file size exceeded",
            Error::UnexpectedEndOfFile => "unexpected end of file",
            Error::UnexpectedCharacters => "unexpected characters",
            Error::UnexpectedToken { .. } => "token was not expected here",
            Error::UnknownIdent => "identifier not found",
            Error::UnknownType => "type not found",
            Error::UnknownFunction => "function not found",
            Error::UnknownVariable => "variable not found",
            Error::UnknownModule => "module not found",
            Error::MissingMain => "no main function provided",
            Error::InvalidMainReturnType(_) => "invalid main return type",
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
            Error::ExpectedValueFoundFunction => "expected value but found a function",
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
            Error::RecursiveDefinition => "definition depends on itself recursively",
            Error::CantIndex => "can't index this",
            Error::ExpectedConstValue => "constant value expected",
            Error::UnusedStatementValue => "unused expression value",
            Error::InfiniteLoop => "possibly detected infinite loop",
            Error::NotAPattern => "not a pattern",
        }
    }
    pub fn details(&self) -> Option<String> {
        Some(match self {
            Error::UnexpectedToken { expected, found } => cformat!(
                "expected {} but found {}",
                expected, found
            ),
            Error::InvalidMainReturnType(ty) => cformat!(
                "the main function should return either an integer or the unit type #m<()> but returns {}",
                ty
            ),
            Error::InvalidGenericCount { expected, found } => cformat!(
                "expected #y<{}> parameters but found #r<{}>",
                expected, found
            ),
            Error::UnusedStatementValue => cformat!(
                "this statement only produces a value that is not used"
            ),
            Error::NotAPattern => cformat!(
                "this expression is not a valid pattern"
            ),
            _ => return None
        })
    }
    pub fn severity(&self) -> Severity {
        match self {
            Self::UnusedStatementValue => Severity::Warn,
            _ => Severity::Error
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Severity { Error, Warn }
impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Error => cwrite!(f, "#r!<error>"),
            Self::Warn => cwrite!(f, "#y!<warn>"),
        }
    }
}

fn print(error: &CompileError, modules: &Ast) {
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
    

    cprint!("{}: ", error.err.severity());
    match error.err.severity() {
        Severity::Error => cprintln!("#r!<{}>", error.err.conclusion()),
        Severity::Warn => cprintln!("#y!<{}>", error.err.conclusion()),
    }
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

    let pre_error_offset = " ".repeat(pre.chars().count());
    match error.err.severity() {
        Severity::Error => cprintln!("{}{}#r!<{}>", p, pre_error_offset, "^".repeat(first.1.chars().count())),
        Severity::Warn => cprintln!("{}{}#y!<{}>", p, pre_error_offset, "^".repeat(first.1.chars().count()))
    }
    if let Some(details) = error.err.details() {
        cprintln!("{}{}{}", p, pre_error_offset, details)
    }

    while let Some((i, line_str)) = lines.next() {
        let line = line + i;
        
        cprint!("#c<{:#4} | >{}", line, line_str);
        post_if_last(&mut lines);

        match error.err.severity() {
            Severity::Error => cprintln!("{}#r!<{}>", p, "^".repeat(line_str.chars().count())),
            Severity::Warn => cprintln!("{}#y!<{}>", p, "^".repeat(line_str.chars().count())),
        }
    }
    println!();
}