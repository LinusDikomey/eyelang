#![allow(unused)]

use std::{iter::{Peekable, Enumerate}, str::Lines};
use colored::Colorize;

use crate::{lexer::Span, ast::{Modules, ModuleId}};
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

    pub fn emit_err(&mut self, err: CompileError) {
        self.errors.push(err);
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    pub fn print(&self, modules: &Modules) {
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
                    format!("[end of file {s} {e} >= {}]", src.len()).into()
                } else {
                    (&src[s..]).into()
                }
            } else {
                (&src[s..=e]).into()
            };
            assert!(src_loc.len() > 0, "empty source location in error");

            let pre = &src[start_of_line_byte..s];

            // find end of the line to print the rest of the line
            let post = if src.as_bytes()[e] == b'\n' || e == src.len() {
                ""
            } else {
                let mut surrounding_end = std::cmp::min(src.len(), e);
                while surrounding_end < src.len() && src.as_bytes()[surrounding_end] != b'\n' {
                    surrounding_end += 1;
                }
                &src[(e+1)..surrounding_end]
            };
            

            println!("{}: {}", "error".bright_red(), format!("{:?}", error.err).bright_red());
            println!("{} {}", "at:".cyan(), format!("{}:{line}:{col}", file.to_string_lossy()).underline());
            let spaces = std::cmp::max(4, (line + src_loc.lines().count() - 1).to_string().len());
            let p = format!("{} | ", " ".repeat(spaces)).cyan();

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

            print!("{}{}{}", format!("{line:#4} | ").cyan(), pre, first.1);
            post_if_last(&mut lines);

            println!("{p}{}{}", " ".repeat(pre.chars().count()), "^".repeat(first.1.chars().count()).bright_red());

            while let Some((i, line_str)) = lines.next() {
                let line = line + i;
                
                print!("{}{}", format!("{line:#4} | ").cyan(), line_str);
                post_if_last(&mut lines);

                println!("{p}{}", "^".repeat(line_str.chars().count()).bright_red());
            }
            println!();
        }
    }

    pub fn emit_unwrap<T>(&mut self, res: Result<T, CompileError>, otherwise: T) -> T {
        match res {
            Ok(t) => t,
            Err(err) => {
                self.emit(err.err, err.span.start, err.span.end, err.span.module);
                otherwise
            }
        }
    }

    pub fn emit_unwrap_or<T>(&mut self, res: Result<T, CompileError>, otherwise: impl Fn() -> T) -> T {
        match res {
            Ok(t) => t,
            Err(err) => {
                self.emit(err.err, err.span.start, err.span.end, err.span.module);
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

#[derive(Debug, Clone, Copy)]
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
    ModuleNameConflictsWithDefinition,
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
    TypeMustBeKnownHere,
    MissingMainFile,
    CantAssignTo,
    TooLargePointer,
    CantTakeRef,
    CantDeref,
    CantUseRootPath,
    InferredTypeNotAllowedHere
}
impl Error {
    pub fn at(self, start: u32, end: u32, module: ModuleId) -> CompileError {
        CompileError {
            err: self,
            span: Span::new(start, end, module)
        }
    }
}