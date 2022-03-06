use std::{iter::{Peekable, Enumerate}, str::Lines};

use colored::Colorize;

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

    pub fn emit(&mut self, err: Error, start: u32, end: u32) {
        self.errors.push(CompileError { err, start, end })
    }

    pub fn has_errors(&self) -> bool {
        self.errors.len() > 0
    }

    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    pub fn print(&self, src: &str, file: &str) {
        for error in &self.errors {
            let s = error.start as usize;
            let e = error.end as usize;

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
            println!("{} {}", "at:".cyan(), format!("{file}:{line}:{col}").underline());
            let spaces = std::cmp::max(4, (line + src_loc.lines().count() - 1).to_string().len());
            let p = format!("{} | ", " ".repeat(spaces)).cyan();

            println!("{p}");

            let mut lines = src_loc.lines().enumerate().peekable();

            let first = lines.next().unwrap();
            
            let post_if_last = |lines: &mut Peekable<Enumerate<Lines>>| {
                if lines.peek().is_some() {
                    println!();
                } else {
                    println!("{post}")
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
}

#[derive(Debug, Clone, Copy)]
pub struct CompileError {
    pub err: Error,
    pub start: u32,
    pub end: u32
}

#[derive(Debug, Clone, Copy)]
pub enum Error {
    FileSizeExceeeded,
    UnexpectedEndOfFile,
    UnexpectedCharacters,
    UnexpectedToken,
    UnknownType,
    UnknownFunction,
    UnknownVariable,
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
    TypeExpectedFoundFunction,
    FunctionExpectedFoundType
}
impl Error {
    pub fn at(self, start: u32, end: u32) -> CompileError {
        CompileError {
            err: self,
            start,
            end
        }
    }
}