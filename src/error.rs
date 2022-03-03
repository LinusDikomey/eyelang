use colored::Colorize;

pub type EyeResult<T> = Result<T, CompileError>;

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
            for c in until_start.chars() {
                if c == '\n' {
                    line += 1;
                    col = 1;
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
            let mut surrounding_start = s;
            while surrounding_start > 0 && (s - surrounding_start) < 40 && src.bytes().nth(surrounding_start - 1).unwrap() != b'\n' {
                surrounding_start -= 1;
            }
            let mut surrounding_end = std::cmp::min(src.len() - 1, e);
            while surrounding_end < src.len() - 1 && (surrounding_end - e) < 20 && src.bytes().nth(surrounding_end + 1).unwrap() != b'\n' {
                surrounding_end += 1;
            }
            println!("{}: {} '{}'", "error".bright_red(), format!("{:?}", error.err).bright_red(), src_loc.cyan());
            println!("{} {}", "at:".cyan(), format!("{file}:{line}:{col}").underline());
            let spaces = std::cmp::max(4, line.to_string().len());
            let p = format!("{} | ", " ".repeat(spaces)).cyan();
            let line_p = format!("{line:#4} | ").cyan();
            println!("{p}\n{line_p}{}", &src[surrounding_start..=surrounding_end]);
            println!("{p}{}{}", " ".repeat(src[surrounding_start..s].chars().count()), "^".repeat(src_loc.chars().count()).bright_red());
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
    UnexpectedCharacter,
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