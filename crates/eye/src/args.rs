use std::fmt;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, clap::ValueEnum)]
pub enum Cmd {
    /// Check a file or project for errors and warnings.
    Check,
    /// Build an executable and run it immediately.
    Run,
    /// Build an executable.
    Build,
    /// Starts a language server that can be used by IDEs for syntax highlighting, autocompletions etc.
    /// Only basic error highlighting is implemented right now.
    #[cfg(feature = "lsp")]
    Lsp,
    /// lists all available targets for the selected backend
    ListTargets,
}
impl Default for Cmd {
    fn default() -> Self {
        Self::Check
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, clap::ValueEnum)]
pub enum Backend {
    // Emit C code
    C,

    // Run with the llvm backend
    #[cfg(feature = "llvm-backend")]
    Llvm,
    /// W.I.P.! Run with the self-implemented backend. Will emit completely unoptimized code.
    /// This backend is primarily used for fast compilations. It is VERY unfinished right now.
    #[cfg(feature = "fast-backend")]
    Fast,
}
impl fmt::Display for Backend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match *self {
            Self::C => "c",
            #[cfg(feature = "llvm-backend")]
            Self::Llvm => "llvm",
            #[cfg(feature = "fast-backend")]
            Self::Fast => "fast",
        };
        f.write_str(s)
    }
}
impl Default for Backend {
    fn default() -> Self {
        #[cfg(feature = "llvm-backend")]
        {
            Self::Llvm
        }

        #[cfg(not(feature = "llvm-backend"))]
        {
            Self::Fast
        }

        #[cfg(not(any(feature = "llvm-backend", feature = "fast-backend")))]
        {
            compile_error!(
                "No backend is active. Compile with at least llvm-backend or fast-backend"
            )
        }
    }
}

#[derive(clap::Parser)]
#[clap(
    version,
    about,
    long_about = "Eye is a simple, compiled, performant programming language"
)]
#[allow(clippy::struct_excessive_bools)]
#[derive(Default)]
pub struct Args {
    #[clap(value_enum)]
    pub cmd: Cmd,
    /// Path to a file or project directory
    pub path: Option<String>,

    #[clap(short, long, value_delimiter = ',', num_args = 1..)]
    pub debug: Vec<Box<str>>,

    #[clap(long, value_delimiter = ',', num_args = 1..)]
    pub debug_functions: Vec<Box<str>>,

    /// Used for providing a custom link command. Use '[OBJ]' and '[OUT]' as placeholders for object and out file.
    /// Example: --link-cmd "ld [OBJ] -lc -o [OUT]"
    #[clap(long)]
    pub link_cmd: Option<String>,

    /// Just emit an object file. Doesn't require a main function
    #[clap(long)]
    pub emit_obj: bool,

    /// Library that doesn't require a main function.
    #[clap(long)]
    pub lib: bool,

    /// Report compilation times of all files/compilation steps.
    #[clap(long)]
    pub timings: bool,

    /// prints out all tokens after lexing.
    #[clap(long)]
    pub tokens: bool,

    /// Crash once a single error is encountered. Mostly used for debugging the compiler.
    #[clap(long)]
    pub crash_on_error: bool,

    /// Libraries to link against
    #[clap(short, long)]
    pub link: Vec<String>,

    #[clap(short, long, value_enum, default_value_t=Backend::default())]
    pub backend: Backend,

    #[clap(short, long)]
    /// The targeted backend to emit code for.
    pub target: Option<String>,

    /// This will still try to build and run the program even if errors are present. Most errors
    /// will lead to a runtime crash when the corresponding code is encountered. No correctness is
    /// guaranteed.
    #[clap(long)]
    pub run_with_errors: bool,

    #[clap(short('O'), long)]
    pub optimize: bool,
}
