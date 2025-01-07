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
    /// W.I.P.! Run with a self-implemented x86-64 backend. Will emit completely unoptimized code.
    /// This backend is primarily used for fast compilations. It is VERY unfinished right now.
    #[cfg(feature = "x86-backend")]
    X86,
}
impl fmt::Display for Backend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match *self {
            Self::C => "C",
            #[cfg(feature = "llvm-backend")]
            Self::Llvm => "LLVM",
            Self::X86 => "x86",
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
            Self::X86
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

    /// Enable debug logging
    #[clap(long)]
    pub log: bool,

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

    /// Reconstructs the src using the abstract syntax tree information. Can be used to test parser correctness.
    #[clap(short, long)]
    pub reconstruct_src: bool,

    /// Print the internal HIR (high-level intermediate representation) to stderr.
    /// This will still normally execute the subcommand.
    #[clap(long)]
    pub hir: bool,

    /// Print the internal IR (intermediate representation) to stderr.
    /// This will still normally execute the subcommand.
    #[clap(long)]
    pub ir: bool,

    /// Print the IR of the selected backend (if the backend creates an ir) to stderr.
    /// This will still normally execute the subcommand.
    #[clap(long)]
    pub backend_ir: bool,

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

    /// Print the ir again after each optimization pass to show changes made by optimizations.
    #[clap(long)]
    pub passes: bool,
}
