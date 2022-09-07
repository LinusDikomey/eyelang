#![feature(
    let_else,
    variant_count,
    fs_try_exists,
    int_log,
    int_roundings,
    array_chunks,
)]
#![warn(unused_qualifications)]

mod ast;
mod backend;
mod compile;
mod dmap;
mod error;
mod ir;
mod lexer;
mod link;
#[cfg(feature = "lsp")]
mod lsp;
mod parser;
mod types;
mod span;
mod help;

#[cfg(feature = "llvm-backend")]
extern crate llvm_sys as llvm;

use clap::StructOpt;
use color_format::*;
use std::{
    path::{Path, PathBuf},
    sync::atomic::AtomicBool, time::Duration, fmt,
};

static LOG: AtomicBool = AtomicBool::new(false);
static DEBUG_INFER: AtomicBool = AtomicBool::new(false);

macro_rules! log {
    () => {
        if $crate::LOG.load(std::sync::atomic::Ordering::Relaxed) { println!() }
    };
    ($s: expr $(,$arg: expr)*) => {
        if $crate::LOG.load(std::sync::atomic::Ordering::Relaxed) { println!($s, $($arg),*) }
    }
}
pub(crate) use log;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, clap::ArgEnum)]
enum Cmd {
    /// Check a file or project for errors and warnings.
    Check,
    /// Build an executable and run it immediately.
    Run,
    /// Build an executable.
    Build,
    /// Compile and run using LLVMs JIT compiler. Might produce different results.
    Jit,
    /// Starts a language server that can be used by IDEs for syntax highlighting, autocompletions etc.
    /// Only basic error highlighting is implemented right now.
    #[cfg(feature = "lsp")]
    Lsp,
}
impl Cmd {
    pub fn is_compiled(self) -> bool {
        match self {
            Cmd::Check => false,
            #[cfg(feature = "lsp")]
            Cmd::Lsp => false,
            _ => true
        }
    }
}
impl Default for Cmd {
    fn default() -> Self { Self::Check }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, clap::ArgEnum)]
pub enum Backend {
    // Run with the llvm backend
    #[cfg(feature = "llvm-backend")]
    LLVM,
    /// W.I.P.! Run with a self-implemented x86 backend. Will emit completely unoptimized code.
    /// This backend is primarily used for fast compilations. It is mostly unfinished right now.
    X86
}
impl Default for Backend {
    fn default() -> Self {
        #[cfg(feature = "llvm-backend")]
        { Self::LLVM }

        #[cfg(not(feature = "llvm-backend"))]
        { Self::X86 }
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
    #[clap(arg_enum)]
    cmd: Cmd,
    file: Option<String>,

    /// Enable debug logging
    #[clap(short, long)]
    log: bool,

    /// Used for providing a custom link command. Use '[OBJ]' and '[OUT]' as placeholders for object and out file.
    /// Example: --link-cmd "ld [OBJ] -lc -o [OUT]"
    #[clap(long)]
    link_cmd: Option<String>,

    /// Disables the standard library
    #[clap(long)]
    nostd: bool,

    /// Just emit an object file. Doesn't require a main function
    #[clap(long)]
    emit_obj: bool,

    /// Report compilation times of all files/compilation steps.
    #[clap(long)]
    timings: bool,

    /// prints out all tokens after lexing.
    #[clap(short, long)]
    tokens: bool,

    /// Reconstructs the src using the abstract syntax tree information. Can be used to test parser correctness.
    #[clap(short, long)]
    reconstruct_src: bool,

    /// Debug the type inferer.
    #[clap(long)]
    debug_infer: bool,

    /// Print the internal IR (intermediate representation) to stderr.
    /// This will still normally execute the subcommand.
    #[clap(long)]
    ir: bool,

    /// Print the llvm IR to stderr.
    /// This will still normally execute the subcommand.
    #[clap(long)]
    llvm_ir: bool,
    
    #[cfg_attr(
        feature = "llvm-backend",
        clap(short, long, arg_enum, default_value_t = Backend::LLVM)
    )]
    #[cfg_attr(
        not(feature = "llvm-backend"),
        clap(short, long, arg_enum, default_value_t = Backend::X86)
    )]
    backend: Backend
}

fn main() {
    let args = Args::parse();
    DEBUG_INFER.store(args.debug_infer, std::sync::atomic::Ordering::Relaxed);
    LOG.store(args.log, std::sync::atomic::Ordering::Relaxed);
    if args.log {
        ast::Expr::debug_sizes();
        ast::UnresolvedType::debug_sizes();
    }
    let errors = run(&args);
    if errors {
        std::process::exit(42)
    }
}

fn run(args: &Args) -> bool {
    #[cfg(feature = "lsp")]
    if let Cmd::Lsp = args.cmd {
        match lsp::lsp(args) {
            Ok(()) => {}
            Err(err) => {
                lsp::debug(format!("Exited with err: {:?}", err));
                std::process::exit(123)
            }
        }
        return false;
    }

    let path = Path::new(args.file.as_deref().unwrap_or("./"));

    let no_extension = path.with_extension("");
    let name = no_extension
        .file_name()
        .expect("Failed to retrieve filename for input file")
        .to_str()
        .expect("Invalid filename");

    cprintln!("#g<Compiling> #u;b!<{}> ...", name);

    run_path(path, args, name)
}

#[derive(Default)]
pub struct Stats {
    file_times: Vec<FileStats>,
    irgen: Duration
}
impl fmt::Display for Stats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, 
            "----------------------------------------\n\
            Timings of {} files:", self.file_times.len())?;
        let mut overall_lex = Duration::ZERO;
        let mut overall_parse = Duration::ZERO;

        for file in &self.file_times {
            writeln!(f, "\t{}: {:?} (lex: {:?}, parse: {:?})",
                file.name, file.lex + file.parse, file.lex, file.parse
            )?;
            overall_lex += file.lex;
            overall_parse += file.parse;
        }
        writeln!(f, "Overall: {:?} (lex: {:?}, parse: {:?}, irgen: {:?})\n\
            ----------------------------------------",
            overall_lex + overall_parse + self.irgen,
            overall_lex, overall_parse, self.irgen,
        )
    }
}

pub struct FileStats {
    name: String,
    lex: Duration,
    parse: Duration,
}

pub struct BackendStats {
    name: &'static str,
    init: Duration,
    type_creation: Duration,
    func_header_creation: Duration,
    emit: Duration
}
impl fmt::Display for BackendStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "----------------------------------------\nBackend Timings ({}):", self.name)?;
        writeln!(f, "\tInit: {:?}", self.init)?;
        writeln!(f, "\tType creation: {:?}", self.type_creation)?;
        writeln!(f, "\tFunction header creation: {:?}", self.func_header_creation)?;
        writeln!(f, "\tEmit: {:?}", self.emit)?;
        writeln!(f, "Overall: {:?}\n----------------------------------------",
            self.init + self.type_creation + self.func_header_creation + self.emit
        )
    }
}

fn run_path(path: &Path, args: &Args, output_name: &str) -> bool {
    let mut stats = Stats::default();
    let ir = {
        let debug_options = compile::Debug {
            tokens: args.tokens,
            reconstruct_src: args.reconstruct_src,
        };
        let (res, ast, errors) =
            compile::project(path, debug_options, !args.nostd, &[], !args.emit_obj, &mut stats); 
        errors.print(&ast);
        match res {
            Ok(val) => val,
            Err(()) => return true
        }
    };

    if args.ir {
        eprintln!("\n\n{ir}\n");
    }

    if args.timings {
        println!("{stats}");
    }

    let obj_file = format!("eyebuild/{output_name}.o");
    let exe_file = format!("eyebuild/{output_name}");
    let exec = || {
        cprintln!("#g<Running {}>...", output_name);
        let mut command = std::process::Command::new(&exe_file);
        // use the exec() syscall on unix systems or just spawn a child process and pass on it's exit code otherwise. 
        #[cfg(unix)]
        {
            let error = std::os::unix::prelude::CommandExt::exec(&mut command);
            panic!("Failed to exec the executable command: {error:?}");
        }
        #[cfg(not(unix))]
        {
            let status = command
            .spawn()
            .expect("Failed to run the executable command")
            .wait()
            .expect("Running process failed");
            std::process::exit(status.code().unwrap_or(0));
        }
    };

    if args.cmd.is_compiled() {
        // create eyebuild directory
        if !std::fs::try_exists("eyebuild").expect("Failed to check availability of eyebuild directory") {
            match std::fs::create_dir("eyebuild") {
                Ok(()) => (),
                Err(err) if err.kind() == std::io::ErrorKind::AlreadyExists => (),
                Err(err) => panic!("Failed to create eyebuild directory: {}", err)
            }
        }
    }

    match (args.cmd, args.backend) {
        (Cmd::Check, _) => {
            let _ = output_name;
            cprintln!("#g<Check successful ✅>");
        }
        #[cfg(feature = "llvm-backend")]
        (Cmd::Run | Cmd::Build | Cmd::Jit, Backend::LLVM) => unsafe {
            let context = llvm::core::LLVMContextCreate();
            let (llvm_module, stats) = backend::llvm::module(context, &ir, args.llvm_ir);
            if args.timings {
                println!("{stats}");
            }
            if args.cmd == Cmd::Jit {
                cprintln!("#g<JIT running>...\n");
                let ret_val = backend::llvm::output::run_jit(llvm_module);
                llvm::core::LLVMContextDispose(context);

                println!("\nResult of JIT execution: {ret_val}");
            } else {
                let bitcode_emit_start_time = std::time::Instant::now();
                backend::llvm::output::emit_bitcode(None, llvm_module, &obj_file);
                if args.timings {
                    println!("LLVM backend bitcode emit time: {:?}", bitcode_emit_start_time.elapsed());
                }
                llvm::core::LLVMContextDispose(context);

                if args.emit_obj {
                    cprintln!("#g<Object successfully emitted!>");
                    return false;
                }
                if !link::link(&obj_file, &exe_file, args) {
                    cprintln!("#r<Aborting because linking failed>");
                    return false;
                }
                if args.cmd == Cmd::Run {
                    exec();
                } else {
                    cprintln!("#g<Built #u<{}>>", output_name);
                }
            }
        }
        (Cmd::Jit, Backend::X86) => panic!("JIT compilation is not supported with the x86 backend"),
        (Cmd::Run | Cmd::Build, Backend::X86) => {
            let asm_path = PathBuf::from(format!("./eyebuild/{output_name}.asm"));
            let asm_file =
                std::fs::File::create(&asm_path).expect("Failed to create assembly file");
            unsafe { backend::x86::emit(&ir, asm_file) };
            if !backend::x86::assemble(&asm_path, Path::new(&obj_file)) {
                eprintln!("Assembler failed! Exiting");
                return true;
            }
            if !link::link(&obj_file, &exe_file, args) {
                ceprintln!("#r<Aborting because linking failed>");
                return true;
            }
            if args.cmd == Cmd::Run {
                exec();
            } else {
                cprintln!("#g<Built #u<{}>>", output_name);
            }
        }
        #[cfg(feature = "lsp")]
        (Cmd::Lsp, _) => unreachable!(),
    }
    false
}
