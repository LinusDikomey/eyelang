#![feature(
    let_else,
    box_patterns,
    variant_count,
    path_try_exists,
    bool_to_option,
    nonzero_ops,
    is_some_with,
    int_log
)]
#![warn(unused_qualifications)]

mod ast;
mod backend;
mod compile;
mod error;
mod ir;
mod lexer;
mod link;
#[cfg(feature = "lsp")]
mod lsp;
mod parser;
mod types;
mod help;

#[cfg(feature = "llvm-backend")]
extern crate llvm_sys as llvm;

use crate::error::Errors;
use clap::StructOpt;
use colored::Colorize;
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
    /// W.I.P! Run with a self-implemented x86 backend. Will emit completely unoptimized code.
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
    /// Reconstructs the src using the abstract syntax tree information. Can be used to test parser correctness.
    #[clap(short, long)]
    reconstruct_src: bool,

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

    /// Debug the type inferer.
    #[clap(long)]
    debug_infer: bool,

    #[cfg_attr(feature = "llvm-backend", clap(short, long, arg_enum, default_value_t = Backend::LLVM))]
    #[cfg_attr(not(feature = "llvm-backend"), clap(short, long, arg_enum, default_value_t = Backend::X86))]
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
    run(&args);
}

fn run(args: &Args) {
    #[cfg(feature = "lsp")]
    if let Cmd::Lsp = args.cmd {
        match lsp::lsp(args) {
            Ok(()) => {}
            Err(err) => {
                lsp::debug(format!("Exited with err: {:?}", err));
                std::process::exit(123)
            }
        }
        return;
    }

    let path = Path::new(args.file.as_deref().unwrap_or("./"));

    let no_extension = path.with_extension("");
    let name = no_extension
        .file_name()
        .expect("Failed to retrieve filename for input file")
        .to_str()
        .expect("Invalid filename");

    println!(
        "{} {} ...",
        "Compiling".green(),
        name.underline().bright_blue()
    );

    match run_path(path, args, name) {
        Ok(()) => {}
        Err((modules, errors)) => {
            println!(
                "{} {} {}",
                "Finished with".red(),
                errors.error_count().to_string().underline().bright_red(),
                "errors".red()
            );
            errors.print(&modules);
        }
    }
}

#[derive(Default)]
pub struct Stats {
    file_times: Vec<FileStats>,
    irgen: Duration
}
impl fmt::Display for Stats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "----------------------------------------\nTimings of {} files:", self.file_times.len())?;
        let mut overall_lex = Duration::ZERO;
        let mut overall_parse = Duration::ZERO;

        for file in &self.file_times {
            writeln!(f, "\t{}: {:?} (lex: {:?}, parse: {:?})",
                file.name, file.lex + file.parse, file.lex, file.parse
            )?;
            overall_lex += file.lex;
            overall_parse += file.parse;
        }
        writeln!(f, "Overall: {:?} (lex: {:?}, parse: {:?}, irgen: {:?})\n----------------------------------------",
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

fn run_path(path: &Path, args: &Args, output_name: &str) -> Result<(), (ast::Ast, Errors)> {
    let mut stats = Stats::default();
    let ir = compile::project(path, args.reconstruct_src, !args.nostd, &[], !args.emit_obj, &mut stats)?;

    log!("\n\n{ir}\n");

    if args.timings {
        println!("{stats}");
    }

    let obj_file = format!("eyebuild/{output_name}.o");
    let exe_file = format!("eyebuild/{output_name}");
    let exec = || {
        println!("{}", format!("Running {output_name}...").green());
        let status = std::process::Command::new(&exe_file)
            .spawn()
            .expect("Failed to run the executable command")
            .wait()
            .expect("Running process failed");
        println!("{}", format!("\nThe program {output_name} exited with status: {status}").green());
    };

    if args.cmd.is_compiled() {
        // compile help.c for some helper methods implemented in c
        let res = std::process::Command::new("clang")
            .args(["-c", "help/help.c", "-o", "eyebuild/help.o"])
            .status()
            .expect("Failed to run command to compile help.c");
        if !res.success() {
            eprintln!("The help.c compilation command failed. \
                The help.o object file is assumed to be found in the eyebuild directory now.");
        }
    }

    match (args.cmd, args.backend) {
        (Cmd::Check, _) => {
            let _ = output_name;
            println!("{}", "Check successful ✅".green());
        }
        #[cfg(feature = "llvm-backend")]
        (Cmd::Run | Cmd::Build | Cmd::Jit, Backend::LLVM) => unsafe {
            let context = llvm::core::LLVMContextCreate();
            let (llvm_module, stats) = backend::llvm::module(context, &ir);
            if args.timings {
                println!("{stats}");
            }
            if args.cmd == Cmd::Jit {
                println!("{}", "JIT running...\n".green());
                let ret_val = backend::llvm::output::run_jit(llvm_module);
                llvm::core::LLVMContextDispose(context);

                println!("\nResult of JIT execution: {ret_val}");
            } else {
                match std::fs::create_dir("eyebuild") {
                    Ok(()) => {}
                    Err(err) => {
                        if err.kind() != std::io::ErrorKind::AlreadyExists {
                            panic!("Failed to create build directory: {err}")
                        }
                    }
                }
                let bitcode_emit_start_time = std::time::Instant::now();
                backend::llvm::output::emit_bitcode(None, llvm_module, &obj_file);
                if args.timings {
                    println!("LLVM backend bitcode emit time: {:?}", bitcode_emit_start_time.elapsed());
                }
                llvm::core::LLVMContextDispose(context);

                if args.emit_obj {
                    println!("{}", "Object successfully emitted!".green());
                    return Ok(());
                }
                if !link::link(&obj_file, &exe_file, args) {
                    eprintln!("{}", "Aborting because linking failed".red());
                    return Ok(());
                }
                if args.cmd == Cmd::Run {
                    exec();
                } else {
                    println!("{}", format!("Built {}", output_name).green());
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
                return Ok(());
            }
            if !link::link(&obj_file, &exe_file, args) {
                eprintln!("{}", "Aborting because linking failed".red());
                return Ok(());
            }
            if args.cmd == Cmd::Run {
                exec();
            } else {
                println!("{}", format!("Built {}", output_name).green());
            }
        }
        #[cfg(feature = "lsp")]
        (Cmd::Lsp, _) => unreachable!(),
    }
    Ok(())
}
