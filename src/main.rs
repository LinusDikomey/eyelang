#![feature(
    let_else,
    box_patterns,
    variant_count,
    path_try_exists,
    bool_to_option,
    nonzero_ops,
)]
#![warn(unused_qualifications)]

mod ast;
mod error;
mod lexer;
mod parser;
mod types;
mod ir;
mod link;
mod compile;
mod backend;
#[cfg(feature = "lsp")]
mod lsp;

#[cfg(feature = "llvm-backend")]
extern crate llvm_sys as llvm;

use crate::error::Errors;
use std::{path::{Path, PathBuf}, sync::atomic::AtomicBool};
use clap::StructOpt;
use colored::Colorize;

static LOG: AtomicBool = AtomicBool::new(false);

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
    #[cfg(feature = "llvm-backend")]
    Run,
    /// Build an executable.
    #[cfg(feature = "llvm-backend")]
    Build,
    /// Compile and run using LLVMs JIT compiler. Might produce different results.
    #[cfg(feature = "llvm-backend")]
    Jit,
    /// Run with a self-implemented x86 backend. Will emit completely unoptimized code.
    /// This backend is primarily used for fast compilations.
    X86Run,
    /// Starts a language server that can be used by IDEs for syntax highlighting, autocompletions etc.
    #[cfg(feature = "lsp")]
    Lsp
}
impl Default for Cmd {
    fn default() -> Self {
        Self::Check
    }
}

#[derive(clap::Parser)]
#[clap(version, about, long_about = "Eye is a simple, compiled, performant programming language")]
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
    emit_obj: bool
}

fn main() {
    let args = Args::parse();
    LOG.store(args.log, std::sync::atomic::Ordering::Relaxed);
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
    println!("{} {} ...", "Compiling".green(), args.file.as_deref().unwrap_or("").underline().bright_blue());

    let no_extension = path.with_extension("");
    let name = no_extension.file_name()
        .expect("Failed to retrieve filename for input file")
        .to_str()
        .expect("Invalid filename");

    match run_path(path, args, name) {
        Ok(()) => {}
        Err((modules, errors)) => {
            println!("{} {} {}",
                "Finished with".red(),
                errors.error_count().to_string().underline().bright_red(),
                "errors".red()
            );
            errors.print(&modules);
        }
    }
}

fn run_path(
    path: &Path,
    args: &Args,
    output_name: &str
) -> Result<(), (ast::Modules, Errors)> {
    let ir = compile::project(path, args.reconstruct_src, !args.nostd, &[], !args.emit_obj)?;
    
    log!("\n\n{ir}\n");
    let obj_file = format!("eyebuild/{output_name}.o");
    let exe_file = format!("eyebuild/{output_name}");
    let exec = || {
        println!("{}", format!("Running {}...", output_name).green());
        std::process::Command::new(&exe_file)
            .spawn()
            .expect("Failed to run the executable command")
            .wait()
            .expect("Running process failed");
    };

    match args.cmd {
        Cmd::Check => {
            let _ = output_name;
            println!("{}", "Check successful ✅".green());
        }
        #[cfg(feature = "llvm-backend")]
        Cmd::Run | Cmd::Build | Cmd::Jit => unsafe {
            let context = llvm::core::LLVMContextCreate();
            let llvm_module = backend::llvm::module(context, &ir);
            if args.cmd == Cmd::Jit {
                println!("{}", "JIT running...\n".green());
                let ret_val = backend::llvm::output::run_jit(llvm_module);
                llvm::core::LLVMContextDispose(context);

                println!("\nResult of JIT execution: {ret_val}");
            } else {
                match std::fs::create_dir("eyebuild") {
                    Ok(()) => {}
                    Err(err) => if err.kind() != std::io::ErrorKind::AlreadyExists {
                        panic!("Failed to create build directory: {err}")
                    }
                }
                // temporary: compile help.c for some helper methods implemented in c
                let res = std::process::Command::new("clang")
                    .args(["-c", "help/help.c", "-o", "eyebuild/help.o"])
                    .status()
                    .expect("Failed to run command to compile help.c");
                if !res.success() {
                    eprintln!("The help.c compilation command failed. \
                        The help.o object file is assumed to be found in the eyebuild directory now.");
                }
                backend::llvm::output::emit_bitcode(None, llvm_module, &obj_file);
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
        Cmd::X86Run => {
            let asm_path = PathBuf::from(format!("./eyebuild/{output_name}.asm"));
            let asm_file = std::fs::File::create(&asm_path)
                .expect("Failed to create assembly file");
            unsafe { backend::x86::emit(&ir, asm_file) };
            if !backend::x86::assemble(&asm_path, Path::new(&obj_file)) {
                eprintln!("Assembler failed! Exiting");
                return Ok(());
            }
            if !link::link(&obj_file, &exe_file, args) {
                eprintln!("{}", "Aborting because linking failed".red());
                return Ok(());
            }
            exec();
        }
        #[cfg(feature = "lsp")]
        Cmd::Lsp => unreachable!()
    }
    Ok(())
}
