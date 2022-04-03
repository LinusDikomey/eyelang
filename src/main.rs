#![feature(
    let_else,
    box_patterns,
    variant_count,
    path_try_exists,
    bool_to_option,
    nonzero_ops
)]
#![warn(unused_qualifications)]

mod ast;
mod error;
mod lexer;
mod parser;
mod types;
mod ir;
#[cfg(feature = "llvm-backend")]
mod link;
mod compile;
mod backend;

#[cfg(feature = "llvm-backend")]
extern crate llvm_sys as llvm;

use crate::error::Errors;
use std::{path::Path, sync::atomic::AtomicBool};
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
}

#[derive(clap::Parser)]
#[clap(version, about, long_about = "Eye is a simple, compiled, performant programming language")]
pub struct Args {
    #[clap(arg_enum)]
    cmd: Cmd,
    file: String,
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

    /// Don't link the object file into an executable after compiling
    #[clap(long)]
    nolink: bool,

}

fn main() {
    let args = Args::parse();
    LOG.store(args.log, std::sync::atomic::Ordering::Relaxed);
    run_file(&args);
}

fn run_file(args: &Args) {
    use colored::*;
    let path = Path::new(&args.file);
    println!("{} {} ...", "Compiling".green(), args.file.underline().bright_blue());
    
    let no_extension = path.with_extension("");
    let name = no_extension.file_name()
        .expect("Failed to retrieve filename for input file")
        .to_str()
        .expect("Invalid filename");

    match run(path, args, name) {
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

fn run(
    path: &Path,
    args: &Args,
    output_name: &str
) -> Result<(), (ast::Modules, Errors)> {
    let (modules, _main, errors) = compile::path(path, args, (!args.nostd).then(|| Path::new("std")));
    let ir = match ir::reduce(&modules, errors) {
        Ok(ir) => ir,
        Err(err) => return Err((modules, err))
    };

    // temporary: compile help.c for some helper methods implemented in c
    let res = std::process::Command::new("clang")
        .args(["-c", "help.c", "-o", "eyebuild/help.o"])
        .status()
        .expect("Failed to run command to compile help.c");
    if !res.success() {
        eprintln!("The help.c compilation command failed. \
            The help.o object file is assumed to be found in the eyebuild directory now.");
    }

    log!("\n\n{ir}\n");

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

                println!("\nResult of main function: {ret_val}");
            } else {
                match std::fs::create_dir("eyebuild") {
                    Ok(()) => {}
                    Err(err) => if err.kind() != std::io::ErrorKind::AlreadyExists {
                        panic!("Failed to create build directory: {err}")
                    }
                }
                let obj_file = format!("eyebuild/{output_name}.o");
                let exe_file = format!("./eyebuild/{output_name}");
                backend::llvm::output::emit_bitcode(None, llvm_module, &obj_file);
                llvm::core::LLVMContextDispose(context);

                if args.nolink {
                    println!("{}", "Skipping link step because --nolink was specified".yellow());
                    return Ok(());
                }
                if !link::link(&obj_file, &exe_file, args) {
                    eprintln!("{}", "Aborting because linking failed".red());
                    return Ok(());
                }
                if args.cmd == Cmd::Run {
                    println!("{}", format!("Running {}...", &args.file).green());

                    std::process::Command::new(exe_file)
                        .spawn()
                        .expect("Failed to run link command")
                        .wait()
                        .expect("Running process failed");
                } else {
                    println!("{}", format!("Built {}", &args.file).green());
                }
            }
        }
        Cmd::X86Run => {
            let asm_file = std::fs::File::create(format!("./eyebuild/{output_name}.asm"))
                .expect("Failed to create assembly file");
            unsafe { backend::x86::emit(&ir, asm_file) };
        }
    }
    Ok(())
}
