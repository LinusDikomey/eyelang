#![feature(iter_intersperse, let_else, box_patterns, variant_count, path_try_exists, array_windows)]
#![warn(unused_qualifications)]

mod ast;
mod error;
mod lexer;
mod parser;
mod types;
// mod interpreter;
mod ir;
mod link;
mod compile;

#[cfg(feature = "llvm-backend")]
mod llvm_codegen;

#[cfg(feature = "llvm-backend")]
extern crate llvm_sys as llvm;

use crate::error::Errors;
use std::{path::Path, sync::atomic::AtomicBool, process::Command};
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
    /// Build an executable and run it immediately.
    Run,
    /// Build an executable.
    Build,
    /// Compile and run using LLVMs JIT compiler. Might produce different results.
    Jit,
    // Interpret using a basic AST walk interpreter. This is just for testing and many programs will work differently.
    // Interpret,
}

#[derive(clap::Parser)]
#[clap(version, about, long_about = None)]
pub struct Args {
    #[clap(arg_enum)]
    cmd: Cmd,
    //#[clap(short, long, default_value_t = "eye/test.eye")]
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
}
impl Default for Args {
    fn default() -> Self {
        Self {
            cmd: Cmd::Run,
            file: "eye/test.eye".to_owned(),
            reconstruct_src: false,
            log: false,
            link_cmd: None,
        }
    }
}

fn main() {
    let args = Args::parse();
    LOG.store(args.log, std::sync::atomic::Ordering::Relaxed);
    run_file(&args);
}

fn run_file(args: &Args) {
    use colored::*;
    let path = Path::new(&args.file);
    //let src = std::fs::read_to_string(path)
    //    .expect(&format!("Could not open source file: {}", args.file));

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
    let (modules, _main, mut errors) = compile::path(path, args);
    if errors.has_errors() {
        return Err((modules, errors));
    }
    let ir = ir::reduce(&modules, &mut errors);

    log!("\n\n{ir}\n");


    if errors.has_errors() {
        return Err((modules, errors));
    }

    match args.cmd {
        #[cfg(feature = "llvm-backend")]
        Cmd::Run | Cmd::Build | Cmd::Jit => unsafe {
            let context = llvm::core::LLVMContextCreate();
            let llvm_module = llvm_codegen::module(context, &ir);
            if args.cmd == Cmd::Jit {
                println!("{}", "JIT running...\n".green());
                let ret_val = llvm_codegen::backend::run_jit(llvm_module);
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
                llvm_codegen::backend::emit_bitcode(None, llvm_module, &obj_file);
                llvm::core::LLVMContextDispose(context);

                link::link(&obj_file, &exe_file, args);
                if args.cmd == Cmd::Run {
                    println!("{}", format!("Running {}...", &args.file).green());

                    Command::new(exe_file)
                        .spawn()
                        .expect("Failed to run")
                        .wait()
                        .expect("Running process failed");
                } else {
                    println!("{}", format!("Built {}", &args.file).green());
                }
            }
        }
    }
    Ok(())
}

/*
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eye_files() {
        const EXPECTED: &'static str = 
"4
Vec before assignment: 1 2.5 3
Vec after assignment: 1 3.1 3
x: 1
Hello, John Doe
You entered: 123456789
Your number is 5 or larger
Half your number is: 61728394
Some calculations:
Bye";
        let mut output = Vec::new();
        run_file(&mut(std::io::Cursor::new(Vec::<u8>::new()), std::io::Cursor::new(&mut output)), &Args {
            cmd: Cmd::Interpret,
            file: "eye/test.eye".to_owned(),
            reconstruct_src: true,
            link_cmd: None,
            log: false
        });
        let string = String::from_utf8(output).unwrap();
        println!("{string}");
        assert_eq!(string, EXPECTED);

        let input = b"123\n";
        let mut output = Vec::new();
        run(
            &mut(std::io::Cursor::new(input), &mut output),
            "main ->: print(string(parse(read(\"Input number: \"))+i32(1)))",
            &Args {
                cmd: Cmd::Interpret,
                file: "eye/test.eye".to_owned(),
                ..Default::default()
            },
            "test"
        ).unwrap();
        println!("{:?}", String::from_utf8(output.clone()));
        assert_eq!(b"Input number: 124".as_slice(), output.as_slice());
    }
}
*/