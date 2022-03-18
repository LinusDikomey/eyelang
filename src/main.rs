#![feature(iter_intersperse, let_else, box_patterns, variant_count)]

mod ast;
mod error;
mod lexer;
mod parser;
mod types;
mod interpreter;
mod ir;
mod link;

#[cfg(feature = "llvm-backend")]
mod llvm_codegen;

#[cfg(feature = "llvm-backend")]
extern crate llvm_sys as llvm;

use crate::{parser::Parser, interpreter::Scope, error::{Errors, Error}, ast::repr::Repr};
use std::{path::Path, sync::atomic::AtomicBool, process::Command};

static LOG: AtomicBool = AtomicBool::new(false);

macro_rules! log {
    () => {
        if $crate::LOG.load(std::sync::atomic::Ordering::Relaxed) { println!() }
    };
    ($s: expr $(,$arg: expr)*) => {
        if $crate::LOG.load(std::sync::atomic::Ordering::Relaxed) { println!($s, $($arg),*) }
    }
}
use colored::Colorize;
use log;

#[derive(Clone, Copy)]
enum Backend {
    TreeWalkInterpreter,
    #[cfg(feature = "llvm-backend")]
    LLVM(LLVMAction)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum LLVMAction {
    Jit,
    Build,
    Run
}

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let mut src_file = None;
    let mut reconstruct_ast = false;
    let mut backend;
    #[cfg(feature = "llvm-backend")]
    {
        backend = Backend::LLVM(LLVMAction::Run);
    }
    #[cfg(not(feature = "llvm-backend"))]
    {
        backend = Backend::TreeWalkInterpreter;
    }
    
    for arg in &args {
        match arg.as_str() {
            "-i" | "--interpret" => backend = Backend::TreeWalkInterpreter,
            "-l" | "--log" => LOG.store(true, std::sync::atomic::Ordering::SeqCst),
            "-r" | "--reconstruct-ast" => reconstruct_ast = true,
            "-j" | "--jit" => backend = Backend::LLVM(LLVMAction::Jit),
            "-b" | "--build" => backend = Backend::LLVM(LLVMAction::Build),
            unknown if unknown.starts_with("-") => eprintln!("Unrecognized argument {unknown}"),
            positional => if src_file.is_none() {
                src_file = Some(positional)
            } else {
                panic!("Too many positional arguments")
            },
        }
    }

    let src_file = src_file.unwrap_or("eye/test.eye");
    run_file(&mut (std::io::stdin().lock(), std::io::stdout()), src_file, reconstruct_ast, backend);
}

fn run_file<R: std::io::BufRead, W: std::io::Write>(io: &mut (R, W), file: &str, reconstruct_ast: bool, backend: Backend) {
    use colored::*;
    let path = Path::new(&file);
    let src = std::fs::read_to_string(path)
        .expect(&format!("Could not open source file: {}", file));

    println!("{} {} ...", "Compiling".green(), file.underline().bright_blue());
    
    let no_extension = path.with_extension("");
    let file = no_extension.file_name()
        .expect("Failed to retrieve filename for input file")
        .to_str()
        .expect("Invalid filename");

    match run(io, &src, reconstruct_ast, backend, file) {
        Ok(()) => {}
        Err(errors) => {
            println!("{} {} {}",
                "Finished with".red(),
                errors.error_count().to_string().underline().bright_red(),
                "errors".red()
            );
            errors.print(&src, file);
        }
    }
}

fn run<'a, R: std::io::BufRead, W: std::io::Write>(
    io: &mut (R, W),
    src: &str,
    reconstruct_ast: bool,
    backend: Backend,
    file_without_extension: &str
) -> Result<(), Errors> {
    let mut errors = Errors::new();
    let Some(tokens) = lexer::parse(&src, &mut errors)
        else { return Err(errors) };
    
        let count = errors.error_count();
        println!("... Lexing finished with {} error{}",
            if count > 0 {
                count.to_string().red()
            } else {
                count.to_string().green()
            },
            if count == 1 { "" } else { "s" }
        );

    let mut parser = Parser::new(tokens, &src);
    let mut module = match parser.parse() {
        Ok(module) => module,
        Err(err) => {
            errors.emit(err.err, err.start, err.end);
            return Err(errors);
        }
    };

    let count = errors.error_count();
    println!("... Parsing finished with {} error{}",
        if count > 0 {
            count.to_string().red()
        } else {
            count.to_string().green()
        },
        if count == 1 { "" } else { "s" }
    );

    log!("Module: {:#?}", module);
    

    if reconstruct_ast {
        println!("\nAST code reconstruction:\n");
        let mut ast_repr_ctx = ast::repr::ReprPrinter::new("  ");
        module.repr(&mut ast_repr_ctx);
        println!("\n---------- End of AST reconstruction ----------\n\n");
    }
    
    // Intrinsics are inserted into the module so the resolver can find them.
    // This is a workarround until imports are present and these functions
    // are no longer magic implemented in the interpreter
    ast::insert_intrinsics(&mut module);

    let ir = ir::reduce(&module, &mut errors);
    log!("... reduced! IR: \n----------\n{}", ir);

    if errors.has_errors() {
        return Err(errors);
    }

    let main = if let Some((ty, id)) = ir.symbols.get("main") {
        if *ty != ir::SymbolType::Func {
            errors.emit(Error::FunctionExpected, 0, 0);
            return Err(errors)
        }
        &ir.funcs[id.idx()]
    } else {
        errors.emit(Error::MissingMain, 0, 0);
        return Err(errors);
    };
    
    match backend {
        Backend::TreeWalkInterpreter => {
            let val = interpreter::eval_function(
                io,
                &mut Scope::from_module(&ir),
                main,
                &[]
            );

            let t = val.get_type().unwrap_or(ir::TypeRef::Primitive(types::Primitive::Unit));
            println!("{}{} of type {}", "\nSuccessfully ran and returned: ".green(), val.adapt_fmt(&ir), t);
        }
        #[cfg(feature = "llvm-backend")]
        Backend::LLVM(action) => unsafe {
            let context = llvm::core::LLVMContextCreate();
            let llvm_module = llvm_codegen::module(context, &ir);
            if action == LLVMAction::Build {
                let ret_val = llvm_codegen::backend::run_jit(llvm_module);
                println!("\nResult of main function: {ret_val}");
            } else {
                let obj_file = format!("{file_without_extension}.o");
                llvm_codegen::backend::emit_bitcode(None, llvm_module, &obj_file);
                link::link(&obj_file, file_without_extension);
                std::fs::remove_file(obj_file).expect("Failed to delete object file");
                if action == LLVMAction::Run {
                    Command::new(format!("./{file_without_extension}"))
                    .spawn()
                    .expect("Failed to run")
                    .wait()
                    .expect("Running process failed");
                }
            }
            llvm::core::LLVMContextDispose(context);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
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
        super::run_file(&mut(std::io::Cursor::new(Vec::<u8>::new()), std::io::Cursor::new(&mut output)), "eye/test.eye", true, crate::Backend::TreeWalkInterpreter);
        let string = String::from_utf8(output).unwrap();
        println!("{string}");
        assert_eq!(string, EXPECTED);

        let input = b"123\n";
        let mut output = Vec::new();
        super::run(
            &mut(std::io::Cursor::new(input), &mut output),
            "main ->: print(string(parse(read(\"Input number: \"))+i32(1)))",
            false,
            crate::Backend::TreeWalkInterpreter,
            "test"
        ).unwrap();
        println!("{:?}", String::from_utf8(output.clone()));
        assert_eq!(b"Input number: 124".as_slice(), output.as_slice());
    }
}
