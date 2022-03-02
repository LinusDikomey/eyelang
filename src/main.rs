#![feature(iter_intersperse, let_else, box_patterns, variant_count)]

mod ast;
mod error;
mod lexer;
mod parser;
mod types;
mod interpreter;
mod ir;
mod irgen;

use crate::{parser::Parser, interpreter::Scope, error::EyeResult, ast::repr::Repr};
use std::{path::Path, sync::atomic::AtomicBool};

static LOG: AtomicBool = AtomicBool::new(false);

macro_rules! log {
    () => {
        if $crate::LOG.load(std::sync::atomic::Ordering::Relaxed) { println!() }
    };
    ($s: expr $(,$arg: expr)*) => {
        if $crate::LOG.load(std::sync::atomic::Ordering::Relaxed) { println!($s, $($arg),*) }
    }
}
use log;

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let mut src_file = None;
    for arg in &args {
        match arg.as_str() {
            "-l" | "--log" => LOG.store(true, std::sync::atomic::Ordering::SeqCst),
            unknown if unknown.starts_with("-") => eprintln!("Unrecognized argument {unknown}"),
            positional => if src_file.is_none() {
                src_file = Some(positional)
            } else {
                panic!("Too many positional arguments")
            },
        }
    }

    let src_file = src_file.unwrap_or("./eye/test.eye");

    use colored::*;
    match run_file(&src_file) {
        Ok(res) => {
            let t = res.get_type().unwrap_or(ir::TypeRef::Primitive(types::Primitive::Unit));
            println!("{}{} of type {}", "\nSuccessfully ran and returned: ".green(), res, t);
        }
        Err(err) => println!("{}{:?}", "Failed to run: ".red(), err)
    }
}

fn run_file(src_file: &str) -> EyeResult<interpreter::Value> {

    let src = std::fs::read_to_string(Path::new(&src_file))
        .expect(&format!("Could not open source file: {}", src_file));

    let tokens = lexer::parse(&src)?;

    let mut parser = Parser::new(tokens, &src);
    let mut module = parser.parse()?;
    log!("Module: {:?}", module);
    

    println!("\nAST code reconstruction:\n");
    let mut ast_repr_ctx = ast::repr::ReprPrinter::new("  ");
    module.repr(&mut ast_repr_ctx);
    println!("\n---------- End of AST reconstruction ----------\n\n");

    // HACK: intrinsics are inserted into the module so the resolver can find them
    interpreter::insert_intrinsics(&mut module);

    log!("\n\nReducing module to TIR...");

    let ir = irgen::reduce(&module)?;

    //verifier::verify(&module)?;

    log!("... reduced! TIR: {:?}", ir);

    //let ctx = Context::create();
    //let main = codegen::generate_module(&module, &ctx)?;
    //let result = unsafe { main.call() };
    //println!("Result of main: {}", result);

    let (ir::SymbolType::Func, main_key) = ir.symbols.get("main")
        .expect("No main symbol found")
        else { panic!("Main has to be a function, found type") };
    let main = &ir.funcs[main_key.idx()];

    Ok(interpreter::eval_function(
        &mut Scope::from_module(ir.clone()),
        main,
        vec![])
    )
}
