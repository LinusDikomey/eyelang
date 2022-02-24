#![feature(iter_intersperse, let_else, box_patterns, variant_count)]

/*
use inkwell::OptimizationLevel;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use inkwell::module::Module;
use inkwell::targets::{InitializationConfig, Target};
use std::error::Error;
*/

mod ast;
mod codegen;
mod error;
mod lexer;
mod parser;
mod types;
mod typing;
mod verifier;
mod interpreter;
mod ir;

use crate::{ast::{Repr, ReprPrinter}, parser::Parser, typing::tir, interpreter::Scope, error::EyeResult};
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
            let t = res.get_type().unwrap_or(ast::UnresolvedType::Primitive(types::Primitive::Unit));
            println!("{}{} of type {}", "\nSuccessfully ran and returned: ".green(), res, t);
        }
        Err(err) => println!("{}{:?}", "Failed to run: ".red(), err)
    }
}

fn run_file(src_file: &str) -> EyeResult<interpreter::Value> {

    let src = std::fs::read_to_string(Path::new(&src_file))
        .expect(&format!("Could not open source file: {}", src_file));

    let tokens = lexer::TokenStream::from_source(&src)?;

    let mut parser = Parser::new(tokens.tokens);

    let mut module = parser.parse()?;
    log!("Module: {:?}", module);
    

    println!("\nAST code reconstruction:\n");
    let mut ast_repr_ctx = ReprPrinter::new("  ");
    module.repr(&mut ast_repr_ctx);
    println!("\n---------- End of AST reconstruction ----------\n\n");

    // HACK: intrinsics are inserted into the module so the resolver can find them
    interpreter::insert_intrinsics(&mut module);

    log!("\n\nReducing module to TIR...");

    let tir = typing::reduce(&module)?;

    //verifier::verify(&module)?;

    log!("... reduced! TIR: {:?}", tir);

    //let ctx = Context::create();
    //let main = codegen::generate_module(&module, &ctx)?;
    //let result = unsafe { main.call() };
    //println!("Result of main: {}", result);

    Ok(interpreter::eval_function(
        &mut Scope::from_module(tir.clone()),
        &tir.functions.get(&tir::SymbolKey::new("main".to_owned())).expect("Main not found"),
        vec![])
    )
}
