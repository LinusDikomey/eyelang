#![feature(iter_intersperse, let_else)]

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

use crate::{ast::{Repr, ReprCtx}, parser::Parser, typing::tir, interpreter::Scope, error::EyeResult};
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
    let src_file = std::env::args().skip(1).next().or(Some("./eye/test.eye".to_owned())).unwrap();
    use colored::*;
    match run_file(&src_file) {
        Ok(res) => println!("{}{}", "Successfully ran and returned ".green(), res),
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

    // HACK: intrinsics are inserted into the module so the resolver can find them
    interpreter::insert_intrinsics(&mut module);
    

    log!("\nAST code reconstruction:\n");
    let mut ast_repr_ctx = ReprCtx::new("  ");
    module.repr(&mut ast_repr_ctx);
    
    log!("\n\nReducing module to TIR...");

    let tir = typing::reduce(&module)?;

    for (name, ty) in &tir.types {
        log!("Type {} has a size of {} bytes", name.name(), match ty {
            typing::tir::Type::Struct(s) => s.size(&tir)
        })
    }

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
