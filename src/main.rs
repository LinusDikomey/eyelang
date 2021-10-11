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

use crate::{ast::{Repr, ReprCtx}, parser::Parser};
use error::EyeError;
use std::path::Path;

fn main() -> Result<(), EyeError> {
    let src_file = "./eye/test.eye";
    let src = std::fs::read_to_string(Path::new(src_file))
        .expect(&format!("Could not open source file: {}", src_file));

    let tokens = lexer::TokenStream::from_source(&src)?;

    let mut parser = Parser::new(tokens.tokens);

    let module = parser.parse()?;
    println!("Module: {:?}", module);

    println!("\nAST code reconstruction:\n");
    let mut ast_repr_ctx = ReprCtx::new("  ");
    module.repr(&mut ast_repr_ctx);
    
    println!("\n\nReducing module to TIR...");

    let tir = typing::reduce(&module)?;

    for (name, ty) in &tir.types {
        println!("Type {} has a size of {} bytes", name.name(), match ty {
            typing::tir::Type::Struct(s) => s.size(&tir)
        })
    }

    //verifier::verify(&module)?;

    println!("... reduced! TIR: {:?}", tir);

    //let ctx = Context::create();
    //let main = codegen::generate_module(&module, &ctx)?;
    //let result = unsafe { main.call() };
    //println!("Result of main: {}", result);

    Ok(())
}
