/*
use inkwell::OptimizationLevel;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use inkwell::module::Module;
use inkwell::targets::{InitializationConfig, Target};
use std::error::Error;
*/


mod lexer;
mod error;
mod types;
mod parser;
mod ast;
mod codegen;
mod verifier;
mod typing;

use std::path::Path;
use error::EyeError;
use crate::parser::Parser;

fn main() -> Result<(), EyeError> {

    let src_file = "./eye/test.eye";
    let src = std::fs::read_to_string(Path::new(src_file)).expect(&format!("Could not open source file: {}", src_file));

    let tokens = lexer::TokenStream::from_source(&src)?;

    let mut parser = Parser::new(tokens.tokens);

    let module = parser.parse()?;
    println!("Module: {:?}", module);
    
    println!("Reducing module to EIR...");

    let eir = typing::reduce(&module);

    //verifier::verify(&module)?;

    println!("... reduced: {:?}", eir);

    
    //let ctx = Context::create();
    //let main = codegen::generate_module(&module, &ctx)?;
    //let result = unsafe { main.call() };
    //println!("Result of main: {}", result);
    
    Ok(())
}