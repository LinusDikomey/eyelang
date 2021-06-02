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
    
    println!("Verifying module...");

    verifier::verify(&module)?;

    println!("... verified!");

    /*
    let ctx = Context::create();
    let main = codegen::generate_module(&module, &ctx)?;
    let result = unsafe { main.call() };
    println!("Result of main: {}", result);
    */
    Ok(())
}

/*
/// Convenience type alias for the `sum` function.
///
/// Calling this is innately `unsafe` because there's no guarantee it doesn't
/// do `unsafe` operations internally.
type SumFunc = unsafe extern "C" fn(u64, u64, u64) -> u64;

struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    execution_engine: ExecutionEngine<'ctx>,
}

impl<'ctx> CodeGen<'ctx> {
    fn jit_compile_sum(&self) -> Option<JitFunction<SumFunc>> {
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
        let function = self.module.add_function("sum", fn_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");

        self.builder.position_at_end(basic_block);

        let x = function.get_nth_param(0)?.into_int_value();
        let y = function.get_nth_param(1)?.into_int_value();
        let z = function.get_nth_param(2)?.into_int_value();

        let sum = self.builder.build_int_add(x, y, "sum");
        let sum = self.builder.build_int_add(sum, z, "sum");

        let two = self.context.i64_type().const_int(2, false);
        let sum = self.builder.build_int_mul(sum, two, "sum");
        self.builder.build_return(Some(&sum));

        unsafe { self.execution_engine.get_function("sum").ok() }
    }
}


fn main() -> Result<(), Box<dyn Error>> {
    let context = Context::create();
    let module = context.create_module("sum");
    let execution_engine = module.create_jit_execution_engine(OptimizationLevel::None)?;
    let codegen = CodeGen {
        context: &context,
        module,
        builder: context.create_builder(),
        execution_engine,
    };

    let sum = codegen.jit_compile_sum().ok_or("Unable to JIT compile `sum`")?;

    let x = 1u64;
    let y = 2u64;
    let z = 3u64;

    unsafe {
        println!("2 * ({} + {} + {}) = {}", x, y, z, sum.call(x, y, z));
        assert_eq!(sum.call(x, y, z), 2 * (x + y + z));
    }

    Ok(())
}*/