#![feature(iter_intersperse, let_else, box_patterns, variant_count)]

mod ast;
mod error;
mod lexer;
mod parser;
mod types;
mod interpreter;
mod ir;
mod typecheck;

use crate::{parser::Parser, interpreter::Scope, error::Errors, ast::repr::Repr};
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
use colored::Colorize;
use log;

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let mut src_file = None;
    let mut reconstruct_ast = false;
    for arg in &args {
        match arg.as_str() {
            "-l" | "--log" => LOG.store(true, std::sync::atomic::Ordering::SeqCst),
            "-r" | "--reconstruct-ast" => reconstruct_ast = true,
            unknown if unknown.starts_with("-") => eprintln!("Unrecognized argument {unknown}"),
            positional => if src_file.is_none() {
                src_file = Some(positional)
            } else {
                panic!("Too many positional arguments")
            },
        }
    }

    let src_file = src_file.unwrap_or("./eye/test.eye");
    run_file(&mut (std::io::stdin().lock(), std::io::stdout()), src_file, reconstruct_ast);
}

fn run_file<R: std::io::BufRead, W: std::io::Write>(io: &mut (R, W), file: &str, reconstruct_ast: bool) {
    use colored::*;
    let src = std::fs::read_to_string(Path::new(&file))
        .expect(&format!("Could not open source file: {}", file));

    println!("{} {} ...", "Compiling".green(), file.underline().bright_blue());
    
    match run(io, &src, reconstruct_ast) {
        Ok((module, res)) => {
            let t = res.get_type().unwrap_or(ir::TypeRef::Primitive(types::Primitive::Unit));
            println!("{}{} of type {}", "\nSuccessfully ran and returned: ".green(), res.adapt_fmt(&module), t);
        }
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

fn run<'a, R: std::io::BufRead, W: std::io::Write>
(io: &mut (R, W), src: &str, reconstruct_ast: bool) -> Result<(ir::Module, interpreter::Value), Errors> {
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

    log!("Module: {:?}", module);
    

    if reconstruct_ast {
        println!("\nAST code reconstruction:\n");
        let mut ast_repr_ctx = ast::repr::ReprPrinter::new("  ");
        module.repr(&mut ast_repr_ctx);
        println!("\n---------- End of AST reconstruction ----------\n\n");
    }
    
    // HACK: intrinsics are inserted into the module so the resolver can find them
    interpreter::insert_intrinsics(&mut module);

    let ir = match typecheck::check(&module, &mut errors) {
        Ok(ir) => ir,
        Err(err) => {
            errors.emit(err.err, err.start, err.end);
            return Err(errors);
        }
    };

    log!("... reduced! TIR: {:?}", ir);

    if errors.has_errors() {
        return Err(errors);
    }
    
    let (ir::SymbolType::Func, main_key) = ir.symbols.get("main")
        .expect("No main symbol found")
        else { panic!("Main has to be a function, found type") };
    let main = &ir.funcs[main_key.idx()];

    let val = interpreter::eval_function(
        io,
        &mut Scope::from_module(&ir),
        main,
        &[]
    );

    Ok((ir, val))
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

// these lines before bye don't work without func type annotations:
//Printing from test()
//Calling return value from test()

        let mut output = Vec::new();
        super::run_file(&mut(std::io::Cursor::new(Vec::<u8>::new()), std::io::Cursor::new(&mut output)), "eye/test.eye", true);
        let string = String::from_utf8(output).unwrap();
        println!("{string}");
        assert_eq!(string, EXPECTED);

        let input = b"123\n";
        let mut output = Vec::new();
        super::run(&mut(std::io::Cursor::new(input), &mut output), "main ->: print(string(parse(read(\"Input number: \"))+i32(1)))", false).unwrap();
        println!("{:?}", String::from_utf8(output.clone()));
        assert_eq!(b"Input number: 124".as_slice(), output.as_slice());
    }
}