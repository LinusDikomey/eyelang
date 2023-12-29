#![deny(unused_must_use)]

mod compiler;
mod error;
mod eval;
mod parser;
mod type_table;

pub use compiler::Compiler;
use span::Span;

use compiler::Def;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut compiler = compiler::Compiler::new();
    let project = compiler.add_project("test-project".to_owned(), "test-project.eye".into())?;
    let std = compiler.add_project("std".to_owned(), "std".into())?;
    compiler.add_dependency(project, std);
    compiler.check_complete_project(project);

    // debug print ast
    /*
    let root = compiler.get_project(project).root_module;
    let ast = compiler.get_module_ast(root);
    println!("Main module ast:");
    parser::ast::repr::ReprPrinter::new("  ", ast).print_module();
    println!("end of ast");
    */

    let root_module = compiler.get_project(project).root_module;
    let main_def = compiler.resolve_in_module(root_module, "main", Span::MISSING);
    match main_def {
        Def::Function(module, main_id) => {
            let checked = compiler.get_checked_function(module, main_id);
            // TODO: compile main
            eprintln!("Checked main function: {checked:?}");
        }
        _ => eprintln!("main should be a function, is {main_def:?}"),
    }

    compiler.print_errors();

    let Def::Global(module, id) = compiler.resolve_in_module(root_module, "my_global", Span::MISSING) else { panic!() };
    dbg!(compiler.get_checked_global(module, id));
    Ok(())
}
