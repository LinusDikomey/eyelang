#![deny(unused_must_use)]

mod check;
mod compiler;
mod error;
mod eval;
mod hir;
mod irgen;
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

    let root_module = compiler.get_project(project).root_module;
    let dump_ast = true;
    if dump_ast {
        let ast = compiler.get_module_ast(root_module);
        parser::ast::repr::ReprPrinter::new("  ", ast).print_module();
    }
    let main_def = compiler.resolve_in_module(root_module, "main", Span::MISSING);
    match main_def {
        Def::Function(module, main_id) => {
            let checked = compiler.get_hir(module, main_id);
            // TODO: compile main
            eprintln!("Checked main function: {checked:?}");
            let main_ir = compiler.get_ir_function_id(root_module, main_id, &[]);
            let display = compiler.ir_functions[main_ir.0 as usize].display(ir::display::Info { funcs: &compiler.ir_functions });
            println!("displaying ir: {display}");
        }
        _ => eprintln!("main should be a function, is {main_def:?}"),
    }

    compiler.print_errors();
    Ok(())
}
