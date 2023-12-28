#![feature(array_chunks)]
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

    let root = compiler.get_project(project).root_module;
    let main_def = compiler.resolve_in_module(root, "main", Span::MISSING);
    match main_def {
        Def::Function(module, main_id) => {
            let checked = compiler.get_checked_function(module, main_id);
            eprintln!("Checked main function: {checked:?}");
        }
        _ => eprintln!("main should be a function, is {main_def:?}"),
    }
    let ast = compiler.get_module_ast(root);
    println!("Main module ast:");
    parser::ast::repr::ReprPrinter::new("  ", ast).print_module();
    println!("end of ast");
    //let main = &compiler.modules[root.idx()][main_id.idx()];
    //let body = main.ast.body.as_ref().unwrap().clone();
    //print!("Main function {main:?} returned ");
    //let main_result = eval::def_expr(body.root(), body, root, &mut compiler);
    //main_result.dump(&mut compiler);

    compiler.print_errors();
    /*
    let Type::DefId { id: vec2, generics } = compiler.resolve_type(&UnresolvedType::Path(vec!["Vec2".to_owned()]), root) else { panic!() };
    assert!(generics.is_empty());
    dbg!(&compiler.type_defs[vec2.idx()]);
    let resolved_vec2 = compiler.get_resolved_type_def(vec2);
    dbg!(&compiler.types[resolved_vec2.idx()]);
    */
    Ok(())
}
