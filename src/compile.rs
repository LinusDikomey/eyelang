use std::path::Path;
use crate::{log, ast::{self, Modules, ModuleId, Module, repr::Repr}, error::{Error, Errors}, lexer, parser::Parser, Args};

pub fn path(path: &Path, args: &Args, std: Option<&Path>) -> (Modules, ModuleId, Errors) {
    let mut errors = Errors::new();
    let mut modules = Modules::new();

    let main = if path.is_dir() {
        tree(path, &mut modules, &mut errors, TreeType::Main, args)
    } else {
        file(path, &mut modules, &mut errors, args)
    };
    if let Some(std) = std {
        let std_mod = tree(std, &mut modules, &mut errors, TreeType::Main, args);
        modules[main].definitions.insert(
            "std".to_owned(),
            ast::Definition::Module(std_mod)    
        );
    }
    (modules, main, errors)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TreeType {
    Main,
    Mod
}
impl TreeType {
    fn file(&self) -> &'static str {
        match self {
            Self::Main => "main.eye",
            Self::Mod => "mod.eye"
        }
    }
}

fn tree(
    path: &Path,
    modules: &mut Modules,
    errors: &mut Errors,
    t: TreeType,
    args: &Args
) -> ModuleId {
    let base_file = path.join(t.file());
    let base_exists = std::fs::try_exists(&base_file)
        .unwrap_or_else(|err| panic!("Failed to access file {base_file:?}: {err}"));
    let base_module = if !base_exists {
        let main_mod = modules.add(Module::empty(), "".to_owned(), path.to_owned());
        if t == TreeType::Main {
            errors.emit(Error::MissingMainFile, 0, 0, main_mod);
        }
        main_mod
    } else {
        file(&base_file, modules, errors, args)
    };

    for entry in std::fs::read_dir(path).expect("Failed to read directory") {
        let entry = entry.expect("Failed to read file");
        let path = entry.path();
        if entry.file_name() == t.file() { continue; }
        let file_ty = entry.file_type().expect("Failed to retrieve file type");
        let child_module = if file_ty.is_dir() {
            tree(&path, modules, errors, TreeType::Mod, args)
        } else if file_ty.is_file() {
            let is_eye = match path.extension() {
                Some(extension) if extension == "eye" => true,
                _ => false
            };
            if !is_eye { continue; }
            file(&path, modules, errors, args)
        } else {
            eprintln!("Invalid file type found in module tree");
            continue;
        };

        modules[base_module].definitions.insert(
            path.with_extension("").file_name().unwrap().to_string_lossy().into_owned(),
            ast::Definition::Module(child_module)
        );
    }
    base_module
}

fn file(path: &Path, modules: &mut Modules, errors: &mut Errors, args: &Args) -> ModuleId {
    let src = match std::fs::read_to_string(path) {
        Ok(f) => f,
        Err(err) => panic!("Failed to read file {path:?}: {err}")
    };

    let module_id = modules.add(Module::empty(), String::new(), path.to_owned());

    let Some(tokens) = lexer::parse(&src, errors, module_id) else {
        modules.update(module_id, Module::empty(), src, path.to_owned());
        return module_id;
    };
    
    let mut parser = Parser::new(tokens, &src, module_id);
    match parser.parse() {
        Ok(module) => {
            if args.reconstruct_src {
                log!("Module: {:#?}", module);
                println!("\n---------- Start of AST code reconstruction for file {path:?} ----------\n");
                let mut ast_repr_ctx = ast::repr::ReprPrinter::new("  ");
                module.repr(&mut ast_repr_ctx);
                println!("------------ End of AST code reconstruction for file {path:?} ----------");
            }
            modules.update(module_id, module, src, path.to_owned());
        },
        Err(err) => {
            modules.update(module_id, Module::empty(), src, path.to_owned());
            errors.emit(err.err, err.span.start, err.span.end, module_id);
        }
    };
    
    // Intrinsics are inserted into the module so the resolver can find them.
    // This is a workarround until imports are present and these functions
    // are no longer magic implemented in the interpreter

    crate::log!("Parsed file {:?}", path);

    module_id
}