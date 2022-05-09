use std::path::{Path, PathBuf};
use crate::{
    log,
    ast::{self, Ast, ModuleId, Module, repr::Repr},
    error::{Error, Errors},
    lexer,
    parser::Parser
};

//TODO: proper dependencies / project handling
pub struct Dependency<'a> {
    _name: String,
    _path: &'a Path
}

pub fn project(module_path: &Path, reconstruct_src: bool, std: bool, _deps: &[Dependency], require_main_func: bool)
-> Result<crate::ir::Module, (Ast, Errors)> {
    let mut errors = Errors::new();
    let mut ast = Ast::new();

    let main = if module_path.is_dir() {
        tree(module_path, &mut ast, &mut errors, TreeType::Main, reconstruct_src)
    } else {
        file(module_path, &mut ast, &mut errors, reconstruct_src)
    };
    
    if let Some(std) = (std).then(std_path) {
        let std_mod = tree(&std, &mut ast, &mut errors, TreeType::Main, reconstruct_src);
        ast[main].definitions.insert(
            "std".to_owned(),
            ast::Definition::Module(std_mod)    
        );
    }
    match crate::ir::reduce(&ast, errors, require_main_func) {
        Ok((ir, _globals)) => Ok(ir),
        Err(err) => Err((ast, err))
    }
}

fn std_path() -> PathBuf {
    match std::env::current_exe()
        .ok()
        .and_then(|path| path.parent().map(|p| Path::join(p, "std"))) {
            Some(path) if std::fs::try_exists(&path).is_ok_and(|v| *v) => path,
            _ => "std".into()
        }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TreeType {
    Main,
    Mod
}
impl TreeType {
    fn file(self) -> &'static str {
        match self {
            Self::Main { .. } => "main.eye",
            Self::Mod => "mod.eye"
        }
    }
}

fn tree(
    path: &Path,
    modules: &mut Ast,
    errors: &mut Errors,
    t: TreeType,
    reconstruct_src: bool,
) -> ModuleId {
    let base_file = path.join(t.file());
    let base_exists = std::fs::try_exists(&base_file)
        .unwrap_or_else(|err| panic!("Failed to access file {base_file:?}: {err}"));
    let base_module = if base_exists {
        file(&base_file, modules, errors, reconstruct_src)
    } else {
        let main_mod = modules.add_module(Module::empty(), "".to_owned(), path.to_owned());
        if let TreeType::Main = t {
            errors.emit(Error::MissingMainFile, 0, 0, main_mod);
        }
        main_mod
    };

    for entry in std::fs::read_dir(path).expect("Failed to read directory") {
        let entry = entry.expect("Failed to read file");
        let path = entry.path();
        if entry.file_name() == t.file() { continue; }
        let file_ty = entry.file_type().expect("Failed to retrieve file type");
        let child_module = if file_ty.is_dir() {
            tree(&path, modules, errors, TreeType::Mod, reconstruct_src)
        } else if file_ty.is_file() {
            let is_eye = matches!(path.extension(), Some(extension) if extension == "eye");
            if !is_eye { continue; }
            file(&path, modules, errors, reconstruct_src)
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

fn file(
    path: &Path,
    ast: &mut Ast,
    errors: &mut Errors,
    reconstruct_src: bool,
) -> ModuleId {
    let src = match std::fs::read_to_string(path) {
        Ok(f) => f,
        Err(err) => panic!("Failed to read file {path:?}: {err}")
    };

    let module_id = ast.add_module(Module::empty(), String::new(), path.to_owned());

    let Some(tokens) = lexer::parse(&src, errors, module_id) else {
        ast.update(module_id, Module::empty(), src, path.to_owned());
        return module_id;
    };
    
    let mut parser = Parser::new(tokens, &src, ast, module_id);
    match parser.parse() {
        Ok(module) => {
            if reconstruct_src {
                log!("Module: {:#?}", module);
                println!("\n---------- Start of AST code reconstruction for file {path:?} ----------\n");
                let ast_repr_ctx = ast::repr::ReprPrinter::new("  ", &ast, &src);
                module.repr(&ast_repr_ctx);
                println!("------------ End of AST code reconstruction for file {path:?} ----------");
            }
            ast.update(module_id, module, src, path.to_owned());
        },
        Err(err) => {
            ast.update(module_id, Module::empty(), src, path.to_owned());
            errors.emit_err(err);
        }
    };
    
    crate::log!("Parsed file {:?}", path);

    module_id
}