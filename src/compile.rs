use std::{path::{Path, PathBuf}, time::{Instant, Duration}};
use crate::{
    log,
    ast::{self, Ast, ModuleId, Module, repr::Repr},
    error::{Error, Errors},
    lexer,
    parser::Parser, Stats
};

//TODO: proper dependencies / project handling
pub struct Dependency<'a> {
    _name: String,
    _path: &'a Path
}

#[derive(Clone, Copy, Default)]
pub struct Debug {
    pub tokens: bool,
    pub reconstruct_src: bool,
}

pub fn project(
    module_path: &Path,
    debug: Debug,
    std: bool,
    _deps: &[Dependency],
    require_main_func: bool,
    stats: &mut Stats
) -> (Result<crate::ir::Module, ()>, Ast, Errors) {
    let mut errors = Errors::new();
    let mut ast = Ast::new();

    let main_module = ast.add_empty_root_module(module_path.to_owned());

    if module_path.is_dir() {
        tree(module_path, &mut ast, &mut errors, main_module, main_module, TreeType::Main, debug, stats);
    } else {
        file(module_path, &mut ast, &mut errors, main_module, main_module, debug, stats);
    };
    
    if let Some(std) = (std).then(std_path) {
        let std_mod = ast.add_empty_root_module(std.to_owned());
        tree(&std, &mut ast, &mut errors, std_mod, std_mod, TreeType::Main, debug, stats);
        let defs = ast[main_module].definitions;
        ast[defs].insert(
            "std".to_owned(),
            ast::Definition::Module(std_mod)    
        );
    }
    let reduce_start_time = Instant::now();
    let (reduce_res, errors) = crate::ir::reduce(&ast, main_module, errors, require_main_func);
    stats.irgen += reduce_start_time.elapsed();
    (match reduce_res {
        Ok((ir, _globals)) => Ok(ir),
        Err(()) => Err(())
    }, ast, errors)
}

fn std_path() -> PathBuf {
    match std::env::current_exe()
        .ok()
        .and_then(|path| path.parent().map(|p| Path::join(p, "std"))) {
            Some(path) => match std::fs::try_exists(&path) {
                Ok(true) => path,
                _ => "std".into()
            }
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
    ast: &mut Ast,
    errors: &mut Errors,
    root_module: ModuleId,
    dir_module: ModuleId,
    t: TreeType,
    debug: Debug,
    stats: &mut Stats,
) {
    let base_file = path.join(t.file());
    let base_exists = std::fs::try_exists(&base_file)
        .unwrap_or_else(|err| panic!("Failed to access file {base_file:?}: {err}"));
    if base_exists {
        file(&base_file, ast, errors, root_module, dir_module, debug, stats);
    } else {
        if let TreeType::Main = t {
            errors.emit(Error::MissingMainFile, 0, 0, dir_module);
        }
    };

    for entry in std::fs::read_dir(path).expect("Failed to read directory") {
        let entry = entry.expect("Failed to read file");
        let path = entry.path();
        if entry.file_name() == t.file() { continue; }
        let file_ty = entry.file_type().expect("Failed to retrieve file type");
        let child_module = ast.add_empty_module(entry.path(), root_module);
        if file_ty.is_dir() {
            tree(&path, ast, errors, root_module, child_module, TreeType::Mod, debug, stats);
        } else if file_ty.is_file() {
            let is_eye = matches!(path.extension(), Some(extension) if extension == "eye");
            if !is_eye { continue; }
            file(&path, ast, errors, root_module, child_module, debug, stats);
        } else {
            eprintln!("Invalid file type found in module tree");
            continue;
        };

        let defs = ast[dir_module].definitions;
        ast[defs].insert(
            path.with_extension("").file_name().unwrap().to_string_lossy().into_owned(),
            ast::Definition::Module(child_module)
        );
    }
}

fn file(
    path: &Path,
    ast: &mut Ast,
    errors: &mut Errors,
    root_module: ModuleId,
    module_id: ModuleId,
    debug: Debug,
    stats: &mut Stats,
) {
    stats.file_times.push(crate::FileStats {
        name: path.to_string_lossy().into_owned(),
        lex: Duration::ZERO,
        parse: Duration::ZERO,
    });
    let file_stats = stats.file_times.last_mut().unwrap();
    
    let lex_start_time = Instant::now();
    let src = match std::fs::read_to_string(path) {
        Ok(f) => f,
        Err(err) => panic!("Failed to read file {path:?}: {err}")
    };

    let lex_res = lexer::parse(&src, errors, module_id);
    if debug.tokens {
        println!("Tokens at path {:?}:\n{:#?}", path, lex_res);
    }
    file_stats.lex = lex_start_time.elapsed();
    let Some(tokens) = lex_res else {
        let empty = Module::empty(ast, root_module);
        ast.update(module_id, empty, src, path.to_owned());
        return;
    };
    
    let parse_start_time = Instant::now();
    let mut parser = Parser::new(tokens, &src, ast, module_id);
    let parse_res = parser.parse(root_module);
    file_stats.parse = parse_start_time.elapsed();
    
    match parse_res {
        Ok(module) => {
            if debug.reconstruct_src {
                log!("Module: {:#?}", module);
                println!("\n---------- Start of AST code reconstruction for file {path:?} ----------\n");
                let ast_repr_ctx = ast::repr::ReprPrinter::new("  ", ast, &src);
                module.repr(&ast_repr_ctx);
                println!("------------ End of AST code reconstruction for file {path:?} ----------");
            }
            ast.update(module_id, module, src, path.to_owned());
        },
        Err(err) => {
            let empty = Module::empty(ast, root_module);
            ast.update(module_id, empty, src, path.to_owned());
            errors.emit_err(err);
        }
    };
    
    crate::log!("Parsed file {:?}", path);
}