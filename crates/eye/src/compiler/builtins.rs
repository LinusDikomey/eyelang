use id::{ModuleId, ProjectId, TypeId};
use span::Span;
use types::Type;

use crate::{parser::ast::FunctionId, Compiler};

use super::Def;

#[derive(Default)]
pub struct Builtins {
    pub std: ProjectId,
    str_type: Option<TypeId>,
    str_eq: Option<(ModuleId, FunctionId)>,
    prelude: Option<ModuleId>,
    panic: Option<(ModuleId, FunctionId)>,
}
impl Builtins {
    pub fn set_std(&mut self, std: ProjectId) {
        self.std = std;
    }
}

pub fn get_str(compiler: &mut Compiler) -> TypeId {
    if let Some(str_type) = compiler.builtins.str_type {
        return str_type;
    }
    let string_module = get_string_module(compiler);
    let str = compiler.resolve_in_module(string_module, "str", Span::MISSING);
    let Def::Type(Type::DefId {
        id: str_type,
        generics: None,
    }) = str
    else {
        panic!("expected a type definition for builtin std.string.str, found {str:?}");
    };
    compiler.builtins.str_type = Some(str_type);
    str_type
}

fn get_string_module(compiler: &mut Compiler) -> ModuleId {
    let std = compiler.builtins.std;
    let root = compiler.get_project(std).root_module;
    let string = compiler.resolve_in_module(root, "string", Span::MISSING);
    let Def::Module(string_module) = string else {
        panic!("expected a module for builtin std.string, found {string:?}");
    };
    string_module
}

pub fn get_str_eq(compiler: &mut Compiler) -> (ModuleId, FunctionId) {
    if let Some(str_eq) = compiler.builtins.str_eq {
        return str_eq;
    }
    let string_module = get_string_module(compiler);
    let Def::Type(Type::DefId {
        id: str_type,
        generics: None,
    }) = compiler.resolve_in_module(string_module, "str", Span::MISSING)
    else {
        panic!("missing std.string.str");
    };
    let Some(&str_eq) = compiler.get_resolved_type_def(str_type).methods.get("eq") else {
        panic!("missing std.str.eq method");
    };
    let str_eq = (string_module, str_eq);
    compiler.builtins.str_eq = Some(str_eq);
    str_eq
}

pub fn get_prelude(compiler: &mut Compiler) -> Option<ModuleId> {
    if let Some(module) = compiler.builtins.prelude {
        return Some(module);
    }
    let std = compiler.builtins.std;
    (std != ProjectId::MISSING).then(|| {
        let root = compiler.get_project(std).root_module;
        let prelude = compiler.resolve_in_module(root, "prelude", Span::MISSING);
        let Def::Module(prelude) = prelude else {
            panic!("expected a module for std.prelude, found {prelude:?}");
        };
        compiler.builtins.prelude = Some(prelude);
        prelude
    })
}

pub fn get_panic(compiler: &mut Compiler) -> (ModuleId, FunctionId) {
    if let Some(panic) = compiler.builtins.panic {
        return panic;
    }

    let std = compiler.builtins.std;
    let root = compiler.get_project(std).root_module;
    let def = compiler.resolve_in_module(root, "panic", Span::MISSING);
    let Def::Function(panic_mod, panic_func) = def else {
        panic!("expected a function for std.panic, found {def:?}")
    };
    compiler.builtins.panic = Some((panic_mod, panic_func));
    (panic_mod, panic_func)
}
