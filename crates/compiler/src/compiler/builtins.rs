use id::{ModuleId, TypeId};
use span::Span;
use types::Type;

use crate::{
    Compiler, ProjectId,
    parser::ast::{FunctionId, TraitId},
};

use super::Def;

#[derive(Default)]
pub struct Builtins {
    pub std: ProjectId,
    str_type: Option<TypeId>,
    str_eq: Option<(ModuleId, FunctionId)>,
    prelude: Option<ModuleId>,
    panic: Option<(ModuleId, FunctionId)>,
    intrinsic: Option<(ModuleId, FunctionId)>,
    iterator: Option<(ModuleId, TraitId)>,
    option: Option<TypeId>,
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
        generics,
    }) = str
    else {
        panic!("expected a type definition for builtin std.string.str, found {str:?}");
    };
    assert!(
        generics.is_empty(),
        "std.string.str shouldn't have generics"
    );
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
        generics: _,
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

pub fn get_intrinsic(compiler: &mut Compiler) -> (ModuleId, FunctionId) {
    if let Some(intrinsic) = compiler.builtins.intrinsic {
        return intrinsic;
    }
    let std = compiler.builtins.std;
    let root = compiler.get_project(std).root_module;
    let def = compiler.resolve_in_module(root, "intrinsics", Span::MISSING);
    let Def::Module(intrinsics_module) = def else {
        panic!("expected a module for std.intrinsics but found {def:?}")
    };
    let def = compiler.resolve_in_module(intrinsics_module, "intrinsic", Span::MISSING);
    let Def::Function(module, id) = def else {
        panic!("expected a module for std.intrinsics but found {def:?}")
    };
    compiler.builtins.intrinsic = Some((module, id));
    (module, id)
}

pub fn get_iterator(compiler: &mut Compiler) -> (ModuleId, TraitId) {
    if let Some(iterator) = compiler.builtins.iterator {
        return iterator;
    }
    let std = compiler.builtins.std;
    let root = compiler.get_project(std).root_module;
    let def = compiler.resolve_in_module(root, "iter", Span::MISSING);
    let Def::Module(iter_module) = def else {
        panic!("expected a module for std.iter but found {def:?}");
    };
    let def = compiler.resolve_in_module(iter_module, "Iterator", Span::MISSING);
    let Def::Trait(module, id) = def else {
        panic!("expected a trait for std.iter.Iterator but found {def:?}");
    };
    compiler.builtins.iterator = Some((module, id));
    (module, id)
}

pub fn get_option(compiler: &mut Compiler) -> TypeId {
    if let Some(option) = compiler.builtins.option {
        return option;
    }
    let std = compiler.builtins.std;
    let root = compiler.get_project(std).root_module;
    let def = compiler.resolve_in_module(root, "option", Span::MISSING);
    let Def::Module(option_module) = def else {
        panic!("expected a module for std.option but found {def:?}");
    };
    let def = compiler.resolve_in_module(option_module, "Option", Span::MISSING);
    let Def::GenericType(id) = def else {
        panic!("expected a type for std.option.Option but found {def:?}");
    };
    debug_assert_eq!(compiler.types[id.idx()].generic_count, 1);
    compiler.builtins.option = Some(id);
    id
}
