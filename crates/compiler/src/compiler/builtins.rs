use id::{ModuleId, TypeId};
use span::Span;
use types::Type;

use crate::{
    Compiler, ProjectId,
    parser::ast::{FunctionId, TraitId},
    types::{LocalTypeIds, TypeInfo},
};

use super::Def;

#[derive(Default)]
pub struct Builtins {
    pub std: ProjectId,
    pub primitives: Primitives,
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

pub struct Primitives {
    pub bool: TypeId,
}
impl Primitives {
    pub fn bool_info(&self) -> TypeInfo {
        TypeInfo::TypeDef(self.bool, LocalTypeIds::EMPTY)
    }

    pub fn resolve(compiler: &mut Compiler) -> Primitives {
        let std = compiler.get_project(compiler.builtins.std).root_module;
        let primitive = resolve_module(compiler, std, "primitive");
        Self {
            bool: resolve_type(compiler, primitive, "bool", 0),
        }
    }
}
impl Default for Primitives {
    fn default() -> Self {
        Self {
            bool: TypeId::MISSING,
        }
    }
}

fn resolve_module(compiler: &mut Compiler, module: ModuleId, name: &str) -> ModuleId {
    let def = compiler.resolve_in_module(module, name, Span::MISSING);
    let Def::Module(id) = def else {
        panic!("Missing builtin module {name}, found {def:?}");
    };
    id
}

fn resolve_type(
    compiler: &mut Compiler,
    module: ModuleId,
    name: &str,
    generic_count: u8,
) -> TypeId {
    let def = compiler.resolve_in_module(module, name, Span::MISSING);
    let Def::Type(ty) = def else {
        panic!("Missing builtin type {name}, found {def:?}");
    };
    let Type::DefId { id, generics } = ty else {
        panic!(
            "Builtin type {name} has unexpected definition, expected a type def with {generic_count} generics but found {ty:?}"
        );
    };
    if generics.len() != generic_count as usize {
        panic!(
            "Builtin type {name} has unexpected generic count, expected {generic_count} but found {}",
            generics.len()
        );
    }
    id
}

pub fn get_str(compiler: &mut Compiler) -> TypeId {
    if let Some(str_type) = compiler.builtins.str_type {
        return str_type;
    }
    let string_module = get_string_module(compiler);
    let str_type = resolve_type(compiler, string_module, "str", 0);
    compiler.builtins.str_type = Some(str_type);
    str_type
}

fn get_string_module(compiler: &mut Compiler) -> ModuleId {
    let std = compiler.builtins.std;
    let root = compiler.get_project(std).root_module;
    resolve_module(compiler, root, "string")
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
