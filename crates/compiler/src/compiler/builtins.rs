use parser::ast::{FunctionId, ModuleId, TraitId};

use crate::{
    Compiler, ProjectId,
    compiler::ModuleSpan,
    types::BaseType,
    typing::{LocalTypeIds, TypeInfo},
};

use super::Def;

#[derive(Default)]
pub struct Builtins {
    pub std: ProjectId,
    pub primitives: Primitives,
    str_type: Option<BaseType>,
    str_eq: Option<(ModuleId, FunctionId)>,
    prelude: Option<ModuleId>,
    panic: Option<(ModuleId, FunctionId)>,
    intrinsic: Option<(ModuleId, FunctionId)>,
    iterator: Option<(ModuleId, TraitId)>,
    option: Option<BaseType>,
    fn_trait: Option<(ModuleId, TraitId)>,
}
impl Builtins {
    pub fn set_std(&mut self, std: ProjectId) {
        self.std = std;
    }
}

pub struct Primitives {
    pub bool: BaseType,
}
impl Primitives {
    pub fn bool_info(&self) -> TypeInfo {
        TypeInfo::Instance(self.bool, LocalTypeIds::EMPTY)
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
            bool: BaseType::MISSING,
        }
    }
}

fn resolve_module(compiler: &mut Compiler, module: ModuleId, name: &str) -> ModuleId {
    let def = compiler.resolve_in_module(module, name, ModuleSpan::MISSING);
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
) -> BaseType {
    let def = compiler.resolve_in_module(module, name, ModuleSpan::MISSING);
    let Def::BaseType(base) = def else {
        panic!("Missing builtin type {name}, found {def:?}");
    };
    assert_eq!(
        generic_count,
        compiler.get_resolved_type_generic_count(base),
        "Compiler-builtin type {name} has unexpected generic count",
    );
    base
}

pub fn get_str(compiler: &mut Compiler) -> BaseType {
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
    let Def::BaseType(str_type) =
        compiler.resolve_in_module(string_module, "str", ModuleSpan::MISSING)
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
        let prelude = compiler.resolve_in_module(root, "prelude", ModuleSpan::MISSING);
        tracing::debug!("NOCHECKIN Resolving prelude: {std:?} {root:?} {prelude:?}");
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
    let def = compiler.resolve_in_module(root, "panic", ModuleSpan::MISSING);
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
    let def = compiler.resolve_in_module(root, "intrinsics", ModuleSpan::MISSING);
    let Def::Module(intrinsics_module) = def else {
        panic!("expected a module for std.intrinsics but found {def:?}")
    };
    let def = compiler.resolve_in_module(intrinsics_module, "intrinsic", ModuleSpan::MISSING);
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
    let def = compiler.resolve_in_module(root, "iter", ModuleSpan::MISSING);
    let Def::Module(iter_module) = def else {
        panic!("expected a module for std.iter but found {def:?}");
    };
    let def = compiler.resolve_in_module(iter_module, "Iterator", ModuleSpan::MISSING);
    let Def::Trait(module, id) = def else {
        panic!("expected a trait for std.iter.Iterator but found {def:?}");
    };
    compiler.builtins.iterator = Some((module, id));
    (module, id)
}

pub fn get_option(compiler: &mut Compiler) -> BaseType {
    if let Some(option) = compiler.builtins.option {
        return option;
    }
    let std = compiler.builtins.std;
    let root = compiler.get_project(std).root_module;
    let def = compiler.resolve_in_module(root, "option", ModuleSpan::MISSING);
    let Def::Module(option_module) = def else {
        panic!("expected a module for std.option but found {def:?}");
    };
    let def = compiler.resolve_in_module(option_module, "Option", ModuleSpan::MISSING);
    let Def::BaseType(id) = def else {
        panic!("expected a type for std.option.Option but found {def:?}");
    };
    debug_assert_eq!(compiler.get_resolved_type_generic_count(id), 1);
    compiler.builtins.option = Some(id);
    id
}

pub fn get_fn_trait(compiler: &mut Compiler) -> (ModuleId, TraitId) {
    if let Some(fn_trait) = compiler.builtins.fn_trait {
        return fn_trait;
    }
    let std = compiler.builtins.std;
    let root = compiler.get_project(std).root_module;
    let fn_module = resolve_module(compiler, root, "call");
    let Def::Trait(module, t) = compiler.resolve_in_module(fn_module, "Fn", ModuleSpan::MISSING)
    else {
        panic!("expected a trait for std.call.Fn");
    };
    compiler.builtins.fn_trait = Some((module, t));
    (module, t)
}
