use std::cell::OnceCell;

use parser::ast::{FunctionId, ModuleId, TraitId};

use crate::{Compiler, ProjectId, Type, compiler::ModuleSpan, types::BaseType, typing::TypeInfo};

use super::Def;

#[derive(Default)]
pub struct Builtins {
    pub std: ProjectId,
    pub primitives: Primitives,
    str_type: OnceCell<Type>,
    str_eq: OnceCell<(ModuleId, FunctionId)>,
    prelude: OnceCell<ModuleId>,
    panic: OnceCell<(ModuleId, FunctionId)>,
    intrinsic: OnceCell<(ModuleId, FunctionId)>,
    iterator: OnceCell<(ModuleId, TraitId)>,
    option: OnceCell<BaseType>,
    fn_trait: OnceCell<(ModuleId, TraitId)>,
}
impl Builtins {
    pub fn set_std(&mut self, std: ProjectId) {
        self.std = std;
    }
}

pub struct Primitives {
    pub bool: Type,
}
impl Primitives {
    pub fn bool_info(&self) -> TypeInfo {
        TypeInfo::Known(self.bool)
    }

    pub fn resolve(compiler: &mut Compiler) -> Primitives {
        let std = compiler.get_project(compiler.builtins.std).root_module;
        let primitive = resolve_module(compiler, std, "primitive");
        Self {
            bool: resolve_type(compiler, primitive, "bool"),
        }
    }
}
impl Default for Primitives {
    fn default() -> Self {
        Self {
            bool: Type::MISSING,
        }
    }
}

fn resolve_module(compiler: &Compiler, module: ModuleId, name: &str) -> ModuleId {
    let def = compiler.resolve_in_module(module, name, ModuleSpan::MISSING);
    let Def::Module(id) = def else {
        panic!("Missing builtin module {name}, found {def:?}");
    };
    id
}

fn resolve_base_type(
    compiler: &Compiler,
    module: ModuleId,
    name: &str,
    generic_count: u8,
) -> BaseType {
    let def = compiler.resolve_in_module(module, name, ModuleSpan::MISSING);
    let Def::BaseType(ty) = def else {
        panic!("Missing builtin type {name}, found {def:?}");
    };
    assert_eq!(compiler.get_base_type_generic_count(ty), generic_count);
    ty
}

fn resolve_type(compiler: &Compiler, module: ModuleId, name: &str) -> Type {
    let def = compiler.resolve_in_module(module, name, ModuleSpan::MISSING);
    let Def::Type(ty) = def else {
        panic!("Missing builtin type {name}, found {def:?}");
    };
    ty
}

pub fn get_str(compiler: &Compiler) -> Type {
    *compiler.builtins.str_type.get_or_init(|| {
        let string_module = get_string_module(compiler);
        resolve_type(compiler, string_module, "str")
    })
}

fn get_string_module(compiler: &Compiler) -> ModuleId {
    let std = compiler.builtins.std;
    let root = compiler.get_project(std).root_module;
    resolve_module(compiler, root, "string")
}

pub fn get_str_eq(compiler: &Compiler) -> (ModuleId, FunctionId) {
    *compiler.builtins.str_eq.get_or_init(|| {
        let string_module = get_string_module(compiler);
        let Def::BaseType(str_type) =
            compiler.resolve_in_module(string_module, "str", ModuleSpan::MISSING)
        else {
            panic!("missing std.string.str");
        };
        let Some(&str_eq) = compiler.get_base_type_def(str_type).methods.get("eq") else {
            panic!("missing std.str.eq method");
        };
        (string_module, str_eq)
    })
}

pub fn get_prelude(compiler: &Compiler) -> ModuleId {
    *compiler.builtins.prelude.get_or_init(|| {
        let std = compiler.builtins.std;
        let root = compiler.get_project(std).root_module;
        let prelude = compiler.resolve_in_module(root, "prelude", ModuleSpan::MISSING);
        let Def::Module(prelude) = prelude else {
            panic!("expected a module for std.prelude, found {prelude:?}");
        };
        prelude
    })
}

pub fn get_panic(compiler: &Compiler) -> (ModuleId, FunctionId) {
    *compiler.builtins.panic.get_or_init(|| {
        let std = compiler.builtins.std;
        let root = compiler.get_project(std).root_module;
        let def = compiler.resolve_in_module(root, "panic", ModuleSpan::MISSING);
        let Def::Function(panic_mod, panic_func) = def else {
            panic!("expected a function for std.panic, found {def:?}")
        };
        (panic_mod, panic_func)
    })
}

pub fn get_intrinsic(compiler: &Compiler) -> (ModuleId, FunctionId) {
    *compiler.builtins.intrinsic.get_or_init(|| {
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
        (module, id)
    })
}

pub fn get_iterator(compiler: &Compiler) -> (ModuleId, TraitId) {
    *compiler.builtins.iterator.get_or_init(|| {
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
        (module, id)
    })
}

pub fn get_option(compiler: &Compiler) -> BaseType {
    *compiler.builtins.option.get_or_init(|| {
        let std = compiler.builtins.std;
        let root = compiler.get_project(std).root_module;
        let option_module = resolve_module(compiler, root, "option");
        resolve_base_type(compiler, option_module, "Option", 1)
    })
}

pub fn get_fn_trait(compiler: &Compiler) -> (ModuleId, TraitId) {
    *compiler.builtins.fn_trait.get_or_init(|| {
        let std = compiler.builtins.std;
        let root = compiler.get_project(std).root_module;
        let fn_module = resolve_module(compiler, root, "call");
        let Def::Trait(module, t) =
            compiler.resolve_in_module(fn_module, "Fn", ModuleSpan::MISSING)
        else {
            panic!("expected a trait for std.call.Fn");
        };
        (module, t)
    })
}
