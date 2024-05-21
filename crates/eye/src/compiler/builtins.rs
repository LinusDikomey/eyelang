use id::{ProjectId, TypeId};
use span::Span;
use types::Type;

use crate::Compiler;

use super::Def;

#[derive(Default)]
pub struct Builtins {
    std: Option<ProjectId>,
    str_type: Option<TypeId>,
}
impl Builtins {
    pub fn set_std(&mut self, std: ProjectId) {
        self.std = Some(std);
    }

    pub fn std(&self) -> ProjectId {
        let Some(std) = self.std else {
            panic!("Tried to use a builtin but no standard library is active");
        };
        std
    }
}

pub fn get_str(compiler: &mut Compiler) -> TypeId {
    if let Some(str_type) = compiler.builtins.str_type {
        return str_type;
    }
    let std = compiler.builtins.std();
    let root = compiler.get_project(std).root_module;
    let string = compiler.resolve_in_module(root, "string", Span::MISSING);
    let Def::Module(string_module) = string else {
        panic!("expected a module for builtin std.string, found {string:?}");
    };
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
