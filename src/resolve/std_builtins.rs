use crate::ast::{TypeId, ModuleId, FunctionId, Ast, TypeDef};

use super::{scope::{Scopes, ScopeId, UnresolvedDefId}, types::DefId, type_info::{TypeInfo, TypeTableIndices}};

/// Builtin items that are defined in the std library and are required by many parts of the compiler,
/// for example because they can be constructed with special syntax (strings).
#[derive(Debug)]
pub struct Builtins {
    pub str_type: TypeId,
    pub str_eq: FunctionId,
}
impl Builtins {
    pub fn resolve(scopes: &mut Scopes, std: ModuleId, ast: &Ast) -> Self {
        fn get_def_in_mod(scopes: &mut Scopes, module: ModuleId, name: &str) -> DefId {
            let def = scopes[ScopeId::module(module)].get_def(name)
                .unwrap_or_else(|| panic!("definition '{name}' not found in std"));
            match def {
                UnresolvedDefId::Resolved(def) => *def,
                _ => panic!("invalid type of definition for '{name}' in std")
            }
        }
        let DefId::Module(string_mod) = get_def_in_mod(scopes, std, "string") else {
            panic!("module expected for 'string'")
        };
        
        let DefId::Type(str_type) = get_def_in_mod(scopes, string_mod, "str") else {
            panic!("type expected for 'str'")
        };
        let TypeDef::Struct(str_def) = &ast[str_type] else {
            panic!("struct expected for 'str'")
        };
        let str_eq = str_def.methods["eq"];

        Self { str_type, str_eq }
    }

    pub fn str_info(&self) -> TypeInfo {
        TypeInfo::Resolved(self.str_type, TypeTableIndices::EMPTY)
    }
}
