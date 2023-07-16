use crate::{ast::{TypeId, ModuleId, FunctionId, Ast, TypeDef}, ir::types::{TypeRefs, IrType}};

use super::{scope::{Scopes, ScopeId, UnresolvedDefId}, types::DefId, type_info::TypeInfo};

/// Builtin items that are defined in the std library and are required by many parts of the compiler,
/// for example because they can be constructed with special syntax (strings).
#[derive(Debug)]
pub struct Builtins {
    values: Option<BuiltinValues>,
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

        let DefId::Module(prelude) = get_def_in_mod(scopes, std, "prelude") else {
            panic!("Module expected for 'predude'")
        };

        Self { values: Some(BuiltinValues { str_type, str_eq, _prelude: prelude }) }
    }

    pub const fn nostd() -> Self {
        Self { values: None }
    }
    
    fn values(&self) -> &BuiltinValues {
        self.values.as_ref().expect("Builtins not available because the project was compiled with --nostd")
    }

    pub fn str_info(&self) -> TypeInfo {
        TypeInfo::Resolved(self.values().str_type, TypeRefs::EMPTY)
    }
    pub fn str_ty(&self) -> TypeId { self.values().str_type }
    pub fn str_ir_ty(&self) -> IrType { IrType::Id(self.values().str_type, TypeRefs::EMPTY) }
    pub fn str_eq(&self) -> FunctionId { self.values().str_eq }
}

#[derive(Debug)]
struct BuiltinValues {
    str_type: TypeId,
    str_eq: FunctionId,
    _prelude: ModuleId,
}
