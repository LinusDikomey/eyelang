use std::collections::HashMap;

use crate::{ast::{Modules, ModuleId, StructDefinition, self, UnresolvedType}, error::{Errors, Error}};

use super::{gen::{TypingCtx, Symbol}, SymbolKey, TypeDef, TypeRef, FunctionHeader};

pub fn gen_globals(modules: &Modules, ctx: &mut TypingCtx, errors: &mut Errors) -> Vec<HashMap<String, Symbol>> {
    let mut symbols = (0..modules.len()).map(|_| HashMap::new()).collect::<Vec<_>>();

    for (module_id, module) in modules.iter() {
        for (name, def) in &module.definitions {
            match def {
                ast::Definition::Function(func) => { add_func(ctx, modules, &mut symbols, func, module_id, name, errors); }
                ast::Definition::Struct(struct_) => { add_struct(ctx, modules, &mut symbols, struct_, module_id, name, errors); }
                ast::Definition::Module(module) => {
                    symbols[module_id.idx()].insert(name.clone(), Symbol::Module(*module));
                }
            }
        }
    }

    symbols
}

pub fn add_func(ctx: &mut TypingCtx, modules: &Modules, symbols: &mut [HashMap<String, Symbol>], func: &ast::Function, module: ModuleId, name: &str, errors: &mut Errors) -> SymbolKey {
    // This should not happen because functions shouldn't cross-refererence.
    // If they do in the future, do the same as add_struct does
    debug_assert!(!symbols[module.idx()].contains_key(name));

    let params = func.params.iter()
        .map(|(name, param_ty, _start, _end)| (name.clone(), resolve(ctx, modules, symbols, module, param_ty, errors)))
        .collect();
    let return_type = resolve(ctx, modules, symbols, module, &func.return_type.0, errors);
    let key = ctx.add_func(super::gen::FunctionOrHeader::Header(FunctionHeader {
        name: name.to_owned(),
        params,
        varargs: func.varargs,
        return_type
    }));
    symbols[module.idx()].insert(name.to_owned(), Symbol::Func(key));
    key
}

pub fn add_struct(ctx: &mut TypingCtx, modules: &Modules, symbols: &mut [HashMap<String, Symbol>], def: &StructDefinition, module: ModuleId, name: &str, errors: &mut Errors) -> SymbolKey {
    if let Some(existing) = symbols[module.idx()].get(name) {
        let Symbol::Type(key) = existing else { unreachable!() };
        return *key;
    }
    let members = def.members.iter().map(|(name, unresolved, _start, _end)| {
        (
            name.to_owned(),
            resolve(ctx, modules, symbols, module, unresolved, errors)
        )
    }).collect::<Vec<_>>();
    let key = ctx.add_type(TypeDef::Struct(crate::ir::Struct { members, name: name.to_owned() }));
    symbols[module.idx()].insert(name.to_owned(), Symbol::Type(key));
    key
}

fn resolve(ctx: &mut TypingCtx, modules: &Modules, symbols: &mut [HashMap<String, Symbol>], module: ModuleId, unresolved: &UnresolvedType, errors: &mut Errors) -> TypeRef {
    match unresolved {
        crate::ast::UnresolvedType::Primitive(p) => TypeRef::Primitive(*p),
        crate::ast::UnresolvedType::Unresolved(name) => ty(ctx, modules, symbols, module, name, errors),
    }
}

fn ty(ctx: &mut TypingCtx, modules: &Modules, symbols: &mut [HashMap<String, Symbol>], module: ModuleId, name: &str, errors: &mut Errors) -> TypeRef {
    if let Some(symbol) = symbols[module.idx()].get(name) {
        match symbol {
            Symbol::Type(ty) => return TypeRef::Resolved(*ty),
            _ => {}
        }
    } else {
        if let Some(def) = modules[module].definitions.get(name) {
            match def {
                crate::ast::Definition::Struct(struct_) => {
                    return TypeRef::Resolved(add_struct(ctx, modules, symbols, struct_, module, name, errors));
                }
                _ => {}
            }
        }
    }
    errors.emit(Error::TypeExpected, 0, 0, module);
    TypeRef::Invalid
}