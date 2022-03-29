use std::{collections::HashMap, num::NonZeroU8};

use crate::{
    ast::{Modules, ModuleId, StructDefinition, self, UnresolvedType},
    error::{Errors, Error},
    ir::{gen::FunctionOrHeader, BaseType}
};
use super::{gen::{TypingCtx, Symbol}, SymbolKey, TypeDef, TypeRef, FunctionHeader, Scope};

pub fn gen_globals(modules: &Modules, ctx: &mut TypingCtx, errors: &mut Errors) -> Vec<HashMap<String, Symbol>> {
    let mut symbols = (0..modules.len()).map(|_| HashMap::new()).collect::<Vec<_>>();

    for (module_id, module) in modules.iter() {
        for (name, def) in &module.definitions {
            match def {
                ast::Definition::Function(func) => {
                    add_func(ctx, modules, &mut symbols, func, module_id, name, errors);
                }
                ast::Definition::Struct(struct_) => {
                    add_struct(ctx, modules, &mut symbols, struct_, module_id, name, errors);
                }
                ast::Definition::Module(module) => {
                    symbols[module_id.idx()].insert(name.clone(), Symbol::Module(*module));
                }
            }
        }
    }

    symbols
}

pub fn gen_locals(
    scope: &mut Scope,
    defs: &HashMap<String, ast::Definition>,
    errors: &mut Errors
) -> HashMap<String, Symbol> {
    fn ty(
        unresolved: &UnresolvedType,
        symbols: &mut HashMap<String, Symbol>,
        defs: &HashMap<String, ast::Definition>,
        scope: &mut Scope,
        errors: &mut Errors
    ) -> TypeRef {
        match unresolved {
            UnresolvedType::Primitive(p) => TypeRef::Base(BaseType::Prim(*p)),
            UnresolvedType::Unresolved(path) => {
                let (root, segments, last) = path.segments();
                let Some(last) = last else {
                    errors.emit(Error::TypeExpected, 0, 0, scope.module);
                    return TypeRef::Invalid
                };
                let mut current_module = root.then_some(ModuleId::ROOT);

                for segment in segments {
                    if let Some(module) = current_module {
                        match scope.globals[module.idx()].get(segment) {
                            Some(Symbol::Module(id)) => current_module = Some(*id),
                            Some(_) => {
                                errors.emit(Error::ModuleExpected, 0, 0, scope.module);
                                return TypeRef::Invalid
                            }
                            None => {
                                errors.emit(Error::UnknownIdent, 0, 0, scope.module);
                                return TypeRef::Invalid
                            }
                        }

                    }
                }

                let mut symbol_to_ty = |symbol: &Symbol| {
                    match symbol {
                        Symbol::Type(key) => TypeRef::Base(BaseType::Id(*key)),
                        _ => {
                            errors.emit(Error::TypeExpected, 0, 0, scope.module);
                            TypeRef::Invalid
                        }
                    }
                };
                if let Some(module) = current_module {
                    let Some(symbol) = scope.globals[module.idx()].get(last) else {
                        errors.emit(Error::UnknownIdent, 0, 0, scope.module);
                        return TypeRef::Invalid;
                    };
                    symbol_to_ty(symbol)

                } else {
                    if let Some(symbol) = symbols.get(last) {
                        symbol_to_ty(symbol)
                    } else if let Some(def) = defs.get(last) {
                        if let ast::Definition::Struct(struct_) = def {
                            gen_struct(last, struct_, symbols, defs, scope, errors)
                        } else {
                            errors.emit(Error::TypeExpected, 0, 0, scope.module);
                            TypeRef::Invalid
                        }
                    } else {
                        errors.emit(Error::UnknownIdent, 0, 0, scope.module);
                        TypeRef::Invalid
                    }
                }
            }
            UnresolvedType::Pointer(inner) => {
                ty(inner, symbols, defs, scope, errors)
            }
        }
    }

    fn gen_struct(
        name: &String,
        struct_: &StructDefinition,
        symbols: &mut HashMap<String, Symbol>,
        defs: &HashMap<String, ast::Definition>,
        scope: &mut Scope,
        errors: &mut Errors
    ) -> TypeRef {
        let members = struct_.members.iter()
            .map(|(name, unresolved, _, _)| {
                (name.clone(), ty(unresolved, symbols, defs, scope, errors))
            })
            .collect();

        let idx = scope.ctx.add_type(TypeDef::Struct(super::Struct { name: name.clone(), members }));
        symbols.insert(name.clone(), Symbol::Type(idx));
        TypeRef::Base(BaseType::Id(idx))
    }

    let mut symbols = HashMap::with_capacity(defs.len());

    for (name, def) in defs {
        if symbols.contains_key(name) { continue }

        match def {
            ast::Definition::Function(func) => {
                let params = func.params.iter()
                    .map(|(name, unresolved, _, _)| {
                        (name.clone(), ty(unresolved, &mut symbols, defs, scope, errors))
                    })
                    .collect();
                let return_type = ty(&func.return_type.0, &mut symbols, defs, scope, errors);
                symbols.insert(name.clone(), Symbol::Func(scope.ctx.add_func(FunctionOrHeader::Header(FunctionHeader {
                    name: name.clone(),
                    params,
                    varargs: func.varargs,
                    return_type,
                }))));
            }
            ast::Definition::Struct(struct_) => {
                gen_struct(name, struct_, &mut symbols, defs, scope, errors);
            }
            ast::Definition::Module(id) => {
                symbols.insert(name.clone(), Symbol::Module(*id));
            }
        };
    }

    symbols
}

pub fn add_func(
    ctx: &mut TypingCtx,
    modules: &Modules,
    symbols: &mut [HashMap<String, Symbol>],
    func: &ast::Function,
    module: ModuleId,
    name: &str,
    errors: &mut Errors
) -> SymbolKey {
    // This should not happen because functions shouldn't cross-refererence.
    // If they do in the future, do the same as add_struct does
    debug_assert!(!symbols[module.idx()].contains_key(name));

    let params = func.params.iter()
        .map(|(name, param_ty, _start, _end)| 
            (name.clone(), resolve(ctx, modules, symbols, module, param_ty, errors))
        )
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

pub fn add_struct(
    ctx: &mut TypingCtx,
    modules: &Modules,
    symbols: &mut [HashMap<String, Symbol>],
    def: &StructDefinition,
    module: ModuleId,
    name: &str,
    errors: &mut Errors
) -> SymbolKey {
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

fn resolve(
    ctx: &mut TypingCtx,
    modules: &Modules,
    symbols: &mut [HashMap<String, Symbol>],
    module: ModuleId,
    unresolved: &UnresolvedType,
    errors: &mut Errors
) -> TypeRef {
    match unresolved {
        crate::ast::UnresolvedType::Primitive(p) => TypeRef::Base(BaseType::Prim(*p)),
        crate::ast::UnresolvedType::Unresolved(path) => {
            let (root, segments, last) = path.segments();
            let Some(last) = last else {
                errors.emit(Error::TypeExpected, 0, 0, module);
                return TypeRef::Invalid;
            };
            let mut module = if root { ModuleId::ROOT } else { module };
            // handle all but the last path segments to go to the correct module
            let mut update = |name| {
                if let Some(def) = modules[module].definitions.get(name) {
                    match def {
                        ast::Definition::Module(new_module) => module = *new_module,
                        _ => {
                            errors.emit(Error::ModuleExpected, 0, 0, module);
                            return Some(TypeRef::Invalid);
                        }
                    }
                } else {
                    errors.emit(Error::UnknownIdent, 0, 0, module);
                    return Some(TypeRef::Invalid);
                }
                None
            };
            for name in segments {
                if let Some(err) = update(name) { return err };
            }
            ty(ctx, modules, symbols, module, last, errors)
        }
        UnresolvedType::Pointer(inner) => {
            match resolve(ctx, modules, symbols, module, inner, errors) {
                TypeRef::Base(inner) => TypeRef::Pointer { count: unsafe { NonZeroU8::new_unchecked(1) }, inner },
                TypeRef::Pointer { count, inner } => { 
                    if count.get() == u8::MAX {
                        errors.emit(Error::TooLargePointer, 0, 0, module);
                    }
                    TypeRef::Pointer { count: count.saturating_add(1), inner }
                }
                TypeRef::Invalid => TypeRef::Invalid,
            }
        }
        
    }
}

fn ty(
    ctx: &mut TypingCtx,
    modules: &Modules,
    symbols: &mut [HashMap<String, Symbol>],
    module: ModuleId,
    name: &str,
    errors: &mut Errors
) -> TypeRef {
    if let Some(symbol) = symbols[module.idx()].get(name) {
        match symbol {
            Symbol::Type(ty) => return TypeRef::Base(BaseType::Id(*ty)),
            _ => {}
        }
    } else if let Some(def) = modules[module].definitions.get(name) {
        match def {
            crate::ast::Definition::Struct(struct_) => {
                return TypeRef::Base(BaseType::Id(add_struct(ctx, modules, symbols, struct_, module, name, errors)));
            }
            _ => {}
        }
    }
    errors.emit(Error::TypeExpected, 0, 0, module);
    TypeRef::Invalid
}