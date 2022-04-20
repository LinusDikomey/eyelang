use std::{collections::HashMap, num::NonZeroU8};
use crate::{
    ast::{Modules, ModuleId, StructDefinition, self, UnresolvedType},
    error::{Errors, Error},
    ir::{gen::FunctionOrHeader, BaseType}
};
use super::{gen::{TypingCtx, Symbol}, SymbolKey, TypeDef, TypeRef, FunctionHeader, Scope};

#[derive(Clone, Debug)]
pub struct Globals(Vec<HashMap<String, Symbol>>);
impl Globals {
    pub fn get_ref<'a>(&'a self) -> GlobalsRef<'a> {
        GlobalsRef(&self.0)
    }
}
impl std::ops::Index<ModuleId> for Globals {
    type Output = HashMap<String, Symbol>;

    fn index(&self, index: ModuleId) -> &Self::Output {
        &self.0[index.idx()]
    }
}

/// For passing arround a reference to globals. More efficient than &Globals.
#[derive(Clone, Copy)]
pub struct GlobalsRef<'a>(&'a [HashMap<String, Symbol>]);
impl std::ops::Index<ModuleId> for GlobalsRef<'_> {
    type Output = HashMap<String, Symbol>;
    fn index(&self, index: ModuleId) -> &Self::Output {
        &self.0[index.idx()]
    }
}

pub fn gen_globals(modules: &Modules, ctx: &mut TypingCtx, errors: &mut Errors) -> Globals {
    let mut symbols = (0..modules.len()).map(|_| HashMap::new()).collect::<Vec<_>>();

    for (module_id, module) in modules.iter() {
        for (name, def) in &module.definitions {
            add_global_def(def, ctx, &modules, &mut symbols, module_id, name, errors);
        }
    }
    Globals(symbols)
}

fn add_global_def(
    def: &ast::Definition,
    ctx: &mut TypingCtx,
    modules: &Modules,
    symbols: &mut [HashMap<String, Symbol>],
    module: ModuleId,
    name: &str,
    errors: &mut Errors,
) -> Option<Symbol> {
    Some(match def {
        ast::Definition::Function(func) => {
            Symbol::Func(add_func(ctx, modules, symbols, func, module, name, errors))
        }
        ast::Definition::Struct(struct_) => {
            Symbol::Type(add_struct(ctx, modules, symbols, struct_, module, name, errors))
        }
        ast::Definition::Module(inner_module) => {
            symbols[module.idx()].insert(name.to_owned(), Symbol::Module(*inner_module));
            Symbol::Module(*inner_module)
        }
        ast::Definition::Use(path) => {
            if let Some(symbol) = resolve_global_path(ctx, modules, symbols, path, module, errors) {
                symbols[module.idx()].insert(name.to_owned(), symbol);
                symbol
            } else {
                return None;
            }
        }
    })
}

pub fn gen_locals(
    scope: &mut Scope,
    defs: &HashMap<String, ast::Definition>,
    errors: &mut Errors
) -> HashMap<String, Symbol> {
    //TODO: split off path resolving into it's own function for use statements
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
                        match scope.globals[module].get(segment) {
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
                    let Some(symbol) = scope.globals[module].get(last) else {
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
            ast::Definition::Use(_) => todo!("local use statements aren't supported right now")
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
    if let Some(existing) = symbols[module.idx()].get(name) {
        let Symbol::Func(key) = existing else { unreachable!() };
        return *key;
    }

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

fn resolve_global_path(
    ctx: &mut TypingCtx,
    modules: &Modules,
    symbols: &mut [HashMap<String, Symbol>],
    path: &ast::IdentPath,
    module: ModuleId,
    errors: &mut Errors
) -> Option<Symbol> {
    let (root, segments, last) = path.segments();
    let Some(last) = last else {
        errors.emit(Error::CantUseRootPath, 0, 0, module);
        return None;
    };
    let mut module = if root { ModuleId::ROOT } else { module };
    // handle all but the last path segments to go to the correct module
    let mut update = |name| {
        if let Some(def) = modules[module].definitions.get(name) {
            match def {
                ast::Definition::Module(new_module) => module = *new_module,
                _ => {
                    errors.emit(Error::ModuleExpected, 0, 0, module);
                    return false;
                }
            }
        } else {
            errors.emit(Error::UnknownIdent, 0, 0, module);
            return false;
        }
        true
    };
    for name in segments {
        if !update(name) { return None };
    }
    resolve_in_module(ctx, modules, symbols, module, last, errors)
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
            match resolve_in_module(ctx, modules, symbols, module, last, errors) {
                Some(Symbol::Type(ty)) => TypeRef::Base(BaseType::Id(ty)),
                Some(_) => {
                    errors.emit(Error::TypeExpected, 0, 0, module);
                    TypeRef::Invalid
                }
                None => TypeRef::Invalid // an error was already emitted in this case
            }
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

fn resolve_in_module(
    ctx: &mut TypingCtx,
    modules: &Modules,
    symbols: &mut [HashMap<String, Symbol>],
    module: ModuleId,
    name: &str,
    errors: &mut Errors
) -> Option<Symbol> {
    if let Some(symbol) = symbols[module.idx()].get(name) {
        /*match symbol {
            Symbol::Type(ty) => return TypeRef::Base(BaseType::Id(*ty)),
            _ => {}
        }*/
        Some(*symbol)
    } else if let Some(def) = modules[module].definitions.get(name) {
        add_global_def(def, ctx, modules, symbols, module, name, errors)
    } else {
        errors.emit(Error::UnknownIdent, 0, 0, module);
        None
    }
}