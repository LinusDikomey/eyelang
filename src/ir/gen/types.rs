use std::collections::HashMap;
use crate::{
    ast::{Ast, ModuleId, StructDefinition, self, UnresolvedType, TSpan, IdentPath},
    error::{Errors, Error},
    ir::{gen::FunctionOrHeader, Type}, lexer::Span
};
use super::{gen::{TypingCtx, Symbol}, SymbolKey, TypeDef, FunctionHeader, Scope};

#[derive(Clone, Debug)]
pub struct Globals(Vec<HashMap<String, Symbol>>);
impl Globals {
    pub fn get_ref(&self) -> GlobalsRef {
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

pub fn gen_globals(ast: &Ast, ctx: &mut TypingCtx, errors: &mut Errors) -> Globals {
    let mut symbols = (0..ast.modules.len()).map(|_| HashMap::new()).collect::<Vec<_>>();

    for (module_id, module) in ast.modules.iter().enumerate() {
        let module_id = ModuleId::new(module_id as u32);
        for (name, def) in &module.definitions {
            add_global_def(def, ctx, ast, &mut symbols, module_id, name, errors);
        }
    }
    Globals(symbols)
}

fn add_global_def(
    def: &ast::Definition,
    ctx: &mut TypingCtx,
    ast: &Ast,
    symbols: &mut [HashMap<String, Symbol>],
    module: ModuleId,
    name: &str,
    errors: &mut Errors,
) -> Option<Symbol> {
    Some(match def {
        ast::Definition::Function(func) => {
            Symbol::Func(add_func(ctx, ast, symbols, func, module, name, errors))
        }
        ast::Definition::Struct(struct_) => {
            Symbol::Type(add_struct(ctx, ast, symbols, struct_, module, name, errors))
        }
        ast::Definition::Module(inner_module) => {
            symbols[module.idx()].insert(name.to_owned(), Symbol::Module(*inner_module));
            Symbol::Module(*inner_module)
        }
        ast::Definition::Use(path) => {
            if let Some(symbol) = resolve_global_path(path, ast, ctx, symbols, module, errors) {
                symbols[module.idx()].insert(name.to_owned(), symbol);
                symbol
            } else {
                return None;
            }
        }
    })
}

fn local_ty(
    unresolved: &UnresolvedType,
    symbols: &mut HashMap<String, Symbol>,
    defs: &HashMap<String, ast::Definition>,
    scope: &mut Scope,
    errors: &mut Errors
) -> Type {
    match unresolved {
        UnresolvedType::Primitive(p, _) => Type::Prim(*p),
        UnresolvedType::Unresolved(path) => {
            match resolve_local_path(path, scope, symbols, defs, errors) {
                Some(Symbol::Type(key)) => Type::Id(key),
                Some(_) => {
                    errors.emit_span(Error::TypeExpected, path.span().in_mod(scope.module));
                    Type::Invalid
                }
                _ => Type::Invalid // an error was already emitted for this
            }
        }
        UnresolvedType::Pointer(box (inner, _)) => {
            local_ty(inner, symbols, defs, scope, errors)
        }
        UnresolvedType::Array(box (inner, span, count)) => {
            let Some(count) = *count else {
                errors.emit_span(Error::ArraySizeCantBeInferredHere, span.in_mod(scope.module));
                return Type::Invalid;
            };
            Type::Array(Box::new((local_ty(inner, symbols, defs, scope, errors), count)))
        }
        UnresolvedType::Infer(start) => {
            errors.emit(Error::InferredTypeNotAllowedHere, *start, *start, scope.module);
            Type::Invalid
        }
    }
}

pub fn gen_locals(
    scope: &mut Scope,
    defs: &HashMap<String, ast::Definition>,
    errors: &mut Errors
) -> HashMap<String, Symbol> {
    let mut symbols = HashMap::with_capacity(defs.len());
    for (name, def) in defs {
        if symbols.contains_key(name) { continue }
        gen_local(name.clone(), def, &mut symbols, defs, scope, errors);
    }
    symbols
}

pub fn add_func(
    ctx: &mut TypingCtx,
    ast: &Ast,
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
            (name.clone(), resolve_ty(ctx, ast, symbols, module, param_ty, errors))
        )
        .collect();
    let return_type = resolve_ty(ctx, ast, symbols, module, &func.return_type, errors);
    let key = ctx.add_func(super::gen::FunctionOrHeader::Header(FunctionHeader {
        params,
        varargs: func.varargs,
        return_type
    }));
    symbols[module.idx()].insert(name.to_owned(), Symbol::Func(key));
    key
}

pub fn add_struct(
    ctx: &mut TypingCtx,
    modules: &Ast,
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
    let members = def.members.iter().map(|(name, unresolved, _start, _end)| {(
        name.clone(),
        resolve_ty(ctx, modules, symbols, module, unresolved, errors)
    )}).collect::<Vec<_>>();
    let key = ctx.add_type(TypeDef::Struct(crate::ir::Struct { members, name: name.to_owned() }));
    symbols[module.idx()].insert(name.to_owned(), Symbol::Type(key));
    key
}

enum ResolveState <'a, 's, 'd> {
    Local(&'a mut Scope<'s>, &'a mut HashMap<String, Symbol>, &'d HashMap<String, ast::Definition>),
    Module(ModuleId)
}
enum ResolveSymbols<'a> {
    Mutable(&'a Ast, &'a mut [HashMap<String, Symbol>], &'a mut TypingCtx),
    Finished(GlobalsRef<'a>)
}
impl<'a> ResolveSymbols<'a> {
    fn get<'b>(&'b mut self, module: ModuleId, name: &str, span: Span, errors: &mut Errors) -> Option<Symbol> {
        match self {
            ResolveSymbols::Mutable(ast, symbols, ctx) => {
                if let Some(symbol) = symbols[module.idx()].get(name) {
                    Some(*symbol)
                } else  if let Some(def) = ast.modules[module.idx()].definitions.get(name) {
                    add_global_def(def, ctx, ast, symbols, module, name, errors)
                } else {
                    errors.emit_span(Error::UnknownIdent, span);
                    None
                }
            }
            ResolveSymbols::Finished(symbols) => {
                let symbol = symbols[module].get(name).copied();
                if symbol.is_none() {
                    errors.emit_span(Error::UnknownIdent, span);
                }
                symbol
            }
        }
    }
}

/// Resolving of `IdentPath`. This function is complicated because it can handle 2 different states:
/// generating globals or generating locals.
fn resolve_path(
    path: &IdentPath,
    mut symbols: ResolveSymbols,
    mut state: ResolveState,
    path_module: ModuleId,
    src: &str,
    errors: &mut Errors
) -> Option<Symbol> {
    let (root, segments, last) = path.segments(src);
    if root.is_some() {
        state = ResolveState::Module(ModuleId::ROOT);
    }

    for (name, span) in segments {
        match state {
            ResolveState::Local(scope, symbols, defs) => {
                match resolve_in_scope(name, span, scope, symbols, defs, errors) {
                    Some(Symbol::Module(new_module)) => state = ResolveState::Module(new_module),
                    Some(_) => {
                        errors.emit_span(Error::ModuleExpected, span.in_mod(path_module));
                        return None;
                    }
                    None => return None
                }
            },
            ResolveState::Module(id) => {
                if let Some(def) = symbols.get(id, name, span.in_mod(path_module), errors) {
                    if let Symbol::Module(new_module) = def {
                        state = ResolveState::Module(new_module);
                    } else {
                        errors.emit_span(Error::ModuleExpected, span.in_mod(path_module));
                        return None;
                    }
                } else {
                    return None;
                }
            }
        }
    }

    if let Some((name, span)) = last {
        match state {
            ResolveState::Local(scope, symbols, defs)
                => resolve_in_scope(name, span, scope, symbols, defs, errors),
            ResolveState::Module(id) => {
                let symbol = symbols.get(id, name, span.in_mod(path_module), errors);
                if symbol.is_none() {
                    errors.emit_span(Error::UnknownIdent, span.in_mod(path_module));
                }
                symbol
            }
        }
    } else {
        match state {
            ResolveState::Local(_, _, _) => unreachable!(),
            ResolveState::Module(id) => Some(Symbol::Module(id))
        }
    }
}

fn resolve_global_path(
    path: &IdentPath,
    ast: &Ast,
    ctx: &mut TypingCtx,
    symbols: &mut [HashMap<String, Symbol>],
    module: ModuleId,
    errors: &mut Errors
) -> Option<Symbol> {
    resolve_path(
        path,
        ResolveSymbols::Mutable(ast, symbols, ctx),
        ResolveState::Module(module),
        module,
        ast.src(module).0,
        errors
    )
}

fn resolve_local_path(
    path: &IdentPath,
    scope: &mut Scope,
    symbols: &mut HashMap<String, Symbol>,
    defs: &HashMap<String, ast::Definition>,
    errors: &mut Errors
) -> Option<Symbol> {
    let module = scope.module;
    let src = scope.ast.src(module).0;

    resolve_path(
        path,
        ResolveSymbols::Finished(scope.globals),
        ResolveState::Local(scope, symbols, defs),
        module,
        src,
        errors
    )
}

fn resolve_in_scope(
    name: &str,
    span: TSpan,
    scope: &mut Scope,
    symbols: &mut HashMap<String, Symbol>,
    defs: &HashMap<String, ast::Definition>,
    errors: &mut Errors
) -> Option<Symbol> {
    if let Some(symbol) = symbols.get(name) {
        Some(*symbol)
    } else if let Some(def) = defs.get(name) {
        gen_local(name.to_owned(), def, symbols, defs, scope, errors)
    } else {
        scope.info.parent().and_then(|parent| match parent.resolve_local(name) {
            Ok(resolved) => resolved.into_symbol(),
            Err(err) => {
                errors.emit_span(err, span.in_mod(scope.module));
                None
            }
        })
    }
}

fn resolve_ty(
    ctx: &mut TypingCtx,
    ast: &Ast,
    symbols: &mut [HashMap<String, Symbol>],
    path_module: ModuleId,
    unresolved: &UnresolvedType,
    errors: &mut Errors
) -> Type {
    match unresolved {
        crate::ast::UnresolvedType::Primitive(p, _) => Type::Prim(*p),
        crate::ast::UnresolvedType::Unresolved(path) => {
            match resolve_global_path(path, ast, ctx, symbols, path_module, errors) {
                Some(Symbol::Type(ty)) => Type::Id(ty),
                Some(_) => {
                    errors.emit_span(Error::TypeExpected, path.span().in_mod(path_module));
                    Type::Invalid
                }
                None => Type::Invalid // an error was already emitted in this case
            }

        }
        UnresolvedType::Pointer(box (inner, _))
            => Type::Pointer(Box::new(resolve_ty(ctx, ast, symbols, path_module, inner, errors))),
        UnresolvedType::Array(box (inner, span, count)) => {
            let Some(count) = *count else {
                errors.emit_span(Error::ArraySizeCantBeInferredHere, span.in_mod(path_module));
                return Type::Invalid;
            };
            Type::Array(Box::new((resolve_ty(ctx, ast, symbols, path_module, inner, errors), count)))
        }
        UnresolvedType::Infer(start) => {
            errors.emit(Error::InferredTypeNotAllowedHere, *start, *start, path_module);
            Type::Invalid
        }
        
    }
}

fn gen_local(name: String, def: &ast::Definition, symbols: &mut HashMap<String, Symbol>, defs: &HashMap<String, ast::Definition>, scope: &mut Scope, errors: &mut Errors) -> Option<Symbol> {
    match def {
        ast::Definition::Function(func) => {
            let params = func.params.iter()
                .map(|(name, unresolved, _, _)| {
                    (name.clone(), local_ty(unresolved, symbols, defs, scope, errors))
                })
                .collect();
            let return_type = local_ty(&func.return_type, symbols, defs, scope, errors);
            let symbol = Symbol::Func(
                scope.ctx.add_func(FunctionOrHeader::Header(FunctionHeader {
                    params,
                    varargs: func.varargs,
                    return_type,
                })
            ));
            symbols.insert(name, symbol);
            Some(symbol)
        }
        ast::Definition::Struct(struct_) => {
            let members = struct_.members.iter()
                .map(|(name, unresolved, _, _)| {
                    (name.clone(), local_ty(unresolved, symbols, defs, scope, errors))
                })
                .collect();

            let idx = scope.ctx.add_type(TypeDef::Struct(super::Struct { name: name.clone(), members }));
            let symbol = Symbol::Type(idx);
            symbols.insert(name, symbol);
            Some(symbol)
        }
        ast::Definition::Module(id) => {
            let symbol = Symbol::Module(*id);
            symbols.insert(name, symbol);
            Some(symbol)
        }
        ast::Definition::Use(path) => {
            resolve_local_path(path, scope, symbols, defs, errors).map(|symbol| {
                symbols.insert(name, symbol);
                symbol
            })
        }
    }
}