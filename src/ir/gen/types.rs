use std::{collections::HashMap, num::NonZeroU8};
use crate::{
    ast::{Ast, ModuleId, StructDefinition, self, UnresolvedType, TSpan},
    error::{Errors, Error},
    ir::{gen::FunctionOrHeader, BaseType}, lexer::Span
};
use super::{gen::{TypingCtx, Symbol}, SymbolKey, TypeDef, TypeRef, FunctionHeader, Scope};

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
            if let Some(symbol) = resolve_global_path(ctx, ast, symbols, path, module, errors) {
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
    //TODO: make UnresolvedTypes use spans to prevent String cloning and provide error spans
    fn ty(
        unresolved: &UnresolvedType,
        symbols: &mut HashMap<String, Symbol>,
        defs: &HashMap<String, ast::Definition>,
        scope: &mut Scope,
        errors: &mut Errors
    ) -> TypeRef {
        match unresolved {
            UnresolvedType::Primitive(p, _) => TypeRef::Base(BaseType::Prim(*p)),
            UnresolvedType::Unresolved(path) => {
                let (root, segments, last) = path.segments();
                let Some(last) = last else {
                    errors.emit_span(Error::TypeExpected, path.span().in_mod(scope.module));
                    return TypeRef::Invalid
                };
                let mut current_module = root.then_some(ModuleId::ROOT);

                for segment in segments {
                    if let Some(module) = current_module {
                        match scope.globals[module].get(scope.src(*segment)) {
                            Some(Symbol::Module(id)) => current_module = Some(*id),
                            Some(_) => {
                                errors.emit_span(Error::ModuleExpected, segment.in_mod(scope.module));
                                return TypeRef::Invalid
                            }
                            None => {
                                errors.emit_span(Error::UnknownIdent, segment.in_mod(scope.module));
                                return TypeRef::Invalid
                            }
                        }

                    }
                }

                let mut symbol_to_ty = |symbol: &Symbol, span: TSpan| {
                    if let Symbol::Type(key) = symbol {
                        TypeRef::Base(BaseType::Id(*key))
                    } else {
                        errors.emit_span(Error::TypeExpected, span.in_mod(scope.module));
                        TypeRef::Invalid
                    }
                };
                let last_str = &scope.ast.sources()[scope.module.idx()].0[last.range()];
                if let Some(module) = current_module {
                    let Some(symbol) = scope.globals[module].get(last_str) else {
                        errors.emit_span(Error::UnknownIdent, last.in_mod(scope.module));
                        return TypeRef::Invalid;
                    };
                    symbol_to_ty(symbol, last)
                } else if let Some(symbol) = symbols.get(last_str) {
                    symbol_to_ty(symbol, last)
                } else if let Some(def) = defs.get(last_str) {
                    if let ast::Definition::Struct(struct_) = def {
                        gen_struct(last_str, struct_, symbols, defs, scope, errors)
                    } else {
                        errors.emit_span(Error::TypeExpected, last.in_mod(scope.module));
                        TypeRef::Invalid
                    }
                } else {
                    errors.emit_span(Error::UnknownIdent, last.in_mod(scope.module));
                    TypeRef::Invalid
                }
            }
            UnresolvedType::Pointer(inner, _) => {
                ty(inner, symbols, defs, scope, errors)
            }
            UnresolvedType::Infer(start) => {
                errors.emit(Error::InferredTypeNotAllowedHere, *start, *start, scope.module);
                TypeRef::Invalid
            }
        }
    }

    fn gen_struct(
        name: &str,
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

        let idx = scope.ctx.add_type(TypeDef::Struct(super::Struct { name: name.to_owned(), members }));
        symbols.insert(name.to_owned(), Symbol::Type(idx));
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
            (name.clone(), resolve(ctx, ast, symbols, module, param_ty, errors))
        )
        .collect();
    let return_type = resolve(ctx, ast, symbols, module, &func.return_type.0, errors);
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
        resolve(ctx, modules, symbols, module, unresolved, errors)
    )}).collect::<Vec<_>>();
    let key = ctx.add_type(TypeDef::Struct(crate::ir::Struct { members, name: name.to_owned() }));
    symbols[module.idx()].insert(name.to_owned(), Symbol::Type(key));
    key
}

fn update_path_module(ast: &Ast, name: &str, span: Span, module: &mut ModuleId, errors: &mut Errors) -> bool {
    if let Some(def) = ast.modules[module.idx()].definitions.get(name) {
        if let ast::Definition::Module(new_module) = def {
            *module = *new_module;
        } else {
            errors.emit_span(Error::ModuleExpected, span);
            return false;
        }
    } else {
        errors.emit_span(Error::UnknownIdent, span);
        return false;
    }
    true
}

fn resolve_global_path(
    ctx: &mut TypingCtx,
    ast: &Ast,
    symbols: &mut [HashMap<String, Symbol>],
    path: &ast::IdentPath,
    module: ModuleId,
    errors: &mut Errors
) -> Option<Symbol> {
    let path_module = module;
    let (root, segments, last) = path.segments();
    let Some(last) = last else {
        errors.emit_span(Error::CantUseRootPath, path.span().in_mod(module));
        return None;
    };
    let mut module = if root { ModuleId::ROOT } else { module };
    // handle all but the last path segments to go to the correct module
    for segment in segments {
        let name = &ast.sources[path_module.idx()].0[segment.range()];
        if !update_path_module(ast, name, Span::new(segment.start, segment.end, path_module), &mut module, errors) {
            return None
        }
    }
    let last_str = &ast.sources[path_module.idx()].0[last.range()];
    resolve_in_module(ctx, ast, symbols, module, last, last_str, errors)
}

fn resolve(
    ctx: &mut TypingCtx,
    ast: &Ast,
    symbols: &mut [HashMap<String, Symbol>],
    path_module: ModuleId,
    unresolved: &UnresolvedType,
    errors: &mut Errors
) -> TypeRef {
    let src = &ast.sources()[path_module.idx()].0;
    match unresolved {
        crate::ast::UnresolvedType::Primitive(p, _) => TypeRef::Base(BaseType::Prim(*p)),
        crate::ast::UnresolvedType::Unresolved(path) => {
            let (root, segments, last) = path.segments();
            let Some(last) = last else {
                errors.emit_span(Error::TypeExpected, path.span().in_mod(path_module));
                return TypeRef::Invalid;
            };
            let mut module = if root { ModuleId::ROOT } else { path_module };
            for segment in segments {
                let name = &src[segment.range()];
                if !update_path_module(ast, name, segment.in_mod(path_module), &mut module, errors) {
                    return TypeRef::Invalid
                };
            }
            let last_str = &ast.sources()[module.idx()].0[last.range()];
            match resolve_in_module(ctx, ast, symbols, module, last, last_str, errors) {
                Some(Symbol::Type(ty)) => TypeRef::Base(BaseType::Id(ty)),
                Some(_) => {
                    errors.emit_span(Error::TypeExpected, last.in_mod(module));
                    TypeRef::Invalid
                }
                None => TypeRef::Invalid // an error was already emitted in this case
            }
        }
        UnresolvedType::Pointer(inner, _) => {
            match resolve(ctx, ast, symbols, path_module, inner, errors) {
                TypeRef::Base(inner) => TypeRef::Pointer { count: unsafe { NonZeroU8::new_unchecked(1) }, inner },
                TypeRef::Pointer { count, inner } => { 
                    if count.get() == u8::MAX {
                        errors.emit_span(Error::TooLargePointer, unresolved.span().in_mod(path_module));
                    }
                    TypeRef::Pointer { count: count.saturating_add(1), inner }
                }
                TypeRef::Invalid => TypeRef::Invalid,
            }
        }
        UnresolvedType::Infer(start) => {
            errors.emit(Error::InferredTypeNotAllowedHere, *start, *start, path_module);
            TypeRef::Invalid
        }
        
    }
}

fn resolve_in_module(
    ctx: &mut TypingCtx,
    ast: &Ast,
    symbols: &mut [HashMap<String, Symbol>],
    module: ModuleId,
    span: TSpan,
    name: &str,
    errors: &mut Errors
) -> Option<Symbol> {
    if let Some(symbol) = symbols[module.idx()].get(name) {
        Some(*symbol)
    } else if let Some(def) = ast.modules[module.idx()].definitions.get(name) {
        add_global_def(def, ctx, ast, symbols, module, name, errors)
    } else {
        errors.emit_span(Error::UnknownIdent, span.in_mod(module));
        None
    }
}