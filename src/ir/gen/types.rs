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
            if symbols[module_id.idx()].contains_key(name) { continue }
            gen_ty(def, module_id, &name, errors,
                TypegenResolveState::Global { symbols: &mut symbols, ctx, ast }
            );
        }
    }
    Globals(symbols)
}
pub fn gen_locals(
    scope: &mut Scope,
    defs: &HashMap<String, ast::Definition>,
    errors: &mut Errors
) -> HashMap<String, Symbol> {
    let mut symbols = HashMap::with_capacity(defs.len());
    for (name, def) in defs {
        if symbols.contains_key(name) { continue }
        gen_ty(def, scope.module, name, errors,
            TypegenResolveState::Local { symbols: &mut symbols, scope: scope.reborrow(), defs }
        );
    }
    symbols
}

enum TypegenResolveState<'a, 's> {
    Global {
        symbols: &'a mut [HashMap<String, Symbol>],
        ctx: &'a mut TypingCtx,
        ast: &'a Ast,
    },
    Local {
        symbols: &'a mut HashMap<String, Symbol>,
        scope: Scope<'s>,
        defs: &'a HashMap<String, ast::Definition>,
    }
}
impl<'a, 's> TypegenResolveState<'a, 's> {
    fn reborrow<'me>(&'me mut self) -> TypegenResolveState<'me, 'me> {
        match self {
            TypegenResolveState::Global { symbols, ctx, ast } 
            => TypegenResolveState::Global { symbols: &mut *symbols, ctx: &mut *ctx, ast: &*ast },
            TypegenResolveState::Local { symbols, scope, defs }
            => TypegenResolveState::Local { symbols: &mut *symbols, scope: scope.reborrow(), defs: &*defs },
        }
    }
    fn ctx(&mut self) -> &mut TypingCtx {
        match self {
            Self::Global { ctx, .. } => ctx,
            Self::Local { scope, .. } => scope.ctx
        }
    }
    fn resolve_ty(&mut self, unresolved: &UnresolvedType, module: ModuleId, errors: &mut Errors) -> Type {
        match self {
            TypegenResolveState::Global { symbols, ctx, ast }
            => resolve_ty(unresolved, module, errors,
                &mut |path, errors| resolve_global_path(path, ast, *ctx, *symbols, module, errors)
            ),
            TypegenResolveState::Local { symbols, scope, defs }
            => resolve_ty(unresolved, module, errors,
                &mut |path, errors| resolve_local_path(path, scope, *symbols, *defs, errors)
            )
        }
    }
    fn resolve_path(&mut self, path: &IdentPath, module: ModuleId, errors: &mut Errors) -> Option<Symbol> {
        match self {
            TypegenResolveState::Global { symbols, ctx, ast }
            => resolve_global_path(path, ast, ctx, symbols, module, errors),
            TypegenResolveState::Local { symbols, scope, defs }
            => resolve_local_path(path, scope, symbols, defs, errors),
        }
    }
    fn insert_symbol(&mut self, module: ModuleId, name: String, symbol: Symbol) {
        let previous = match self {
            Self::Global { symbols, .. } => symbols[module.idx()].insert(name.clone(), symbol),
            Self::Local { scope, symbols, .. } => {
                debug_assert_eq!(scope.module, module);
                symbols.insert(name.clone(), symbol)
            }
        };
        debug_assert!(previous.is_none(), "Duplicate symbol insertion '{name}' {previous:?}");
    }
    fn gen_func(&mut self, module: ModuleId, func: &ast::Function, errors: &mut Errors) -> FunctionHeader {
        match self {
            TypegenResolveState::Global { symbols, ctx, ast } => gen_func(func,
                |ty| resolve_ty(
                    ty, module, errors,
                    &mut |path, errors| resolve_global_path(path, ast, ctx, symbols, module, errors),
                )
            ),
            TypegenResolveState::Local { symbols, scope, defs } => {
                debug_assert_eq!(scope.module, module);
                gen_func(func, |ty| resolve_ty(
                    ty, module, errors,
                    &mut |path, errors| resolve_local_path(path, scope, symbols, defs, errors),
                ))
            }
        }
        
    }
}

fn gen_ty(
    def: &ast::Definition,
    //ast: &Ast,
    module: ModuleId,
    name: &str,
    errors: &mut Errors,
    mut state: TypegenResolveState,
) -> Option<Symbol> {
    Some(match def {
        ast::Definition::Function(func) => {
            let header = state.gen_func(module, func, errors);
            let key = state.ctx().add_func(FunctionOrHeader::Header(header));
            state.insert_symbol(module, name.to_owned(), Symbol::Func(key));
            Symbol::Func(key)
        }
        ast::Definition::Struct(struct_) => {
            let key = gen_struct(struct_, name, module, errors, state.reborrow());
            Symbol::Type(key)
        }
        ast::Definition::Module(inner_module) => {
            state.insert_symbol(module, name.to_owned(), Symbol::Module(*inner_module));
            Symbol::Module(*inner_module)
        }
        ast::Definition::Use(path) => {
            if let Some(symbol) = state.resolve_path(path, module, errors) {
                state.insert_symbol(module, name.to_owned(), symbol);
                symbol
            } else {
                return None;
            }
        }
    })
}

fn resolve_ty<PathResolve: FnMut(&IdentPath, &mut Errors) -> Option<Symbol>>(
    unresolved: &UnresolvedType,
    module: ModuleId,
    errors: &mut Errors,
    path_resolve: &mut PathResolve,
) -> Type {
    match unresolved {
        UnresolvedType::Primitive(p, _) => Type::Prim(*p),
        UnresolvedType::Unresolved(path) => {
            match path_resolve(path, errors) {
                Some(Symbol::Type(ty)) => Type::Id(ty),
                Some(_) => {
                    errors.emit_span(Error::TypeExpected, path.span().in_mod(module));
                    Type::Invalid
                }
                None => Type::Invalid // an error was already emitted in this case
            }

        }
        UnresolvedType::Pointer(box (inner, _)) => {
            let pointer_ty = resolve_ty(inner, module, errors, path_resolve);
            Type::Pointer(Box::new(pointer_ty))
        }
        UnresolvedType::Array(box (inner, span, count)) => {
            let Some(count) = *count else {
                errors.emit_span(Error::ArraySizeCantBeInferredHere, span.in_mod(module));
                return Type::Invalid;
            };
            let elem_ty = resolve_ty(inner, module, errors, path_resolve);
            Type::Array(Box::new((elem_ty, count)))
        }
        UnresolvedType::Tuple(elems, _) => {
            let mut tuple_types = Vec::with_capacity(elems.len());
            for ty in elems {
                let ty = resolve_ty(ty, module, errors, path_resolve);
                tuple_types.push(ty);
            }
            Type::Tuple(tuple_types)
        }
        UnresolvedType::Infer(start) => {
            errors.emit(Error::InferredTypeNotAllowedHere, *start, *start, module);
            Type::Invalid
        }
    }
}

fn gen_func<'a>(func: &ast::Function, mut resolve_ty_func: impl FnMut(&UnresolvedType) -> Type)
-> FunctionHeader {
    let params = func.params.iter()
        .map(|(name, unresolved, _, _)| {
            (name.clone(), resolve_ty_func(unresolved))
        })
        .collect();
    let return_type = resolve_ty_func(&func.return_type);

    FunctionHeader {
        params,
        varargs: func.varargs,
        return_type,
    }
}

fn gen_struct(
    def: &StructDefinition,
    name: &str,
    module: ModuleId,
    errors: &mut Errors,
    mut state: TypegenResolveState,
) -> SymbolKey {
    let members = def.members.iter().map(|(name, unresolved, _start, _end)| {(
        name.clone(),
        state.resolve_ty(unresolved, module, errors),
    )}).collect::<Vec<_>>();
    let key = state.ctx().add_type(TypeDef::Struct(super::Struct {
        members,
        methods: HashMap::with_capacity(def.members.len()),
        name: name.to_owned(),
    }));
    state.insert_symbol(module, name.to_owned(), Symbol::Type(key));
    for (method_name, method) in &def.methods {
        let header = gen_func(method, |ty| state.resolve_ty(ty, module, errors));
        let method_key = state.ctx().add_func(super::gen::FunctionOrHeader::Header(header));
        let TypeDef::Struct(struct_) = state.ctx().get_type_mut(key);
        struct_.methods.insert(method_name.clone(), method_key);
    }
    key
}

enum PathResolveState<'a, 's, 'd> {
    Local(&'a mut Scope<'s>, &'a mut HashMap<String, Symbol>, &'d HashMap<String, ast::Definition>),
    Module(ModuleId)
}
enum PathResolveSymbols<'a> {
    Mutable(&'a Ast, &'a mut [HashMap<String, Symbol>], &'a mut TypingCtx),
    Finished(GlobalsRef<'a>)
}
impl<'a> PathResolveSymbols<'a> {
    fn get<'b>(&'b mut self, module: ModuleId, name: &str, span: Span, errors: &mut Errors) -> Option<Symbol> {
        match self {
            PathResolveSymbols::Mutable(ast, symbols, ctx) => {
                if let Some(symbol) = symbols[module.idx()].get(name) {
                    Some(*symbol)
                } else  if let Some(def) = ast.modules[module.idx()].definitions.get(name) {
                    gen_ty(def, module, name, errors,
                        TypegenResolveState::Global { symbols, ctx, ast }
                    )
                } else {
                    errors.emit_span(Error::UnknownIdent, span);
                    None
                }
            }
            PathResolveSymbols::Finished(symbols) => {
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
    mut symbols: PathResolveSymbols,
    mut state: PathResolveState,
    path_module: ModuleId,
    src: &str,
    errors: &mut Errors
) -> Option<Symbol> {
    let (root, segments, last) = path.segments(src);
    if root.is_some() {
        state = PathResolveState::Module(ModuleId::ROOT);
    }

    for (name, span) in segments {
        match state {
            PathResolveState::Local(scope, symbols, defs) => {
                match resolve_in_scope(name, span, scope, symbols, defs, errors) {
                    Some(Symbol::Module(new_module)) => state = PathResolveState::Module(new_module),
                    Some(_) => {
                        errors.emit_span(Error::ModuleExpected, span.in_mod(path_module));
                        return None;
                    }
                    None => return None
                }
            },
            PathResolveState::Module(id) => {
                if let Some(def) = symbols.get(id, name, span.in_mod(path_module), errors) {
                    if let Symbol::Module(new_module) = def {
                        state = PathResolveState::Module(new_module);
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
            PathResolveState::Local(scope, symbols, defs)
                => resolve_in_scope(name, span, scope, symbols, defs, errors),
            PathResolveState::Module(id) => {
                let symbol = symbols.get(id, name, span.in_mod(path_module), errors);
                if symbol.is_none() {
                    errors.emit_span(Error::UnknownIdent, span.in_mod(path_module));
                }
                symbol
            }
        }
    } else {
        match state {
            PathResolveState::Local(_, _, _) => unreachable!(),
            PathResolveState::Module(id) => Some(Symbol::Module(id))
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
        PathResolveSymbols::Mutable(ast, symbols, ctx),
        PathResolveState::Module(module),
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
        PathResolveSymbols::Finished(scope.globals),
        PathResolveState::Local(scope, symbols, defs),
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
        gen_ty(def, scope.module, name, errors,
            TypegenResolveState::Local { symbols: symbols, scope: scope.reborrow(), defs }
        )
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
