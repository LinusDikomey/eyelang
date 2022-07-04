use crate::{
    ast::{Ast, ModuleId, StructDefinition, self, UnresolvedType, IdentPath, TraitDefinition, EnumDefinition},
    error::{Errors, Error},
    ir::{gen::FunctionOrHeader, Type, ConstVal}, span::{Span, TSpan}, dmap::{self, DHashMap},
};
use super::{gen::{TypingCtx, Symbol}, SymbolKey, TypeDef, FunctionHeader, Scope};

#[derive(Clone, Debug)]
pub struct Globals(Vec<DHashMap<String, Symbol>>);
impl Globals {
    pub fn get_ref(&self) -> GlobalsRef {
        GlobalsRef(&self.0)
    }
}
impl Globals {
    pub fn iter(&self) -> impl Iterator<Item = (&String, &Symbol)> {
        self.0.iter().flat_map(|it| it.iter())
    }
}
impl std::ops::Index<ModuleId> for Globals {
    type Output = DHashMap<String, Symbol>;

    fn index(&self, index: ModuleId) -> &Self::Output {
        &self.0[index.idx()]
    }
}

/// For passing arround a reference to globals. More efficient than &Globals.
#[derive(Clone, Copy)]
pub struct GlobalsRef<'a>(&'a [DHashMap<String, Symbol>]);
impl std::ops::Index<ModuleId> for GlobalsRef<'_> {
    type Output = DHashMap<String, Symbol>;
    fn index(&self, index: ModuleId) -> &Self::Output {
        &self.0[index.idx()]
    }
}

pub fn gen_globals(ast: &Ast, ctx: &mut TypingCtx, errors: &mut Errors) -> Globals {
    let mut symbols = (0..ast.modules.len()).map(|_| dmap::new()).collect::<Vec<_>>();

    for (module_id, module) in ast.modules.iter().enumerate() {
        let module_id = ModuleId::new(module_id as u32);
        for (name, def) in &ast[module.definitions] {
            if symbols[module_id.idx()].contains_key(name) { continue }
            gen_def(def, module.definitions, module_id, name, errors,
                GlobalResolveState { symbols: &mut symbols, ctx, ast }
            );
        }
    }
    Globals(symbols)
}
pub fn gen_locals(
    scope: &mut Scope,
    defs: ast::Defs,
    errors: &mut Errors
) -> DHashMap<String, Symbol> {
    let mut symbols = dmap::with_capacity(scope.ast[defs].len());
    for (name, def) in &scope.ast[defs] {
        if symbols.contains_key(name) { continue }
        gen_def(def, defs, scope.module, name, errors,
            LocalResolveState { symbols: &mut symbols, scope: scope.reborrow(), defs }
        );
    }
    symbols
}

trait ResolveState {
    type Reborrowed<'me> : ResolveState where Self: 'me;
    fn reborrow(&mut self) -> Self::Reborrowed<'_>;
    fn ctx(&mut self) -> &mut TypingCtx;
    fn src(&self, module: ModuleId) -> &str;
    fn resolve_ty(&mut self, unresolved: &UnresolvedType, module: ModuleId, errors: &mut Errors) -> Type {
        resolve_ty(unresolved, module, errors, self.reborrow())
    }
    fn resolve_path(&mut self, path: &IdentPath, module: ModuleId, errors: &mut Errors) -> Option<Symbol>;
    fn insert_symbol(&mut self, module: ModuleId, name: String, symbol: Symbol) {
        let previous = self.replace_symbol(module, name.clone(), symbol);
        debug_assert!(previous.is_none(), "Duplicate symbol insertion '{name}' {previous:?}");
    }
    fn replace_symbol(&mut self, module: ModuleId, name: String, symbol: Symbol) -> Option<Symbol>;
    fn gen_func(&mut self, module: ModuleId, func: &ast::Function, errors: &mut Errors) -> FunctionHeader;
    fn scope(&mut self, module: ModuleId) -> Scope;
}
struct GlobalResolveState<'a> {
    symbols: &'a mut [DHashMap<String, Symbol>],
    ctx: &'a mut TypingCtx,
    ast: &'a Ast,
}
impl<'a> ResolveState for GlobalResolveState<'a> {
    type Reborrowed<'me> = GlobalResolveState<'me> where Self: 'me;
    fn reborrow(&mut self) -> GlobalResolveState {
        GlobalResolveState { symbols: &mut self.symbols, ctx: &mut self.ctx, ast: self.ast }
    }
    fn ctx(&mut self) -> &mut TypingCtx { self.ctx }
    fn src(&self, module: ModuleId) -> &str { &self.ast.sources()[module.idx()].0 }
    fn resolve_path(&mut self, path: &IdentPath, module: ModuleId, errors: &mut Errors) -> Option<Symbol> {
        resolve_global_path(path, self.ast, self.ctx, self.symbols, module, errors)
    }
    fn replace_symbol(&mut self, module: ModuleId, name: String, symbol: Symbol) -> Option<Symbol> {
        self.symbols[module.idx()].insert(name, symbol)
    }
    fn gen_func(&mut self, module: ModuleId, func: &ast::Function, errors: &mut Errors) -> FunctionHeader {
        gen_func(func, self.reborrow(), module, errors)   
    }
    fn scope(&mut self, module: ModuleId) -> Scope {
        Scope::new(self.ctx, &self.symbols[module.idx()], &self.ast[self.ast[module].definitions], 
            GlobalsRef(self.symbols), self.ast, module)
    }
}
struct LocalResolveState<'a, 's> {
    symbols: &'a mut DHashMap<String, Symbol>,
    scope: Scope<'s>,
    defs: ast::Defs,
}
impl<'a, 's> ResolveState for LocalResolveState<'a, 's> {
    type Reborrowed<'me> = LocalResolveState<'me, 'me> where Self: 'me;
    fn reborrow(&mut self) -> LocalResolveState {
        LocalResolveState { symbols: &mut *self.symbols, scope: self.scope.reborrow(), defs: self.defs }
    }
    fn ctx(&mut self) -> &mut TypingCtx { self.scope.ctx }
    fn src(&self, module: ModuleId) -> &str { &self.scope.ast.sources()[module.idx()].0 }
    fn resolve_path(&mut self, path: &IdentPath, _module: ModuleId, errors: &mut Errors) -> Option<Symbol> {
        resolve_local_path(path, &mut self.scope, self.symbols, self.defs, errors)
    }
    fn replace_symbol(&mut self, module: ModuleId, name: String, symbol: Symbol) -> Option<Symbol> {
        debug_assert_eq!(self.scope.module, module);
        self.symbols.insert(name, symbol)
    }
    fn gen_func(&mut self, module: ModuleId, func: &ast::Function, errors: &mut Errors) -> FunctionHeader {
        debug_assert_eq!(self.scope.module, module);
        gen_func(func, self.reborrow(), module, errors)
    }
    fn scope(&mut self, module: ModuleId) -> Scope {
        assert_eq!(self.scope.module, module);
        self.scope.reborrow()
    }
}
/// Resolve state inside a struct or function definition containing a prototype of the definition itself
/// and generic type parameters.
struct DefinitionResolveState<'a, R: ResolveState> {
    parent: R,
    generics: &'a DHashMap<String, u8>,
    module: ModuleId,
}
impl<'a, R: ResolveState> ResolveState for DefinitionResolveState<'a, R> {
    type Reborrowed<'r> = DefinitionResolveState<'r, R::Reborrowed<'r>> where Self: 'r;

    fn reborrow(&mut self) -> Self::Reborrowed<'_> {
        DefinitionResolveState {
            parent: self.parent.reborrow(),
            generics: self.generics,
            module: self.module,
        }
    }

    fn ctx(&mut self) -> &mut TypingCtx { self.parent.ctx() }
    fn src(&self, module: ModuleId) -> &str { self.parent.src(module) }
    fn resolve_path(&mut self, path: &IdentPath, module: ModuleId, errors: &mut Errors) -> Option<Symbol> {
        if let (None, mut segments, Some((last, _))) = path.segments(self.src(module)) {
            if segments.next().is_none() {
                if let Some(generic) = self.generics.get(last) {
                    return Some(Symbol::Generic(*generic));
                }
            }
        }
        self.parent.resolve_path(path, module, errors)
    }

    fn replace_symbol(&mut self, module: ModuleId, name: String, symbol: Symbol) -> Option<Symbol> {
        self.parent.replace_symbol(module, name, symbol)
    }

    fn gen_func(&mut self, module: ModuleId, func: &ast::Function, errors: &mut Errors) -> FunctionHeader {
        self.parent.gen_func(module, func, errors)
    }
    fn scope(&mut self, module: ModuleId) -> Scope {
        self.parent.scope(module)
    }
}

fn gen_def(
    def: &ast::Definition,
    defs: ast::Defs,
    module: ModuleId,
    name: &str,
    errors: &mut Errors,
    mut state: impl ResolveState,
) -> Option<Symbol> {
    let ret = Some(match def {
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
        ast::Definition::Enum(enum_) => {
            let key = gen_enum(enum_, name, module, errors, state.reborrow());
            Symbol::Type(key)
        }
        ast::Definition::Trait(trait_) => {
            let key = gen_trait(trait_, name, module, errors, state.reborrow());
            Symbol::Trait(key)
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
        ast::Definition::Const(_, _) => {
            let symbol = Symbol::Const(state.ctx().add_const(ConstVal::NotGenerated { defs, generating: false }));
            state.insert_symbol(module, name.to_owned(), symbol);
            symbol
        }
        ast::Definition::Global(ty, val) => {
            let ty = state.resolve_ty(ty, module, errors);
            assert!(val.is_none(), "TODO: Globals with initial values are unsupported right now");
            let symbol = Symbol::GlobalVar(state.ctx().add_global(ty, None));
            state.insert_symbol(module, name.to_owned(), symbol);
            symbol
        }
    });
    ret
}

fn resolve_ty(
    unresolved: &UnresolvedType,
    module: ModuleId,
    errors: &mut Errors,
    mut state: impl ResolveState,
) -> Type {
    match unresolved {
        UnresolvedType::Primitive(p, _) => Type::Prim(*p),
        UnresolvedType::Unresolved(path, generics) => {
            match state.resolve_path(path, module, errors) {
                Some(Symbol::Type(ty)) => {
                    let generic_count = state.ctx().get_type(ty).generic_count();
                    let resolved_generics = generics.as_ref()
                        .map_or(Vec::new(), |(generics, _)| {
                            generics.iter().map(|ty| resolve_ty(ty, module, errors, state.reborrow())).collect()
                        });
                    if generic_count as usize != resolved_generics.len() {
                        let span = generics.as_ref().map_or_else(|| path.span(), |(_, span)| *span);
                        errors.emit_span(
                            Error::InvalidGenericCount {
                                expected: generic_count,
                                found: resolved_generics.len() as u8
                            },
                            span.in_mod(module)
                        );
                        Type::Invalid
                    } else {
                        Type::Id(ty, resolved_generics)
                    }
                }
                Some(Symbol::Generic(idx)) => Type::Generic(idx),
                Some(Symbol::Const(key)) => {
                    let mut scope = state.scope(module);
                    let val = scope.get_or_gen_const(key, unresolved.span(), errors);
                    match val {
                        ConstVal::Invalid => Type::Invalid ,
                        ConstVal::Symbol(Symbol::Type(key))
                        => Type::Id(*key, vec![]),
                        _ => {
                            errors.emit_span(Error::TypeExpected, unresolved.span().in_mod(module));
                            Type::Invalid
                        }
                    }
                }
                Some(_) => {
                    errors.emit_span(Error::TypeExpected, path.span().in_mod(module));
                    Type::Invalid
                }
                None => Type::Invalid // an error was already emitted in this case
            }
        }
        UnresolvedType::Pointer(box (inner, _)) => {
            let pointer_ty = resolve_ty(inner, module, errors, state);
            Type::Pointer(Box::new(pointer_ty))
        }
        UnresolvedType::Array(box (inner, span, count)) => {
            let Some(count) = *count else {
                errors.emit_span(Error::ArraySizeCantBeInferredHere, span.in_mod(module));
                return Type::Invalid;
            };
            let elem_ty = resolve_ty(inner, module, errors, state);
            Type::Array(Box::new((elem_ty, count)))
        }
        UnresolvedType::Tuple(elems, _) => {
            let mut tuple_types = Vec::with_capacity(elems.len());
            for ty in elems {
                let ty = resolve_ty(ty, module, errors, state.reborrow());
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

fn gen_func(func: &ast::Function, mut state: impl ResolveState, module: ModuleId, errors: &mut Errors)
-> FunctionHeader {
    let params = func.params.iter()
        .map(|(name, unresolved, _, _)| {
            (name.clone(), state.resolve_ty(unresolved, module, errors))
        })
        .collect();
    let return_type = state.resolve_ty(&func.return_type, module, errors);

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
    mut state: impl ResolveState,
) -> SymbolKey {
    let key = state.ctx().add_proto_ty(name.to_owned(), def.generics.len() as u8);
    state.insert_symbol(module, name.to_owned(), Symbol::Type(key));
    let generics = def.generics.iter()
        .enumerate()
        .map(|(i, span)| (state.src(module)[span.range()].to_owned(), i as u8))
        .collect();

    let mut state = DefinitionResolveState {
        parent: state,
        generics: &generics,
        module
    };
    let members = def.members.iter().map(|(name, unresolved, _start, _end)| {(
        name.clone(),
        state.resolve_ty(unresolved, module, errors),
    )}).collect::<Vec<_>>();
    *state.ctx().get_type_mut(key) = TypeDef::Struct(super::Struct {
        members,
        methods: dmap::with_capacity(def.members.len()),
        generic_count: def.generics.len() as u8,
        name: name.to_owned(),
    });
    for (method_name, method) in &def.methods {
        let header = gen_func(method, state.reborrow(), module, errors);
        let method_key = state.ctx().add_func(super::gen::FunctionOrHeader::Header(header));

        // type is set to Struct above
        let TypeDef::Struct(struct_) = state.ctx().get_type_mut(key) else { unreachable!() };
        struct_.methods.insert(method_name.clone(), method_key);
    }
    key
}

fn gen_enum(
    def: &EnumDefinition,
    name: &str,
    module: ModuleId,
    _errors: &mut Errors,
    mut state: impl ResolveState,
) -> SymbolKey {
    let key = state.ctx().add_proto_ty(name.to_owned(), def.generics.len() as u8);
    state.insert_symbol(module, name.to_owned(), Symbol::Type(key));

    let _generics: Vec<_> = def.generics.iter()
        .enumerate()
        .map(|(i, span)| (state.src(module)[span.range()].to_owned(), i as u8))
        .collect();
    
    let variants = def.variants.iter()
        .enumerate()
        .map(|(idx, (_span, name))| (name.clone(), idx as u32))
        .collect();

    *state.ctx().get_type_mut(key) = TypeDef::Enum(super::Enum {
        variants,
        generic_count: def.generics.len() as u8,
    });

    key
}

fn gen_trait(
    def: &TraitDefinition,
    name: &str,
    module: ModuleId,
    errors: &mut Errors,
    state: impl ResolveState,
) -> SymbolKey {
    let mut state = DefinitionResolveState {
        parent: state,
        generics: &dmap::new(),
        module,
    };
    let functions = def.functions.iter()
        .enumerate()
        .map(|(i, (name, (_span, func)))| (name.clone(), (i as u32, state.gen_func(module, func, errors))))
        .collect();
    let key = state.ctx().add_trait(crate::ir::TraitDef { functions });
    state.insert_symbol(module, name.to_owned(), Symbol::Trait(key));
    key
}

enum PathResolveState<'a, 's> {
    Local(&'a mut Scope<'s>, &'a mut DHashMap<String, Symbol>, ast::Defs),
    Module(ModuleId, &'a Ast)
}
impl<'a> PathResolveState<'a, '_> {
    fn into_ast(self) -> &'a Ast {
        match self {
            Self::Local(scope, _, _) => scope.ast,
            Self::Module(_, ast) => ast,
        }
    }
}
enum PathResolveSymbols<'a> {
    Mutable(&'a Ast, &'a mut [DHashMap<String, Symbol>], &'a mut TypingCtx),
    Finished(GlobalsRef<'a>)
}
impl<'a> PathResolveSymbols<'a> {
    fn get<'b>(&'b mut self, module: ModuleId, name: &str, span: Span, errors: &mut Errors)
    -> Option<Symbol> {
        match self {
            PathResolveSymbols::Mutable(ast, symbols, ctx) => {
                if let Some(symbol) = symbols[module.idx()].get(name) {
                    Some(*symbol)
                } else if let Some(def) = ast[ast.modules[module.idx()].definitions].get(name) {
                    gen_def(def, ast.modules[module.idx()].definitions, module, name, errors,
                        GlobalResolveState { symbols, ctx, ast }
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
    errors: &mut Errors,
) -> Option<Symbol> {
    let (root, segments, last) = path.segments(src);
    if root.is_some() {
        state = PathResolveState::Module(ModuleId::ROOT, state.into_ast());
    }

    for (name, span) in segments {
        match state {
            PathResolveState::Local(scope, symbols, defs) => {
                match resolve_in_scope(name, span, scope, symbols, defs, errors) {
                    Some(Symbol::Module(new_module)) => state = PathResolveState::Module(new_module, scope.ast),
                    Some(_) => {
                        errors.emit_span(Error::ModuleExpected, span.in_mod(path_module));
                        return None;
                    }
                    None => return None
                }
            },
            PathResolveState::Module(id, ast) => {
                if let Some(def) = symbols.get(id, name, span.in_mod(path_module), errors) {
                    if let Symbol::Module(new_module) = def {
                        state = PathResolveState::Module(new_module, ast);
                    } else {
                        errors.emit_span(Error::ModuleExpected, span.in_mod(path_module));
                        return None;
                    }
                } else {
                    // an error was already emitted here
                    return None;
                }
            }
        }
    }

    if let Some((name, span)) = last {
        match state {
            PathResolveState::Local(scope, symbols, defs)
                => resolve_in_scope(name, span, scope, symbols, defs, errors),
            PathResolveState::Module(id, _) => {
                // an error was already emitted here if the symbol is None
                symbols.get(id, name, span.in_mod(path_module), errors)
            }
        }
    } else {
        match state {
            PathResolveState::Local(_, _, _) => unreachable!(),
            PathResolveState::Module(id, _ast) => Some(Symbol::Module(id))
        }
    }
}

fn resolve_global_path(
    path: &IdentPath,
    ast: &Ast,
    ctx: &mut TypingCtx,
    symbols: &mut [DHashMap<String, Symbol>],
    module: ModuleId,
    errors: &mut Errors
) -> Option<Symbol> {
    resolve_path(
        path,
        PathResolveSymbols::Mutable(ast, symbols, ctx),
        PathResolveState::Module(module, ast),
        module,
        ast.src(module).0,
        errors,
    )
}

fn resolve_local_path(
    path: &IdentPath,
    scope: &mut Scope,
    symbols: &mut DHashMap<String, Symbol>,
    defs: ast::Defs,
    errors: &mut Errors,
) -> Option<Symbol> {
    let module = scope.module;
    let src = scope.ast.src(module).0;

    resolve_path(
        path,
        PathResolveSymbols::Finished(scope.globals),
        PathResolveState::Local(scope, symbols, defs),
        module,
        src,
        errors,
    )
}

fn resolve_in_scope(
    name: &str,
    span: TSpan,
    scope: &mut Scope,
    symbols: &mut DHashMap<String, Symbol>,
    defs: ast::Defs,
    errors: &mut Errors,
) -> Option<Symbol> {
    if let Some(symbol) = symbols.get(name) {
        Some(*symbol)
    } else if let Some(def) = scope.ast[defs].get(name) {
        gen_def(def, defs, scope.module, name, errors,
            LocalResolveState { symbols, scope: scope.reborrow(), defs }
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
