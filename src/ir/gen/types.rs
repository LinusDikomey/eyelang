use std::collections::HashMap;
use crate::{
    ast::{Ast, ModuleId, StructDefinition, self, UnresolvedType, IdentPath, TraitDefinition, ExprRef},
    error::{Errors, Error, EyeResult, CompileError},
    ir::{gen::FunctionOrHeader, Type, ConstVal}, span::{Span, TSpan}, lexer::tokens::Operator,
};
use super::{gen::{TypingCtx, Symbol}, SymbolKey, TypeDef, FunctionHeader, Scope, string_literal};

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
            gen_def(def, module_id, name, errors, ast,
                GlobalResolveState { symbols: &mut symbols, ctx, ast }
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
        gen_def(def, scope.module, name, errors, scope.ast,
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
    symbols: &'a mut [HashMap<String, Symbol>],
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
        Scope::new(self.ctx, &self.symbols[module.idx()], GlobalsRef(self.symbols), self.ast, module)
    }
}
struct LocalResolveState<'a, 's> {
    symbols: &'a mut HashMap<String, Symbol>,
    scope: Scope<'s>,
    defs: &'a HashMap<String, ast::Definition>,
}
impl<'a, 's> ResolveState for LocalResolveState<'a, 's> {
    type Reborrowed<'me> = LocalResolveState<'me, 'me> where Self: 'me;
    fn reborrow(&mut self) -> LocalResolveState {
        LocalResolveState { symbols: &mut *self.symbols, scope: self.scope.reborrow(), defs: &*self.defs }
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
    generics: &'a HashMap<String, u8>,
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
    module: ModuleId,
    name: &str,
    errors: &mut Errors,
    ast: &Ast,
    mut state: impl ResolveState,
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
        ast::Definition::Const(ty, expr) => {
            let val = match const_resolve(Some(ty), *expr, module, ast, state.reborrow()) {
                Ok(val) => val,
                Err(err) => {
                    errors.emit_err(err);
                    ConstVal::Invalid
                }
            };
            let symbol = Symbol::Const(state.ctx().add_const(val));
            state.insert_symbol(module, name.to_owned(), symbol);
            symbol
        }
    })
}

fn const_resolve(ty: Option<&UnresolvedType>, val: ExprRef, module: ModuleId, ast: &Ast, mut state: impl ResolveState)
-> EyeResult<ConstVal> {
    #![allow(unused)]
    let expr = &ast[val];
    Ok(match expr {
        // ast::Expr::Block { span, items, defs } => todo!(),
        // ast::Expr::Declare { name, annotated_ty, end } => todo!(),
        // ast::Expr::DeclareWithVal { name, annotated_ty, val } => todo!(),
        // ast::Expr::Return { start, val } => todo!(),
        ast::Expr::IntLiteral(span) => ConstVal::Int(state.src(module)[span.range()].parse().unwrap()),
        ast::Expr::FloatLiteral(span) => ConstVal::Float(state.src(module)[span.range()].parse().unwrap()),
        ast::Expr::StringLiteral(span) => ConstVal::String(string_literal(*span, state.src(module))),
        ast::Expr::BoolLiteral { start, val } => ConstVal::Bool(*val),
        ast::Expr::EnumLiteral { dot, ident } => ConstVal::EnumVariant(state.src(module)[ident.range()].to_owned()),
        ast::Expr::Nested(_, inner) => const_resolve(ty, *inner, module, ast, state)?,
        ast::Expr::Unit(_) => ConstVal::Unit,
        // ast::Expr::Variable(span) => todo!(),
        // ast::Expr::Array(_, _) => todo!(),
        // ast::Expr::Tuple(_, _) => todo!(),
        ast::Expr::If { .. }
        | ast::Expr::IfElse { .. }
        | ast::Expr::While { .. }
        | ast::Expr::FunctionCall { .. }
        => return Err(CompileError::new(Error::NotConst, expr.span_in(ast, module))),
        ast::Expr::UnOp(_, op, inner) => {
            let val = const_resolve(ty, *inner, module, ast, state)?;
            match op {
                ast::UnOp::Neg => {
                    let ConstVal::Int(int_val) = val else {
                        return Err(CompileError::new(Error::CantNegateType, ast[*inner].span_in(ast, module)));
                    };
                    ConstVal::Int(-int_val)
                }
                ast::UnOp::Not => {
                    let ConstVal::Bool(bool_val) = val else {
                        return Err(CompileError::new(Error::UnexpectedType, ast[*inner].span_in(ast, module)));
                    };
                    ConstVal::Bool(!bool_val)
                }
                ast::UnOp::Ref | ast::UnOp::Deref => return Err(CompileError::new(
                    Error::UnexpectedType, expr.span_in(ast, module))),
            }
        }
        ast::Expr::BinOp(op, l, r) => {
            let l_val = const_resolve(None, *l, module, ast, state.reborrow())?;
            let r_val = const_resolve(None, *r, module, ast, state)?;

            match op {
                Operator::Assignment(_) => {
                    return Err(CompileError::new(
                        Error::NotConst, expr.span_in(ast, module)
                    ));
                }
                Operator::Add | Operator::Sub | Operator::Mul | Operator::Div | Operator::Mod => {
                    macro_rules! math_op {
                        ($($tok: ident $t: tt),*) => {
                            match op {
                                $(
                                    Operator::$tok => {
                                        match (l_val, r_val) {
                                            (ConstVal::Invalid, ConstVal::Invalid) => ConstVal::Invalid,
                                            (ConstVal::Int(l), ConstVal::Int(r)) => ConstVal::Int(l $t r),
                                            (ConstVal::Float(l), ConstVal::Float(r)) => ConstVal::Float(l $t r),
                                            _ => {
                                                return Err(CompileError::new(
                                                    Error::MismatchedType, expr.span_in(ast, module)
                                                ));
                                            }
                                        }
                                    }
                                )*
                                _ => unreachable!()
                            }
                        };
                    }
                    math_op!(Add +, Sub -, Mul *, Div /, Mod %)
                }
                Operator::And | Operator::Or => {
                    let ConstVal::Bool(l) = l_val else { return Err(CompileError::new(
                        Error::UnexpectedType, ast[*l].span_in(ast, module))) };
                    let ConstVal::Bool(r) = r_val else { return Err(CompileError::new(
                        Error::UnexpectedType, ast[*r].span_in(ast, module))) };
                    ConstVal::Bool(match op {
                        Operator::Or => l | r,
                        Operator::And => l | r,
                        op => unreachable!()
                    })
                }
                Operator::Equals => ConstVal::Bool(l_val == r_val),
                Operator::NotEquals => ConstVal::Bool(l_val != r_val),
                Operator::LT | Operator::GT | Operator::LE | Operator::GE | Operator::Equals => {
                    macro_rules! cmp_ops {
                        ($($op: ident $t: tt $eq: expr),*) => {
                            match op {
                                $(
                                    Operator::$op => ConstVal::Bool(match (l_val, r_val) {
                                        (ConstVal::Invalid, ConstVal::Invalid) => return Ok(ConstVal::Invalid),
                                        (ConstVal::Unit, ConstVal::Unit) => $eq,
                                        (ConstVal::Int(l), ConstVal::Int(r)) => l $t r,
                                        (ConstVal::Float(l), ConstVal::Float(r)) => l $t r,
                                        (ConstVal::Bool(l), ConstVal::Bool(r)) => l $t r,
                                        _ => {
                                            return Err(CompileError::new(
                                                Error::MismatchedType, expr.span_in(ast, module)
                                            ));
                                        }
                                    }),
                                )*
                                _ => unreachable!()
                            }
                        };
                    }
                    cmp_ops!{
                        LT < false,
                        GT > false,
                        LE <= true,
                        GE >= true,
                        Equals == true
                    }
                }
            }
        }
        // ast::Expr::MemberAccess { left, name } => todo!(),
        // ast::Expr::TupleIdx { expr, idx, end } => todo!(),
        // ast::Expr::Cast(_, _, _) => todo!(),
        // ast::Expr::Root(_) => todo!(),
        _ => return Err(CompileError::new(Error::NotConst, expr.span_in(ast, module)))
    })
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
    let key = state.ctx().add_proto_ty(def.generics.len() as u8);
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
        methods: HashMap::with_capacity(def.members.len()),
        generic_count: def.generics.len() as u8,
        name: name.to_owned(),
    });
    for (method_name, method) in &def.methods {
        let header = gen_func(method, state.reborrow(), module, errors);
        let method_key = state.ctx().add_func(super::gen::FunctionOrHeader::Header(header));

        // type is set to Struct above
        let TypeDef::Struct(struct_) = state.ctx().get_type_mut(key);
        struct_.methods.insert(method_name.clone(), method_key);
    }
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
        generics: &HashMap::new(),
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

enum PathResolveState<'a, 's, 'd> {
    Local(&'a mut Scope<'s>, &'a mut HashMap<String, Symbol>, &'d HashMap<String, ast::Definition>),
    Module(ModuleId, &'a Ast)
}
impl<'a> PathResolveState<'a, '_, '_> {
    fn into_ast(self) -> &'a Ast {
        match self {
            Self::Local(scope, _, _) => scope.ast,
            Self::Module(_, ast) => ast,
        }
    }
}
enum PathResolveSymbols<'a> {
    Mutable(&'a Ast, &'a mut [HashMap<String, Symbol>], &'a mut TypingCtx),
    Finished(GlobalsRef<'a>)
}
impl<'a> PathResolveSymbols<'a> {
    fn get<'b>(&'b mut self, module: ModuleId, name: &str, span: Span, errors: &mut Errors)
    -> Option<Symbol> {
        match self {
            PathResolveSymbols::Mutable(ast, symbols, ctx) => {
                if let Some(symbol) = symbols[module.idx()].get(name) {
                    Some(*symbol)
                } else if let Some(def) = ast.modules[module.idx()].definitions.get(name) {
                    gen_def(def, module, name, errors, ast,
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
                match resolve_in_scope(name, span, scope, symbols, defs, errors, scope.ast) {
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
                => resolve_in_scope(name, span, scope, symbols, defs, errors, scope.ast),
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
    symbols: &mut [HashMap<String, Symbol>],
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
    symbols: &mut HashMap<String, Symbol>,
    defs: &HashMap<String, ast::Definition>,
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
    symbols: &mut HashMap<String, Symbol>,
    defs: &HashMap<String, ast::Definition>,
    errors: &mut Errors,
    ast: &Ast,
) -> Option<Symbol> {
    if let Some(symbol) = symbols.get(name) {
        Some(*symbol)
    } else if let Some(def) = defs.get(name) {
        gen_def(def, scope.module, name, errors, ast,
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
