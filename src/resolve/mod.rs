use crate::{
    ast::{self, ModuleId, Definition, ExprRef, Ast, TypeDef, FunctionId, TypeId, GlobalId, ConstId, VariantId},
    error::{Errors, Error},
    dmap::{DHashMap, self},
    span::{Span, TSpan},
    parser::IdentId,
    resolve::types::ResolvedFunc,
    types::Primitive,
    irgen, ir::types::{TypeRef, TypeRefs},
};

use self::{
    types::{DefId, Type, SymbolTable, FunctionHeader, Struct, ResolvedTypeDef, Enum},
    type_info::{TypeTable, TypeInfo, TypeInfoOrIndex},
    scope::{ModuleCtx, Scope, ExprInfo, UnresolvedDefId, Scopes, ScopeId},
    const_val::ConstVal, expr::val_expr, std_builtins::Builtins, exhaust::Exhaustion
};

pub mod const_val;
mod scope;
pub mod std_builtins;
pub mod types;
pub mod type_info;
mod expr;
mod pat;
mod exhaust;

pub fn resolve_project(
    ast: &Ast,
    main_module: ModuleId,
    errors: &mut Errors,
    require_main: bool,
    std: Option<ModuleId>
) -> (SymbolTable, irgen::Functions, Option<FunctionId>) {
    let mut ir_functions = irgen::Functions::new();

    let prelude = std.map(|std| {
        let Some(Definition::Module(prelude)) = ast[ast[std].definitions].get("prelude") else {
            panic!("prelude module not found in std library")
        };
        *prelude
    });

    // Add ids for definitions. Definitions that will have to be cross-resolved (use, const) are left as Unresolved
    let module_scopes: Vec<_> = ast.modules.iter().enumerate().map(|(i, module)| {
        let module_id = ModuleId::new(i as _);
        let module_ctx = ModuleCtx { src: ast.src(module_id).0, id: module_id, root: module.root_module };
        let names = scope_defs(&ast[module.definitions]);
        let prelude = prelude.and_then(|prelude| (module_id != prelude).then_some(prelude));
        Scope::root(names, module_ctx, prelude)
    }).collect();   
    
    let mut scopes = Scopes::new(module_scopes);

    let builtins = if let Some(std) = std {
        Builtins::resolve(&mut scopes, std, ast)
    } else {
        Builtins::nostd()
    };

    let mut symbols = SymbolTable::new(
        builtins,
        ast.functions.len(),
        ast.expr_count(),
        &ast.types,
        ast.traits.len(),
        ast.calls.len(),
        ast.globals.len(),
        ast.member_access_count as usize,
    );

    // resolve types, function signatures
    for (i, module) in ast.modules.iter().enumerate() {
        let scope = ScopeId::module(ModuleId::new(i as _));
        for (name, def) in &ast[module.definitions] {
            resolve_def(name, def, ast, &mut symbols, &mut scopes, scope, errors, &mut ir_functions);
        }
    }

    let main = require_main.then_some(()).and_then(|()| {
        if let Some(&UnresolvedDefId::Resolved(DefId::Function(id))) = scopes[ScopeId::module(main_module)].get_def("main") {
            let main = symbols.get_func(id);
            if main.varargs || main.params.len() != 0 {
                errors.emit_span(Error::MainArgs, ast.functions[id.idx()].span.in_mod(main_module));
            }
            match main.return_type {
                Type::Prim(p) if p.is_int() => {}
                Type::Prim(Primitive::Unit) => {}
                _ => errors.emit_span(
                    Error::InvalidMainReturnType("TODO: show type here".to_owned()),
                    ast.functions[id.idx()].return_type.span().in_mod(main_module)
                )
            }
            Some(id)
        } else {
            errors.emit_span(Error::MissingMain, Span::new(0, 0, main_module));
            None
        }
    });

    // function bodies
    for (i, module) in ast.modules.iter().enumerate() {
        let scope = ScopeId::module(ModuleId::new(i as _));
        scope_bodies(&mut scopes, scope, &ast[module.definitions], &ast, &mut symbols, errors, &mut ir_functions);
    }

    (symbols, ir_functions, main)
    
}

/// add all order independent definitions to a scope
fn scope_defs<'a>(defs: &'a DHashMap<String, Definition>,) -> DHashMap<String, UnresolvedDefId> {
    defs.iter().map(|(name, def)| {
        let def_id = match def {
            &Definition::Function(id) => UnresolvedDefId::Resolved(DefId::Function(id)),
            &Definition::Type(id) => UnresolvedDefId::Resolved(DefId::Type(id)),
            &Definition::Trait(id) => UnresolvedDefId::Resolved(DefId::Trait(id)),
            &Definition::Module(id) => UnresolvedDefId::Resolved(DefId::Module(id)),
            &Definition::Use(path) => UnresolvedDefId::Use(path),
            Definition::Const { ty, val, counts } => UnresolvedDefId::Const {
                expr: *val,
                ty: ty.clone(),
                counts: *counts,
            },
            &Definition::Global(id) => UnresolvedDefId::Resolved(DefId::Global(id)),
        };
        (name.clone(), def_id)
    }).collect()
}

fn scope_bodies(
    scopes: &mut Scopes,
    scope: ScopeId,
    defs: &DHashMap<String, Definition>,
    ast: &Ast,
    symbols: &mut SymbolTable,
    errors: &mut Errors,
    ir_functions: &mut irgen::Functions
) {

    fn gen_func_body(
        id: FunctionId,
        scopes: &mut Scopes,
        scope: ScopeId,
        generics_ctx: &[String],
        ast: &Ast,
        symbols: &mut SymbolTable,
        errors: &mut Errors,
        ir_functions: &mut irgen::Functions
    ) {
        
        let func = &ast[id];
        if let Some(body) = func.body {
            let generic_count = symbols.get_func(id).generic_count();
        
            let mut types = TypeTable::new(generic_count);
            let mut vars = vec![];
            let mut idents = vec![Ident::Invalid; func.counts.idents as usize];
            let mut exhaustions = Vec::new();
            func_body(body, id, generics_ctx, Ctx {
                scopes,
                scope,
                ast,
                symbols,
                types: &mut types,
                idents: &mut idents,
                vars: &mut vars,
                errors,
                ir: ir_functions,
                exhaustions: &mut exhaustions,
            });

            for (exhaustion, ty, span) in exhaustions {
                let Some(exhausted) = exhaustion.is_exhausted(types[ty], &mut types, symbols) else {
                    errors.emit_span(
                        Error::Internal(format!("exhaustion type mismatch: {:?}", types[ty])),
                        span.in_mod(scopes[scope].module.id)
                    );
                    continue
                };
                if !exhausted {
                    errors.emit_span(Error::Inexhaustive, span.in_mod(scopes[scope].module.id));
                }
            }

            symbols.get_func_mut(id).resolved_body = Some(ResolvedFunc {
                body,
                idents,
                vars,
                types,
            })
        }
    }

    for (_name, def) in defs {
        match def {
            Definition::Function(func_id) => gen_func_body(*func_id, scopes, scope, &[], ast, symbols, errors, ir_functions),
            Definition::Type(id) => {
                match symbols.get_type(*id) {
                    ResolvedTypeDef::Struct(def) => {
                        // PERF: cloning generics here
                        let generics = def.generics.clone();
                        // PERF: collecting here (ownership reasons)
                        for method_id in def.methods.values().copied().collect::<Vec<_>>() {
                            gen_func_body(method_id, scopes, scope, &generics, ast, symbols, errors, ir_functions);
                        }
                        
                    }
                    ResolvedTypeDef::Enum(_) => {}
                }
                
            }
            Definition::Trait(_) | Definition::Module(_) | Definition::Use(_)
            | Definition::Const { .. } | Definition::Global(_) => {}
        }
    }
}

fn resolve_def(
    name: &str,
    def: &Definition,
    ast: &Ast,
    symbols: &mut SymbolTable,
    scopes: &mut Scopes,
    scope: ScopeId,
    errors: &mut Errors,
    ir: &mut irgen::Functions,
) {
    match def {
        &Definition::Function(id) => {
            let header = func_signature(name.to_owned(), 0, &ast[id], scopes, scope, symbols, errors, ast, ir);
            symbols.place_func(id, header);
        }
        &Definition::Type(id) => {
            let def = match &ast[id] {
                TypeDef::Struct(s) => ResolvedTypeDef::Struct(
                    struct_def(name.to_owned(), s, scopes, scope, ast, symbols, errors, ir)
                ),
                TypeDef::Enum(e) => ResolvedTypeDef::Enum(
                    enum_def(name.to_owned(), e, scopes, scope, ast, symbols, errors, ir)
                ),
            };
            symbols.place_type(id, def);
        }
        &Definition::Global(id) => {
            let def = &ast[id];
            let (ty, val) = global(def, ast, scopes, scope, symbols, errors, ir);
            symbols.place_global(id, name.to_owned(), ty, val);
        }
        Definition::Trait(_)
        | Definition::Module(_)
        | Definition::Use(_)
        | Definition::Const { .. } => {}
    }
}

fn func_signature(
    name: String,
    inherited_generics_count: u8,
    func: &ast::Function,
    scopes: &mut Scopes,
    scope: ScopeId,
    symbols: &mut SymbolTable,
    errors: &mut Errors,
    ast: &Ast,
    ir: &mut irgen::Functions,
) -> FunctionHeader {
    let generics: Vec<String> = func.generics
        .iter()
        .map(|span| scopes[scope].module.src()[span.range()].to_owned())
        .collect();

    let generic_defs = generics
        .iter()
        .enumerate()
        .map(|(i, name)| (name.clone(), UnresolvedDefId::Resolved(DefId::Generic(i as u8))))
        .collect();
    let scope = scopes.child(scope, generic_defs, dmap::new(), false);

    let params = func.params.iter().map(|(name, ty, _, _)| {
        (name.clone(), scopes.resolve_ty(scope, ty, errors, symbols, ast, ir))
    }).collect();

    let return_type = scopes.resolve_ty(scope, &func.return_type, errors, symbols, ast, ir);

    FunctionHeader {
        name,
        inherited_generic_count: inherited_generics_count,
        generics,
        params,
        return_type,
        varargs: func.varargs,
        resolved_body: None,
        module: scopes[scope].module.id,
    }
}

fn struct_def(
    name: String,
    def: &ast::StructDefinition,
    scopes: &mut Scopes,
    scope: ScopeId,
    ast: &Ast,
    symbols: &mut SymbolTable,
    errors: &mut Errors,
    ir: &mut irgen::Functions
) -> Struct {    
    let scope = generic_scope(&def.generics, scopes, scope, ast);
    
    let members = def.members.iter().map(|(name, ty, _, _)| {
        (name.clone(), scopes.resolve_ty(scope, ty, errors, symbols, ast, ir))
    }).collect();

    let symbols = def.methods.iter().map(|(name, id)| {
        let header = func_signature(name.to_owned(), def.generic_count(), &ast[*id], scopes, scope, symbols, errors, ast, ir);
        symbols.place_func(*id, header);
        (name.clone(), *id)
    }).collect();

    let generics = def.generics
        .iter()
        .map(|name_span| ast.src(scopes[scope].module.id).0[name_span.range()].to_owned())
        .collect();

    Struct {
        name,
        members,
        methods: symbols,
        generics,
    }
}

fn generic_scope(generics: &[TSpan], scopes: &mut Scopes, scope: ScopeId, ast: &Ast) -> ScopeId {
    let names = generics.iter().enumerate().map(|(i, name_span)| {
        let name = &ast.src(scopes[scope].module.id).0[name_span.range()];
        (name.to_owned(), UnresolvedDefId::Resolved(DefId::Generic(i as u8)))
    }).collect();

    scopes.child(scope, names, dmap::new(), false)
}

fn enum_def(
    name: String,
    def: &ast::EnumDefinition,
    scopes: &mut Scopes,
    scope: ScopeId,
    ast: &Ast,
    symbols: &mut SymbolTable,
    errors: &mut Errors,
    ir: &mut irgen::Functions,
) -> Enum {
    let scope = generic_scope(&def.generics, scopes, scope, ast);
    let variants = def.variants
        .iter()
        .enumerate()
        .map(|(i, (_, name, args))| (
            name.clone(),
            (
                VariantId::new(i as u16),
                i as _,
                args.iter().map(|ty| scopes.resolve_ty(scope, ty, errors, symbols, ast, ir)).collect(),
            )
        ))
        .collect();
    Enum { name, variants, generic_count: def.generic_count() }
}

fn global(def: &ast::GlobalDefinition, ast: &Ast, scopes: &mut Scopes, scope: ScopeId, symbols: &mut SymbolTable, errors: &mut Errors, ir: &mut irgen::Functions)
-> (Type, Option<ConstVal>) {
    let ty = scopes.resolve_ty(scope, &def.ty, errors, symbols, ast, ir);

    if def.val.is_some() {
        todo!("globals with initial values")
    }

    (ty, None)
}

#[derive(Clone, Copy, Debug)]
pub enum Ident {
    Invalid,
    Var(VarId),
    Global(GlobalId),
    Const(ConstId),
    Type(TypeRef),
}

#[derive(Clone, Copy, Debug)]
pub struct VarId(u32);
impl VarId {
    pub fn idx(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Var {
    ty: TypeRef,
}

struct Ctx<'a> {
    scope: ScopeId,
    scopes: &'a mut Scopes,
    ast: &'a Ast,
    symbols: &'a mut SymbolTable,
    types: &'a mut TypeTable,
    idents: &'a mut [Ident],
    vars: &'a mut Vec<Var>,
    errors: &'a mut Errors,
    ir: &'a mut irgen::Functions,
    exhaustions: &'a mut Vec<(Exhaustion, TypeRef,TSpan)>,
}
impl<'a> Ctx<'a> {
    fn with_scope(&mut self, scope: ScopeId) -> Ctx<'_> {
        Ctx {
            scope,
            scopes: &mut *self.scopes,
            ast: self.ast,
            symbols: &mut *self.symbols,
            types: &mut *self.types,
            idents: &mut *self.idents,
            vars: &mut *self.vars,
            errors: &mut *self.errors,
            ir: &mut *self.ir,
            exhaustions: &mut *self.exhaustions,
        }
    }
    fn reborrow(&mut self) -> Ctx<'_> {
        Ctx {
            scope: self.scope,
            scopes: &mut *self.scopes,
            ast: self.ast,
            symbols: &mut *self.symbols,
            types: &mut *self.types,
            idents: &mut *self.idents,
            vars: &mut *self.vars,
            errors: &mut *self.errors,
            ir: &mut *self.ir,
            exhaustions: &mut *self.exhaustions,
        }
    }
    fn new_var(&mut self, var: Var) -> VarId {
        self.vars.push(var);
        VarId((self.vars.len() - 1) as _)
    }
    fn var(&self, id: VarId) -> Var {
        self.vars[id.0 as usize]
    }
    fn set_ident(&mut self, id: IdentId, ident: Ident) {
        self.idents[id.idx()] = ident;
    }
    fn merge(&mut self, a: TypeRef, b: TypeRef, span: Span) {
        self.types.merge(a, b, self.errors, span, self.symbols);
    } 
    fn specify(&mut self, idx: TypeRef, info: TypeInfo, span: Span) {
        self.types.specify(idx, info, self.errors, span, self.symbols)
    }
    fn span(&self, expr: ExprRef) -> Span {
        self.ast[expr].span_in(self.ast, self.scopes[self.scope].module.id)
    }
    fn scope(&self) -> &Scope {
        &self.scopes[self.scope]
    }

    fn src(&self, span: TSpan) -> &str {
        &self.ast.src(self.scopes[self.scope].module.id).0[span.range()]
    }

    pub fn specify_enum_variant(&mut self, idx: TypeRef, name: &str, span: Span, args: TypeRefs) {
        // avoid creating enum TypeInfo unnecessarily to avoid allocations and complex comparisons
        let (idx, ty) = self.types.find_optimizing(idx);
        match ty {
            TypeInfo::Enum(variants) => {
                match self.types.get_enum_variants(variants).iter().find(|(other_name, _)| other_name.as_str() == name) {
                    Some((_, other_args)) => {
                        if args.len() != other_args.len() {
                            self.errors.emit_span(Error::MismatchedType {
                                expected: format!("enum variant with {} args", other_args.len()),
                                found: format!("enum variang with {} args", args.len())
                            }, span);
                            return;
                        }
                        for (a, b) in args.iter().zip(other_args.iter()) {
                            self.merge(a, b, span);
                        }
                    }
                    None => {
                        let new_variants = self.types.extend_enum_variants(
                            variants,
                            std::iter::once((name.to_owned(), args))
                        );
                        self.types.update_type(idx, TypeInfo::Enum(new_variants));
                    }
                }
            }
            TypeInfo::Resolved(id, generics) => {
                if let ResolvedTypeDef::Enum(def) = self.symbols.get_type(id) {
                    match def.variants.get(name) {
                        Some((_id, _, arg_types)) => {
                            if args.len() != arg_types.len() {
                                self.errors.emit_span(Error::InvalidArgCount {
                                    expected: arg_types.len() as u32,
                                    found: args.len() as u32,
                                    varargs: false,
                                }, span);
                                return;
                            }
                            for (arg_idx, ty) in args.iter().zip(arg_types) {
                                let ty = ty.as_info(self.types, |i| generics.nth(i as _).into());
                                self.types.specify_or_merge(arg_idx, ty, self.errors, span, &self.symbols);
                            }
                        }
                        None => self.errors.emit_span(Error::NonexistantEnumVariant, span),
                    }
                } else {
                    let found = ty.as_string(&self.types, &self.symbols).into_owned();
                    self.errors.emit_span(Error::MismatchedType {
                        expected: "an enum".to_string(), found
                    }, span);
                }
            }
            _ => {
                let variant = self.types.add_enum_variants(std::iter::once((name.to_owned(), args)));
                self.specify(
                    idx,
                    TypeInfo::Enum(variant),
                    span,
                );
            }
        }
    }

    pub fn add_exhaustion(&mut self, exhaustion: Exhaustion, ty: TypeRef, span: TSpan) {
        if exhaustion.is_trivially_exhausted() { return } 
        self.exhaustions.push((exhaustion, ty, span));
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ResolvedCall {
    Function { func_id: FunctionId, generics: TypeRefs },
    Struct { type_id: TypeId, generics: TypeRefs },
    Invalid,
}

#[derive(Debug, Clone, Copy)]
pub enum MemberAccess {
    Size(TypeId),
    Align(TypeId),
    Stride(TypeId),
    LocalSize(TypeRef),
    LocalAlign(TypeRef),
    LocalStride(TypeRef),
    StructMember(u32),
    Symbol(DefId),
    Method(FunctionId),
    EnumItem(TypeId, u32),
    Invalid,
}

fn func_body<'a>(body: ExprRef, func_id: FunctionId, generics_ctx: &[String], mut ctx: Ctx) {
    let scope = ctx.scopes.child(ctx.scope, dmap::new(), dmap::new(), false);
    let mut ctx = ctx.with_scope(scope);
    let signature = ctx.symbols.get_func(func_id);
    
    let generics = ctx.types.generics();
    let mut generic_types = generics.iter();

    for name in generics_ctx {
        let ty = generic_types.next().unwrap();
        ctx.scopes[scope].add_generic(name.clone(), ty);
    }
    for name in &signature.generics {
        let ty = generic_types.next().unwrap();
        ctx.scopes[scope].add_generic(name.clone(), ty);
    }

    let on_generic = |i| TypeInfoOrIndex::Idx(generics.nth(i as u32));

    for (i, (name, ty)) in signature.params.iter().enumerate() {
        let ty = ty.as_info(ctx.types, on_generic);
        let ty = ctx.types.add_info_or_idx(ty);
        ctx.vars.push(Var { ty });
        let var_id = VarId((ctx.vars.len() - 1) as _);
        ctx.idents[i] = Ident::Var(var_id);
        ctx.scopes[scope].define_var(name.clone(), var_id);
    }

    let signature = ctx.symbols.get_func(func_id);
    let return_type_info = signature.return_type.as_info(ctx.types, on_generic);
    let expected = ctx.types.add_info_or_idx(return_type_info);

    let mut noreturn = false;
    val_expr(body, ExprInfo { expected, ret: expected, noreturn: &mut noreturn }, ctx.reborrow(), false);
}
