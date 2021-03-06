use std::ptr::NonNull;

use crate::{
    ast::{self, Expr, ModuleId, UnOp, ExprRef, IdentPath},
    error::{Error, Errors, EyeResult},
    lexer::tokens::{Operator, AssignType, IntLiteral, FloatLiteral},
    types::Primitive, span::{Span, TSpan}, dmap::{self, DHashMap},
};
use builder::IrBuilder;

use super::{typing::*, *};

mod builder;

struct GenCtx<'s> {
    ctx: TypingCtx,
    globals: Globals,
    ast: &'s ast::Ast,
    module: ModuleId,
    errors: Errors,
}
impl<'s> GenCtx<'s> {
    pub fn span(&self, expr: &Expr) -> Span {
        expr.span_in(self.ast, self.module)
    }
    pub fn src(&self, span: TSpan) -> &str {
        &self.ast.sources[self.module.idx()].0[span.range()]
    }
}

#[derive(Clone, Debug)]
pub struct Globals(pub Vec<DHashMap<String, Symbol>>);
impl Globals {
    pub fn get_ref(&self) -> GlobalsRef {
        GlobalsRef(&self.0)
    }
}
impl Globals {
    pub fn iter(&self) -> impl Iterator<Item = (&String, &Symbol)> {
        self.0.iter().flat_map(|it| it.iter())
    }
    pub fn _shrink_to_fit(&mut self) {
        self.0.shrink_to_fit();
        for map in &mut self.0 {
            map.shrink_to_fit();
        }
    }
}
impl std::ops::Index<ModuleId> for Globals {
    type Output = DHashMap<String, Symbol>;

    fn index(&self, index: ModuleId) -> &Self::Output {
        &self.0[index.idx()]
    }
}
impl std::ops::IndexMut<ModuleId> for Globals {
    fn index_mut(&mut self, index: ModuleId) -> &mut Self::Output {
        &mut self.0[index.idx()]
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


pub fn reduce(ast: &ast::Ast, mut errors: Errors, require_main_func: bool) 
-> (Result<(Module, Globals), ()>, Errors) {
    let mut ctx = TypingCtx {
        funcs: Vec::new(),
        types: Vec::new(),
        traits: Vec::new(),
        consts: Vec::new(),
        globals: Vec::new(),
    };
    //let mut globals = types2::gen_globals(ast, &mut ctx, &mut errors);
    let mut globals = Globals((0..ast.modules.len()).map(|_| dmap::new()).collect());

    for (id, module) in ast.modules.iter().enumerate() {
        let id = ModuleId::new(id as u32);
        let mut gen_ctx = GenCtx { ctx, globals, ast, module: id, errors };
        let mut scope = Scope::module(id);

        generate_bodies(&mut scope, &ast[module.definitions], &mut gen_ctx);
        globals = gen_ctx.globals;
        errors = gen_ctx.errors;
        ctx = gen_ctx.ctx;
    }
    if errors.has_errors() {
        return (Err(()), errors);
    }
    
    let global_vars = globals.iter().filter_map(|(name, symbol)| {
        match symbol {
            Symbol::GlobalVar(key) => {
                let (ty, initial_val) = ctx.get_global(*key);
                Some((name.clone(), ty.clone(), initial_val.clone()))
            }
            _ => None
        }
    }).collect();

    let funcs = ctx
        .funcs
        .into_iter()
        .map(|func| match func {
            FunctionOrHeader::Header(_) => panic!("Function was not generated"),
            FunctionOrHeader::Func(func) => func,
        })
        .collect();

    let mut main = None;
    if require_main_func {
        main = Some(if let Some(Symbol::Func(func)) = globals[ModuleId::ROOT].get("main") {
            *func
        } else {
            errors.emit(Error::MissingMain, 0, 0, ModuleId::ROOT);
            return (Err(()), errors);
        });
    }


    (
        Ok((
            Module {
                name: "MainModule".to_owned(),
                funcs,
                globals: global_vars,
                main,
                types: ctx.types,
            },
            globals
        )),
        errors,
    )
}

fn generate_bodies(
    scope: &mut Scope,
    defs: &DHashMap<String, ast::Definition>,
    gen_ctx: &mut GenCtx,
) {
    for (name, def) in defs {
        if scope.get_scope_symbol(gen_ctx.globals.get_ref(), &name).is_some() { continue }
        gen_definition(name, def, scope, gen_ctx,
            |scope, name, symbol, globals| scope.add_symbol(name, symbol, globals));
    }
}

fn gen_definition(
    name: &str,
    def: &ast::Definition,
    scope: &mut Scope,
    ctx: &mut GenCtx,
    add_symbol: impl FnOnce(&mut Scope, String, Symbol, &mut Globals)
) -> Symbol {
    match def {
        ast::Definition::Function(func) => {
            let header = gen_func_header(func, scope, ctx);
            let key = ctx.ctx.add_func(FunctionOrHeader::Header(header));
            add_symbol(scope, name.to_owned(), Symbol::Func(key), &mut ctx.globals);
            gen_func_body(name, func, key, scope, ctx);
            Symbol::Func(key)
        }
        ast::Definition::Struct(def) => {
            let key = ctx.ctx.add_proto_ty(name.to_owned(), def.generics.len() as _);
            add_symbol(scope, name.to_owned(), Symbol::Type(key), &mut ctx.globals);
            gen_struct(def, ctx, scope, key);
            Symbol::Type(key)
        }
        ast::Definition::Enum(def) => {
            let key = ctx.ctx.add_proto_ty(name.to_owned(), def.generics.len() as _);
            add_symbol(scope, name.to_owned(), Symbol::Type(key), &mut ctx.globals);
            gen_enum(def, ctx, scope, key);
            Symbol::Type(key)
        }
        ast::Definition::Trait(def) => {
            let trait_ = gen_trait(def, ctx, scope);
            let symbol = Symbol::Trait(ctx.ctx.add_trait(trait_));
            add_symbol(scope, name.to_owned(), symbol, &mut ctx.globals);
            symbol
        }
        ast::Definition::Module(id) => {
            add_symbol(scope, name.to_owned(), Symbol::Module(*id), &mut ctx.globals);
            Symbol::Module(*id)
        }
        ast::Definition::Use(path) => {
            let symbol = resolve_path(path, ctx, scope);
            add_symbol(scope, name.to_owned(), symbol, &mut ctx.globals);
            symbol
        },
        ast::Definition::Const(ty, expr) => {
            let key = ctx.ctx.add_const(ConstVal::NotGenerated);
            add_symbol(scope, name.to_owned(), Symbol::Const(key), &mut ctx.globals);
            let val = match scope.eval_const(ctx, Some(ty), *expr) {
                Ok(val) => val,
                Err(err) => {
                    ctx.errors.emit_err(err);
                    ConstVal::Invalid
                }
            };
            ctx.ctx.consts[key.idx()] = val;
            Symbol::Const(key)
        }
        ast::Definition::Global(ty, val) => {
            let ty = scope.resolve_uninferred_type(ty, ctx);
            assert!(val.is_none(), "TODO: Globals with initial values are unsupported right now");
            let symbol = Symbol::GlobalVar(ctx.ctx.add_global(ty, None));
            add_symbol(scope, name.to_owned(), symbol, &mut ctx.globals);
            symbol
        }
    }
}

fn gen_func_header(func: &ast::Function, scope: &mut Scope, ctx: &mut GenCtx)
-> FunctionHeader {
    let params = func.params.iter()
        .map(|(name, unresolved, _, _)| {
            let ty = scope.resolve_uninferred_type(unresolved, ctx);
            (name.clone(), ty)
        })
        .collect();
    let return_type = scope.resolve_uninferred_type(&func.return_type, ctx);

    FunctionHeader {
        params,
        varargs: func.varargs,
        return_type,
    }
}
fn gen_func_body(name: &str, def: &ast::Function, key: SymbolKey, scope: &mut Scope, ctx: &mut GenCtx) {
    let func_idx = key.idx();
    let header = match &ctx.ctx.funcs[func_idx] {
        FunctionOrHeader::Func(_) => {
            // this might happen in the future when functions need to know other function's bodies
            unreachable!("Function shouldn't already be defined here")
        }
        FunctionOrHeader::Header(header) => header.clone(),
    };
    let ir = def.body.as_ref().map(|body| {
        let mut builder = IrBuilder::new(ctx.module);
        let mut scope_symbols = dmap::with_capacity(header.params.len() + def.generics.len());
        
        for generic in &def.generics {
            let name = &ctx.ast.src(ctx.module).0[generic.range()];
            let generic_ty = builder.types.add(TypeInfo::Unknown);
            scope_symbols.insert(name.to_owned(), Symbol::LocalType(generic_ty));
        }
        for (i, (name, ty)) in header.params.iter().enumerate() {
            let info = ty.as_info(&mut builder.types);
            let ty = builder.types.add(info);
            let param = builder.add(Data { int32: i as u32 }, Tag::Param, ty);
            scope_symbols.insert(name.clone(), Symbol::Var { ty, var: param });
        }
        let scope_defs = dmap::new();
        let mut scope: Scope<'_> = scope.child(&mut scope_symbols, &scope_defs);
        let return_type = header.return_type.as_info(&mut builder.types);
        let expected = builder.types.add(return_type);
        let mut noreturn = false;
        let body = &ctx.ast[*body];
        let body_span = body.span(ctx.ast);
        let val = scope.reduce_expr_val_spanned(ctx, &mut builder, body, body_span,
            ExprInfo { expected, ret: expected, noreturn: &mut noreturn });
        if !noreturn {
            if header.return_type == Type::Prim(Primitive::Unit) {
                builder.add_unused_untyped(Tag::Ret, Data { un_op: Ref::UNIT });
            } else if !body.is_block() {
                builder.add_unused_untyped(Tag::Ret, Data { un_op: val });
            } else {
                ctx.errors.emit_span(Error::MissingReturnValue, body_span.in_mod(ctx.module));
            }
        } else if !builder.currently_terminated() {
            builder.add_unused_untyped(Tag::RetUndef, Data { none: () });
        }
        builder.finish()
    });

    ctx.ctx.funcs[func_idx] = FunctionOrHeader::Func(Function {
        name: name.to_owned(),
        header,
        ir,
    });
}

fn gen_struct(
    def: &ast::StructDefinition,
    ctx: &mut GenCtx,
    scope: &mut Scope,
    key: SymbolKey,
) {
    let mut generic_symbols = def.generics.iter()
    .enumerate()
    .map(|(i, span)| (ctx.src(*span).to_owned(), Symbol::Generic(i as u8)))
    .collect();
    let scope_defs = dmap::new();
    let mut scope = scope.child(&mut generic_symbols, &scope_defs);

    let members = def.members.iter().map(|(name, unresolved, _start, _end)| {(
        name.clone(),
        scope.resolve_uninferred_type(unresolved, ctx),
    )}).collect::<Vec<_>>();

    *ctx.ctx.get_type_mut(key) = TypeDef::Struct(Struct {
        members,
        methods: dmap::with_capacity(def.members.len()),
        generic_count: def.generics.len() as u8,
    });

    for (method_name, method) in &def.methods {
        let header = gen_func_header(method, &mut scope, ctx);
        let method_key = ctx.ctx.add_func(super::gen::FunctionOrHeader::Header(header));
        let TypeDef::Struct(Struct { methods, .. }) = ctx.ctx.get_type_mut(key) else { unreachable!() };
        methods.insert(method_name.clone(), method_key);
    }
    for (method_name, method) in &def.methods {
        // type is set to Struct above
        let TypeDef::Struct(struct_) = ctx.ctx.get_type_mut(key) else { unreachable!() };
        gen_func_body(&method_name, method, struct_.methods[method_name], &mut scope, ctx);
    }
}

fn gen_enum(
    def: &ast::EnumDefinition,
    ctx: &mut GenCtx,
    _scope: &mut Scope,
    key: SymbolKey,  
) {
    let mut generic_symbols = def.generics.iter()
    .enumerate()
    .map(|(i, span)| (ctx.src(*span).to_owned(), Symbol::Generic(i as u8)))
    .collect();
    let scope_defs = dmap::new();
    let mut _scope = _scope.child(&mut generic_symbols, &scope_defs);

    let variants = def.variants.iter()
        .enumerate()
        .map(|(idx, (_span, name))| (name.clone(), idx as u32))
        .collect();

    *ctx.ctx.get_type_mut(key) = TypeDef::Enum(Enum {
        variants,
        generic_count: def.generics.len() as u8,
    });
}

fn gen_trait(
    def: &ast::TraitDefinition,
    ctx: &mut GenCtx,
    scope: &mut Scope,
) -> TraitDef {
    let mut generic_symbols = def.generics.iter()
    .enumerate()
    .map(|(i, span)| (ctx.src(*span).to_owned(), Symbol::Generic(i as u8)))
    .collect();
    let scope_defs = dmap::new();
    let mut scope = scope.child(&mut generic_symbols, &scope_defs);


    let functions = def.functions.iter()
        .enumerate()
        .map(|(i, (name, (_span, func)))| (name.clone(), (i as u32, gen_func_header(func, &mut scope, ctx))))
        .collect();
    TraitDef { functions }
}

fn resolve_path(path: &IdentPath, ctx: &mut GenCtx, scope: &mut Scope) -> Symbol {
    enum State {
        Local,
        Module(ModuleId)
    }
    let (root, segments, last) = path.segments(ctx.ast.src(ctx.module).0);
    let mut state = if root.is_some() { State::Module(ModuleId::ROOT) } else { State::Local };
    
    for (segment, segment_span) in segments {
        let symbol = match state {
            State::Local => scope.resolve(segment, ctx),
            State::Module(id) => resolve_module_symbol(ctx, id, segment)
        };
        match symbol {
            Some(Symbol::Module(id)) => state = State::Module(id),
            Some(_) => {
                ctx.errors.emit_span(Error::ModuleExpected, segment_span.in_mod(ctx.module));
                return Symbol::Invalid
            }
            None => {
                ctx.errors.emit_span(Error::UnknownModule, segment_span.in_mod(ctx.module));
                return Symbol::Invalid
            }
        }
    }

    if let Some((last, last_span)) = last {
        let symbol = match state {
            State::Local => scope.resolve(last, ctx),
            State::Module(id) => resolve_module_symbol(ctx, id, last)
        };
        match symbol {
            Some(symbol) => symbol,
            None => {
                ctx.errors.emit_span(Error::UnknownIdent, last_span.in_mod(ctx.module));
                Symbol::Invalid
            }
        }
    } else {
        // there can't be no last symbol and not a single module because then there wouldn't be any path.
        let State::Module(id) = state else { unreachable!() };
        Symbol::Module(id)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Symbol {
    Func(SymbolKey),
    Type(SymbolKey),
    Trait(SymbolKey),
    LocalType(TypeTableIndex),
    Generic(u8),
    Module(ModuleId),
    Var { ty: TypeTableIndex, var: Ref },
    GlobalVar(SymbolKey),
    Const(SymbolKey),
    Invalid,
}

pub enum FunctionOrHeader {
    Func(Function),
    Header(FunctionHeader),
}
impl FunctionOrHeader {
    fn header(&self) -> &FunctionHeader {
        match self {
            Self::Func(f) => &f.header,
            Self::Header(h) => h,
        }
    }
}

pub struct TypingCtx {
    funcs: Vec<FunctionOrHeader>,
    types: Vec<(String, TypeDef)>,
    traits: Vec<TraitDef>,
    consts: Vec<ConstVal>,
    globals: Vec<(Type, Option<ConstVal>)>,
}
impl TypingCtx {
    pub fn add_func(&mut self, func: FunctionOrHeader) -> SymbolKey {
        let key = SymbolKey(self.funcs.len() as u64);
        self.funcs.push(func);
        key
    }
    pub fn add_type(&mut self, name: String, ty: TypeDef) -> SymbolKey {
        let key = SymbolKey(self.types.len() as u64);
        self.types.push((name, ty));
        key
    }
    pub fn add_proto_ty(&mut self, name: String, generic_count: u8) -> SymbolKey {
        self.add_type(name, TypeDef::NotGenerated { generic_count, generating: false })
    }
    pub fn add_trait(&mut self, t: TraitDef) -> SymbolKey {
        let key = SymbolKey(self.traits.len() as u64);
        self.traits.push(t);
        key
    }
    pub fn add_const(&mut self, c: ConstVal) -> SymbolKey {
        let key = SymbolKey(self.consts.len() as u64);
        self.consts.push(c);
        key
    }
    pub fn add_global(&mut self, ty: Type, val: Option<ConstVal>) -> SymbolKey {
        let key = SymbolKey(self.globals.len() as u64);
        self.globals.push((ty, val));
        key
    }
    pub fn get_type(&self, key: SymbolKey) -> &TypeDef { &self.types[key.idx()].1 }
    pub fn get_type_mut(&mut self, key: SymbolKey) -> &mut TypeDef { &mut self.types[key.idx()].1 }
    //pub fn get_func(&self, key: SymbolKey) -> &FunctionOrHeader { &self.funcs[key.idx()] }
    //pub fn get_func_mut(&mut self, key: SymbolKey) -> &mut FunctionOrHeader { &mut self.funcs[key.idx()] }
    pub fn get_trait(&self, key: SymbolKey) -> &TraitDef { &self.traits[key.idx()] }
    pub fn get_const(&self, key: SymbolKey) -> &ConstVal { &self.consts[key.idx()] }
    pub fn get_global(&self, key: SymbolKey) -> &(Type, Option<ConstVal>) { &self.globals[key.idx()] }
    pub fn get_const_mut(&mut self, key: SymbolKey) -> &mut ConstVal { &mut self.consts[key.idx()] }
}

#[derive(Debug)]
enum ExprResult {
    VarRef(Ref),
    Val(Ref),
    Func(SymbolKey),
    TraitFunc(SymbolKey, u32),
    /// method call on a variable: x.method
    Method(Ref, SymbolKey),
    Type(SymbolKey),
    Trait(SymbolKey),
    LocalType(TypeTableIndex),
    Module(ModuleId),
    Stored(Ref),
}

impl ExprResult {
    pub fn get_or_load(
        self,
        ir: &mut IrBuilder,
        ty: TypeTableIndex,
        errors: &mut Errors,
        span: Span,
    ) -> Ref {
        self.try_get_or_load(ir, ty).unwrap_or_else(|| {
            errors.emit_span(Error::ExpectedValueFoundDefinition, span);
            Ref::UNDEF
        })
    }

    pub fn try_get_or_load(&self, ir: &mut IrBuilder, ty: TypeTableIndex) -> Option<Ref> {
        match self {
            ExprResult::VarRef(var) | ExprResult::Stored(var) => {
                Some(ir.add(Data { un_op: *var }, Tag::Load, ty))
            }
            ExprResult::Val(val) => Some(*val),
            _ => None,
        }
    }
}

struct ExprInfo<'a> {
    expected: TypeTableIndex,
    ret: TypeTableIndex,
    noreturn: &'a mut bool,
}
impl<'a> ExprInfo<'a> {
    pub fn mark_noreturn(&mut self) {
        *self.noreturn = true;
    }
    pub fn with_expected(&mut self, expected: TypeTableIndex) -> ExprInfo {
        ExprInfo { expected, ret: self.ret, noreturn: self.noreturn }
    }
    pub fn with_noreturn<'b>(&self, noreturn: &'b mut bool) -> ExprInfo<'b> {
        ExprInfo { expected: self.expected, ret: self.ret, noreturn }
    }
    pub fn reborrow(&mut self) -> ExprInfo<'_> {
        ExprInfo { expected: self.expected, ret: self.ret, noreturn: &mut *self.noreturn }
    }
}

pub enum Scope<'a> {
    Module(ModuleId),
    Local {
        parent: NonNull<Scope<'a>>, // &'a mut Scope<'a> I tried this multiple times with references and it should be possible but it isn't
        symbols: &'a mut DHashMap<String, Symbol>,
        defs: &'a DHashMap<String, ast::Definition>,
    }
}

fn resolve_module_symbol(ctx: &mut GenCtx, id: ModuleId, name: &str) -> Option<Symbol> {
    let prev_id = ctx.module;
    ctx.module = id;
    let symbol = ctx.globals[id].get(name).copied().or_else(|| {
        ctx.ast[ctx.ast[id].definitions].get(name).map(|def|
            gen_definition(name, def, &mut Scope::Module(id), ctx,
                |_scope, name, symbol, globals| {
                    let prev = globals[id].insert(name, symbol);
                    debug_assert!(prev.is_none());
                }
            )
        )
    });
    ctx.module = prev_id;
    symbol
}

impl<'s> Scope<'s> {
    pub fn module(module: ModuleId) -> Self {
        Self::Module(module)
    }
    /*pub fn reborrow<'n>(&mut self) -> Scope<'n> where 's: 'n {
        match self {
            Self::Module(id) => Scope::Module(*id),
            Self::Local { parent, symbols, defs } => Scope::Local { parent: &mut *parent, symbols, defs }
        }
    }*/
    pub fn child<'c>(
        &'c mut self,
        symbols: &'c mut DHashMap<String, Symbol>,
        defs: &'c DHashMap<String, ast::Definition>
    ) -> Scope<'c>
    where 's: 'c {
        Scope::Local {
            parent: self.into(),
            symbols,
            defs,
        }
    }
    fn get_scope_symbol<'a>(&'a self, globals: GlobalsRef<'a>, name: &str) -> Option<Symbol> {
        match self {
            Self::Module(id) => &globals[*id],
            Self::Local { symbols, .. } => *symbols
        }.get(name).copied()
    }
    fn add_symbol(&mut self, name: String, symbol: Symbol, globals: &mut Globals) {
        let prev = match self {
            Self::Module(id) => &mut globals[*id],
            Self::Local { symbols, .. } => *symbols
        }.insert(name, symbol);
        debug_assert!(prev.is_none(), "symbol added multiple times");
    }
    fn resolve(&mut self, name: &str, ctx: &mut GenCtx) -> Option<Symbol> {
        let mut current = self;
        loop {
            match current {
                &mut Scope::Module(id) => return resolve_module_symbol(ctx, id, name),
                Scope::Local { parent: _, symbols, defs } => {
                    if let Some(symbol) = symbols.get(name).copied()
                    .or_else(|| defs.get(name).map(|def| gen_definition(name, def, current, ctx,
                        |scope, name, symbol, globals| scope.add_symbol(name, symbol, globals)
                    )))
                    {
                        return Some(symbol);
                    } else {
                        let Scope::Local { parent, .. } = current else { unreachable!() };
                        current = unsafe { parent.as_mut() };
                    }
                }
            }
        }
    }
        

    fn resolve_type(&mut self, unresolved: &ast::UnresolvedType, types: &mut TypeTable, ctx: &mut GenCtx)
    -> Result<TypeInfo, Error> {
        match unresolved {
            ast::UnresolvedType::Primitive(p, _) => Ok(TypeInfo::Primitive(*p)),
            ast::UnresolvedType::Unresolved(path, generics) => {
                let (root, iter, last) = path.segments(ctx.ast.src(ctx.module).0);
                // no last segment means it must point to the root module
                let Some(last) = last else { return Err(Error::TypeExpected) };
                
                enum ModuleOrLocal {
                    Module(ModuleId),
                    Local
                }
                
                let mut current_module = if root.is_some() {
                    ModuleOrLocal::Module(ModuleId::ROOT)
                } else {
                    ModuleOrLocal::Local
                };

                for segment in iter {
                    let look_from = match current_module {
                        ModuleOrLocal::Module(m) => m,
                        ModuleOrLocal::Local => ctx.module
                    };
                    match ctx.globals[look_from].get(segment.0) {
                        Some(Symbol::Module(m)) => current_module = ModuleOrLocal::Module(*m),
                        Some(_) => panic!("1"),//return Err(Error::ModuleExpected),
                        None => return Err(Error::UnknownModule)
                    }
                }
                let mut resolve_generics = |ctx: &mut GenCtx, s: &mut Scope, key: SymbolKey| {
                    let generic_count = ctx.ctx.get_type(key).generic_count();
                    Ok(if let Some((generics, _)) = generics {
                        if generics.len() != generic_count as usize {
                            return Err(Error::InvalidGenericCount {
                                expected: generic_count,
                                found: generics.len() as u8
                            })
                        }
                        let generics = generics.iter()
                            .map(|ty| s.resolve_type(ty, types, ctx))
                            .collect::<Result<Vec<_>, _>>()?;
                        types.add_multiple(
                            generics
                        )
                    } else {
                        types.add_multiple(
                            (0..generic_count)
                                .map(|_| TypeInfo::Unknown)
                        )
                    })
                };
                match current_module {
                    ModuleOrLocal::Module(m) => match ctx.globals[m]
                        .get(last.0)
                        .ok_or(Error::UnknownIdent)? {
                            &Symbol::Type(ty) => {
                                let generics = resolve_generics(ctx, self, ty)?;
                                Ok(TypeInfo::Resolved(ty, generics))
                            }
                            // TODO: might require a new solution to allow inference of local types
                            Symbol::LocalType(ty) => Ok(types.get_type(*ty)),
                            Symbol::Const(key) => {
                                match ctx.ctx.get_const(*key) {
                                    &ConstVal::Symbol(Symbol::Type(key)) => {
                                        let generics = resolve_generics(ctx, self, key)?;
                                        Ok(TypeInfo::Resolved(key, generics))
                                    }
                                    _ => Err(Error::TypeExpected)
                                }
                            }
                            _ => Err(Error::TypeExpected)
                        },
                    ModuleOrLocal::Local => match self.resolve(last.0, ctx).ok_or(Error::UnknownIdent)? {
                        Symbol::Type(ty) => {
                            let generics = resolve_generics(ctx, self, ty)?;
                            Ok(TypeInfo::Resolved(ty, generics))
                        }
                        //TODO: local generics?
                        Symbol::LocalType(ty) => Ok(types.get_type(ty)),
                        _ => Err(Error::TypeExpected)
                    }
                }
            }
            ast::UnresolvedType::Pointer(box (inner, _)) => {
                let inner = self.resolve_type(inner, types, ctx)?;
                Ok(TypeInfo::Pointer(types.add(inner)))
            }
            ast::UnresolvedType::Array(box (inner, _, count)) => {
                let inner = self.resolve_type(inner, types, ctx)?;
                let inner = types.add(inner);
                Ok(TypeInfo::Array(*count, inner))
            }
            ast::UnresolvedType::Tuple(elems, _) => {
                let elems = elems.iter().map(|ty| self.resolve_type(ty, types, ctx)).collect::<Result<Vec<_>, _>>()?;
                Ok(TypeInfo::Tuple(types.add_multiple(elems)))
            }
            ast::UnresolvedType::Infer(_) => Ok(TypeInfo::Unknown)
        }
    }

    // TODO: rename to uninferred
    fn resolve_uninferred_type(&mut self, unresolved: &ast::UnresolvedType, ctx: &mut GenCtx)
    -> Type {
        match unresolved {
            ast::UnresolvedType::Primitive(p, _) => Type::Prim(*p),
            ast::UnresolvedType::Unresolved(path, generics) => {
                let (root, iter, last) = path.segments(ctx.ast.src(ctx.module).0);
                // no last segment means it must point to the root module
                let Some(last) = last else {
                    ctx.errors.emit_span(Error::TypeExpected, unresolved.span().in_mod(ctx.module));
                    return Type::Invalid
                };
                
                enum ModuleOrLocal {
                    Module(ModuleId),
                    Local
                }
                
                let mut current_module = if root.is_some() {
                    ModuleOrLocal::Module(ModuleId::ROOT)
                } else {
                    ModuleOrLocal::Local
                };

                for segment in iter {
                    let look_from = match current_module {
                        ModuleOrLocal::Module(m) => m,
                        ModuleOrLocal::Local => ctx.module
                    };
                    match resolve_module_symbol(ctx, look_from, segment.0) {
                        Some(Symbol::Module(m)) => current_module = ModuleOrLocal::Module(m),
                        Some(_) => {
                            ctx.errors.emit_span(Error::ModuleExpected, segment.1.in_mod(ctx.module));
                            return Type::Invalid
                        }
                        None => {
                            ctx.errors.emit_err(Error::UnknownModule.at_span(segment.1.in_mod(ctx.module)));
                            return Type::Invalid;
                        }
                    }
                }
                let resolve_generics = |ctx: &mut GenCtx, s: &mut Scope, key: SymbolKey| {
                    let generic_count = ctx.ctx.get_type(key).generic_count();
                    Ok(if let Some((generics, _)) = generics {
                        if generics.len() != generic_count as usize {
                            ctx.errors.emit_span(Error::InvalidGenericCount {
                                expected: generic_count,
                                found: generics.len() as u8
                            }, unresolved.span().in_mod(ctx.module));
                            return Err(())
                        }
                        generics.iter()
                            .map(|ty| s.resolve_uninferred_type(ty, ctx))
                            .collect::<Vec<_>>()
                    } else {
                        if generic_count != 0 {
                            ctx.errors.emit_span(
                                Error::InvalidGenericCount { expected: generic_count, found: 0 },
                                unresolved.span().in_mod(ctx.module)
                            );
                            return Err(())
                        } else {
                            Vec::new()
                        }
                    })
                };
                match current_module {
                    ModuleOrLocal::Module(m) => match ctx.globals[m]
                        .get(last.0) {
                            None => {
                                ctx.errors.emit_span(Error::UnknownIdent, last.1.in_mod(ctx.module));
                                Type::Invalid
                            }
                            Some(&Symbol::Type(ty)) => {
                                let Ok(generics) = resolve_generics(ctx, self, ty) else { return Type::Invalid };
                                Type::Id(ty, generics)
                            }
                            Some(Symbol::LocalType(_ty)) => todo!(), // what to do here, what was LocalType again?
                            Some(Symbol::Const(key)) => {
                                match ctx.ctx.get_const(*key) {
                                    &ConstVal::Symbol(Symbol::Type(key)) => {
                                        let Ok(generics) = resolve_generics(ctx, self, key) else { return Type::Invalid };
                                        Type::Id(key, generics)
                                    }
                                    _ => {
                                        ctx.errors.emit_span(Error::TypeExpected, last.1.in_mod(ctx.module));
                                        Type::Invalid
                                    }
                                }
                            }
                            _ => {
                                ctx.errors.emit_span(Error::TypeExpected, last.1.in_mod(ctx.module));
                                Type::Invalid
                            }
                        },
                    ModuleOrLocal::Local => match self.resolve(last.0, ctx) {
                        Some(Symbol::Type(ty)) => {
                            let Ok(generics) = resolve_generics(ctx, self, ty) else { return Type::Invalid };
                            Type::Id(ty, generics)
                        }
                        Some(Symbol::Generic(i)) => Type::Generic(i),
                        //TODO: local generics?
                        Some(Symbol::LocalType(_ty)) => todo!(), // what to do here, what was LocalType again?
                        None => {
                            ctx.errors.emit_span(Error::UnknownIdent, last.1.in_mod(ctx.module));
                            Type::Invalid
                        }
                        _ => {
                            ctx.errors.emit_span(Error::TypeExpected, last.1.in_mod(ctx.module));
                            Type::Invalid
                        }
                    }
                }
            }
            ast::UnresolvedType::Pointer(box (inner, _)) => {
                let inner = self.resolve_uninferred_type(inner, ctx);
                Type::Pointer(Box::new(inner))
            }
            ast::UnresolvedType::Array(box (inner, _, count)) => {
                let inner = self.resolve_uninferred_type(inner, ctx);
                let Some(count) = count else {
                    ctx.errors.emit_span(Error::ArraySizeCantBeInferredHere, unresolved.span().in_mod(ctx.module));
                    return Type::Invalid
                };
                Type::Array(Box::new((inner, *count)))
            }
            ast::UnresolvedType::Tuple(elems, _) => {
                let elems = elems.iter().map(|ty| self.resolve_uninferred_type(ty, ctx)).collect::<Vec<_>>();
                Type::Tuple(elems)
            }
            ast::UnresolvedType::Infer(_) => {
                ctx.errors.emit_span(Error::InferredTypeNotAllowedHere, unresolved.span().in_mod(ctx.module));
                Type::Invalid
            }
        }
    }

    fn declare_var(&mut self, ir: &mut IrBuilder, name: String, ty: TypeTableIndex) -> Ref {
        let var = ir.add(Data { none: () }, Tag::Decl, ty);
        match self {
            Scope::Module(_) => unreachable!("There shouldn't be variables defined in the global scope"),
            Scope::Local { symbols, .. } => {
                symbols.insert(name, Symbol::Var { ty, var  });
            }
        }
        var
    }

    fn reduce_expr_val_spanned(
        &mut self,
        ctx: &mut GenCtx,
        ir: &mut IrBuilder,
        expr: &Expr,
        span: TSpan,
        mut info: ExprInfo,
    ) -> Ref {
        self.reduce_expr(ctx, ir, expr, info.reborrow())
            .get_or_load(ir, info.expected, &mut ctx.errors, span.in_mod(ctx.module))
    }

    fn reduce_expr_idx_val(
        &mut self,
        gen_ctx: &mut GenCtx,
        ir: &mut IrBuilder,
        expr: ExprRef,
        info: ExprInfo,
    ) -> Ref {
        self.reduce_expr_val_spanned(gen_ctx, ir, &gen_ctx.ast[expr], gen_ctx.ast[expr].span(gen_ctx.ast), info)
    }

    fn reduce_expr(
        &mut self,
        ctx: &mut GenCtx,
        ir: &mut IrBuilder,
        expr: &Expr,
        mut info: ExprInfo,
    ) -> ExprResult {
        let expected = info.expected;
        self.reduce_expr_any(
            ctx, ir, expr, info.reborrow(),
            |ir| ir.add(Data { none: () }, Tag::Decl, expected), // declare new var
        ).0
    }

    fn reduce_unused_expr(
        &mut self,
        ctx: &mut GenCtx,
        ir: &mut IrBuilder,
        expr: &Expr,
        mut info: ExprInfo,
    ) {
        let expected = info.expected;
        if self.reduce_expr_any(
            ctx, ir, expr, info.reborrow(),
            |ir| ir.add(Data { none: () }, Tag::Decl, expected), // declare new var
        ).1 {
            ctx.errors.emit_span(Error::UnusedStatementValue, expr.span(ctx.ast).in_mod(ctx.module))  
        }
    }

    fn reduce_expr_store_into_var(
        &mut self,
        ctx: &mut GenCtx,
        ir: &mut IrBuilder,
        expr: &Expr,
        var: Ref,
        mut info: ExprInfo,
    ) {
        let val = match self.reduce_expr_any(ctx, ir, expr, info.reborrow(), |_| var).0 {
            ExprResult::Stored(_) => return,
            ExprResult::VarRef(other_var) => ir.add(Data { un_op: other_var }, Tag::Load, info.expected),
            ExprResult::Val(val) => val,
            _ => {
                ctx.errors.emit_span(Error::ExpectedValueFoundDefinition, expr.span(ctx.ast).in_mod(ctx.module));
                Ref::UNDEF
            }
        };
        ir.add_unused_untyped(Tag::Store, Data { bin_op: (var, val) });
    }

    fn reduce_lval_expr(
        &mut self,
        ctx: &mut GenCtx,
        ir: &mut IrBuilder,
        expr: &Expr,
        mut info: ExprInfo,
        error: Error,
    ) -> Ref {
        let expected = info.expected;
        match self.reduce_expr_any(
            ctx, ir, expr, info.reborrow(),
            |ir| ir.add(Data { none: () }, Tag::Decl, expected)
        ).0 {
            ExprResult::VarRef(var) | ExprResult::Stored(var) => var,
            ExprResult::Val(_)
            | ExprResult::Func(_)
            | ExprResult::TraitFunc(_, _)
            | ExprResult::Method(_, _)
            | ExprResult::Type(_)
            | ExprResult::Trait(_)
            | ExprResult::LocalType(_)
            | ExprResult::Module(_)
            => {
                if !ir.types.get_type(info.expected).is_invalid() {
                    ctx.errors.emit_span(error, expr.span(ctx.ast).in_mod(ctx.module));
                }
                Ref::UNDEF
            }
        }
    }

    fn reduce_expr_any(
        &mut self,
        ctx: &mut GenCtx,
        ir: &mut IrBuilder,
        expr: &Expr,
        mut info: ExprInfo,
        get_var: impl Fn(&mut IrBuilder) -> Ref,
    ) -> (ExprResult, bool) {
        let (r, should_use) = match expr {
            ast::Expr::Block { span, items, defs } => {
                let defs = &ctx.ast.expr_builder[*defs];
                let mut block_symbols = dmap::new();
                let mut block_scope = self.child(&mut block_symbols, defs);
                //types2::gen_locals(&mut block_scope, errors);
                
                generate_bodies(&mut block_scope, defs, ctx);
                let prev_emit = ir.emit;
                let mut block_noreturn = false;
                for item in ctx.ast.get_extra(*items) {
                    let item_ty = ir.types.add(TypeInfo::Unknown);
                    block_scope.reduce_unused_expr(ctx, ir, &ctx.ast[*item],
                        info.with_expected(item_ty).with_noreturn(&mut block_noreturn));
                    ir.emit = prev_emit && !block_noreturn;
                }
                ir.emit = prev_emit;
                *info.noreturn |= block_noreturn;
                if !block_noreturn {
                    ir.specify(info.expected, TypeInfo::UNIT, &mut ctx.errors, *span, &ctx.ctx);
                }
                (Ref::UNIT, false)
            }
            ast::Expr::Declare { name, end: _, annotated_ty } => {
                let expr_span = ctx.span(expr);
                ir.types.specify(info.expected, TypeInfo::UNIT, &mut ctx.errors, expr_span, &ctx.ctx);
                let ty = match self.resolve_type(annotated_ty, &mut ir.types, ctx) {
                    Ok(t) => t,
                    Err(err) => {
                        ctx.errors.emit_span(err, annotated_ty.span().in_mod(ctx.module));
                        TypeInfo::Invalid
                    }
                };
                let ty = ir.types.add(ty);

                self.declare_var(ir, ctx.src(*name).to_owned(), ty);

                (Ref::UNIT, false)
            }
            ast::Expr::DeclareWithVal { name, annotated_ty, val } => {
                let ty = match self.resolve_type(annotated_ty, &mut ir.types, ctx) {
                    Ok(t) => t,
                    Err(err) => {
                        ctx.errors.emit_span(err, annotated_ty.span().in_mod(ctx.module));
                        TypeInfo::Invalid
                    }
                };
                let ty = ir.types.add(ty);

                let var = self.declare_var(ir, ctx.src(*name).to_owned(), ty);

                self.reduce_expr_store_into_var(ctx, ir, &ctx.ast[*val], var, info.with_expected(ty));
                (Ref::UNIT, false)
            }
            ast::Expr::Return { start: _, val } => {
                info.mark_noreturn();
                let r = self.reduce_expr_idx_val(ctx, ir, *val, info.with_expected(info.ret));
                ir.specify(info.expected, TypeInfo::Primitive(Primitive::Never), &mut ctx.errors,
                    ctx.ast[*val].span(ctx.ast), &ctx.ctx);
                ir.add_untyped(Tag::Ret, Data { un_op: r });
                (Ref::UNDEF, false)
            }
            ast::Expr::IntLiteral(span) => {
                let s = ctx.src(*span);
                let lit = IntLiteral::parse(s);
                let int_ty = lit
                    .ty
                    .map_or(TypeInfo::Int, |int_ty| TypeInfo::Primitive(int_ty.into()));
                ir.specify(info.expected, int_ty, &mut ctx.errors, *span, &ctx.ctx);
                (if lit.val <= std::u64::MAX as u128 {
                    ir.add(
                        Data {
                            int: lit.val as u64,
                        },
                        Tag::Int,
                        info.expected,
                    )
                } else {
                    let extra = ir.extra_data(&lit.val.to_le_bytes());
                    ir.add(Data { extra }, Tag::LargeInt, info.expected)
                }, true)
            }
            ast::Expr::FloatLiteral(span) => {
                let lit = FloatLiteral::parse(ctx.src(*span));
                let float_ty = lit.ty.map_or(TypeInfo::Float, |float_ty| {
                    TypeInfo::Primitive(float_ty.into())
                });
                ir.specify(info.expected, float_ty, &mut ctx.errors, *span, &ctx.ctx);
                (ir.add(Data { float: lit.val }, Tag::Float, info.expected), true)
            }
            ast::Expr::StringLiteral(span) => {
                let lit = string_literal(*span, ctx.ast.src(ctx.module).0);
                (gen_string(&lit, ir, info.expected, *span, &mut ctx.errors, &ctx.ctx), true)
            }
            ast::Expr::BoolLiteral { val, start } => {
                let span = TSpan::new(*start, start + if *val {4} else {5});
                ir.specify(info.expected, TypeInfo::Primitive(Primitive::Bool), &mut ctx.errors, span, &ctx.ctx);
                (Ref::val(if *val { RefVal::True } else { RefVal::False }), true)
            }
            ast::Expr::EnumLiteral { dot: _, ident } => {
                let variant_name = ctx.src(*ident);
                let extra = ir.extra_data(variant_name.as_bytes());
                let variant_name_len = variant_name.len() as u32;
                // avoid creating enum TypeInfo unnecessarily to avoid allocations and complex comparisons
                if let TypeInfo::Enum(names) = ir.types.get_type(info.expected) {
                    if !ir.types.get_names(names).iter().any(|s| *s == variant_name) {
                        let new_names = ir.types.extend_names(names, std::iter::once(variant_name.to_owned()));
                        ir.types.update_type(info.expected, TypeInfo::Enum(new_names));
                    }
                } else {
                    let variant = ir.types.add_names(std::iter::once(variant_name.to_owned()));
                    ir.types.specify(
                        info.expected,
                        TypeInfo::Enum(variant),
                        &mut ctx.errors,
                        expr.span(ctx.ast).in_mod(ctx.module),
                        &ctx.ctx,
                    );
                }
                (ir.add(Data { extra_len: (extra, variant_name_len)  }, Tag::EnumLit, info.expected), true)
            }
            ast::Expr::Nested(_, inner) => {
                return self.reduce_expr_any(ctx, ir, &ctx.ast[*inner], info, get_var);
            }
            ast::Expr::Unit(span) => {
                ir.specify(info.expected, TypeInfo::Primitive(Primitive::Unit), &mut ctx.errors, *span, &ctx.ctx);
                (Ref::UNIT, true)
            }
            ast::Expr::Variable(span) => {
                let name = &ctx.ast.sources[ctx.module.idx()].0[span.range()];
                match self.resolve(name, ctx) {
                    Some(resolved) => return (match resolved {
                        Symbol::Var { ty, var } => {
                            ir.types.merge(ty, info.expected, &mut ctx.errors, ctx.module, *span, &ctx.ctx);
                            ExprResult::VarRef(var)
                        }
                        Symbol::GlobalVar(key) => {
                            let (ty, _) = ctx.ctx.get_global(key);
                            let ty_info = ty.as_info(&mut ir.types);
                            ir.specify(info.expected, ty_info, &mut ctx.errors, expr.span(ctx.ast), &ctx.ctx);
                            ExprResult::VarRef(ir.add(Data { symbol: key }, Tag::Global, info.expected))
                        }
                        Symbol::Func(f) => ExprResult::Func(f),
                        Symbol::Type(t) => ExprResult::Type(t),
                        Symbol::Trait(t) => ExprResult::Trait(t),
                        Symbol::LocalType(t) => ExprResult::LocalType(t),
                        Symbol::Module(m) => ExprResult::Module(m),
                        Symbol::Const(c) => {
                            let const_ty = self.get_or_gen_const(ctx, c, *span).type_info(&mut ir.types);
                            ir.specify(info.expected, const_ty, &mut ctx.errors, *span, &ctx.ctx);
                            let val = ctx.ctx.get_const(c);
                            self.const_val_to_result(val, ir, info)
                        }
                        Symbol::Generic(_) => todo!(),
                        Symbol::Invalid => {
                            ir.invalidate(info.expected);
                            ExprResult::Val(Ref::UNDEF)
                        }
                    }, true),
                    None => {
                        ctx.errors.emit_span(Error::UnknownIdent, span.in_mod(ctx.module));
                        ir.invalidate(info.expected);
                        (Ref::UNDEF, true)
                    }
                }
            }
            ast::Expr::Array(span, elems) => {
                let elems = &ctx.ast.expr_builder[*elems];
                let elem_ty = ir.types.add(TypeInfo::Unknown);
                let arr_ty = TypeInfo::Array(Some(elems.len() as u32), elem_ty);
                ir.types.specify(info.expected, arr_ty, &mut ctx.errors, span.in_mod(ctx.module), &ctx.ctx);
                //let arr = ir.add(Data { none: () }, Tag::Decl, expected);
                let arr = get_var(ir);
                let u64_ty = ir.types.add(TypeInfo::Primitive(Primitive::U64));
                for (i, elem) in elems.iter().enumerate() {
                    let elem_val = self.reduce_expr_val_spanned(ctx, ir, &ctx.ast[*elem], *span,
                        info.with_expected(elem_ty));
                    let idx = ir.add(Data { int: i as u64 }, Tag::Int, u64_ty);
                    let elem_ptr = ir.add(Data { bin_op: (arr, idx) }, Tag::Member, elem_ty);
                    ir.add_untyped(Tag::Store, Data { bin_op: (elem_ptr, elem_val) });
                }
                return (ExprResult::Stored(arr), true)
            }
            ast::Expr::Tuple(span, elems) => {
                let elems = ctx.ast.get_extra(*elems);
                let var = get_var(ir);
                let i32_ty = ir.types.add(TypeInfo::Primitive(Primitive::I32));
                let types = ir.types.add_multiple(std::iter::repeat(TypeInfo::Unknown).take(elems.len()));
                ir.types.specify(info.expected, TypeInfo::Tuple(types), &mut ctx.errors, span.in_mod(ctx.module), &ctx.ctx);
                for (i, elem) in elems.iter().enumerate() {
                    let member_ty = types.iter().nth(i).unwrap();
                    let member_val = self.reduce_expr_idx_val(ctx, ir, *elem, info.with_expected(member_ty));
                    let idx = ir.add(Data { int: i as u64 }, Tag::Int, i32_ty);
                    let member = ir.add(Data { bin_op: (var, idx) }, Tag::Member, member_ty);
                    ir.add_untyped(Tag::Store, Data { bin_op: (member, member_val) });
                }
                return (ExprResult::Stored(var), true);
            }
            ast::Expr::If { start: _, cond, then } => {
                let after_block = self.gen_if_then(ctx, ir, *cond, info.ret, info.noreturn);

                ir.specify(info.expected, TypeInfo::Primitive(Primitive::Unit), &mut ctx.errors, expr.span(ctx.ast), &ctx.ctx);
                let then_ty = ir.types.add(TypeInfo::Unknown);
                let mut then_noreturn = false;
                self.reduce_expr(ctx, ir, &ctx.ast[*then],
                    ExprInfo { expected: then_ty, noreturn: &mut then_noreturn, ret: info.ret});
                if !then_noreturn {
                    ir.add_untyped(Tag::Goto, Data { int32: after_block.0 });
                } else if !ir.currently_terminated() {
                    ir.add_unused_untyped(Tag::RetUndef, Data { none: () });
                }
                ir.begin_block(after_block);
                (Ref::UNIT, false)
            }
            ast::Expr::IfElse { start: _, cond, then, else_ } => {
                let else_block = self.gen_if_then(ctx, ir, *cond, info.ret, info.noreturn);
                let mut then_noreturn = false;
                let then_val = self.reduce_expr_idx_val(ctx, ir, *then, info.with_noreturn(&mut then_noreturn));
                let then_exit = ir.current_block();
                let after_block = if !then_noreturn {
                    let after_block = ir.create_block();
                    ir.add_untyped(Tag::Goto, Data { int32: after_block.0, });
                    Some(after_block)
                } else {
                    if !ir.currently_terminated() {
                        ir.add_unused_untyped(Tag::RetUndef, Data { none: () });
                    }
                    None
                };
                ir.begin_block(else_block);
                let mut else_noreturn = false;
                let else_val = self.reduce_expr_idx_val(ctx, ir, *else_, info.with_noreturn(&mut else_noreturn));
                let else_exit = ir.current_block();
                (if then_noreturn && else_noreturn {
                    *info.noreturn = true;
                    Ref::UNDEF
                } else {
                    let after_block = after_block.unwrap_or_else(|| ir.create_block());
                    if else_noreturn {
                        if !ir.currently_terminated() {
                            ir.add_unused_untyped(Tag::RetUndef, Data { none: () });
                        }
                    } else {
                        ir.add_untyped(Tag::Goto, Data { int32: after_block.0, });
                    }
                    ir.begin_block(after_block);
                    if then_noreturn {
                        else_val
                    } else if else_noreturn {
                        then_val
                    } else {
                        let extra = ir.extra_data(&then_exit.bytes());
                        ir.extra_data(&then_val.to_bytes());
                        ir.extra_data(&else_exit.bytes());
                        ir.extra_data(&else_val.to_bytes());
                        ir.add(Data { extra_len: (extra, 2) }, Tag::Phi, info.expected)
                    }
                }, false)
            }
            ast::Expr::While { start: _, cond, body } => {
                ir.specify(info.expected, TypeInfo::Primitive(Primitive::Unit), &mut ctx.errors, expr.span(ctx.ast), &ctx.ctx);

                let cond_block = ir.create_block();
                let body_block = ir.create_block();
                let after_block = ir.create_block();

                ir.add_untyped(Tag::Goto, Data { int32: cond_block.0 });
                ir.begin_block(cond_block);
                
                let b = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
                let cond = self.reduce_expr_idx_val(ctx, ir, *cond, info.with_expected(b));

                let branch_extra = ir.extra_data(&body_block.0.to_le_bytes());
                ir.extra_data(&after_block.0.to_le_bytes());
                ir.add_untyped(Tag::Branch, Data { branch: (cond, branch_extra) });
                ir.begin_block(body_block);
                let body_ty = ir.types.add(TypeInfo::Unknown);
                let mut body_noreturn = false;
                self.reduce_expr_idx_val(ctx, ir, *body,
                    ExprInfo { expected: body_ty, ret: info.ret, noreturn: &mut body_noreturn });
                if !body_noreturn {
                    ir.add_untyped(Tag::Goto, Data { int32: cond_block.0 });
                } else if !ir.currently_terminated() {
                    ir.add_unused_untyped(Tag::RetUndef, Data { none: () });
                }
                ir.begin_block(after_block);
                (Ref::UNIT, false)
            }
            ast::Expr::FunctionCall { func, args, end: _ } => {
                let args = &ctx.ast.expr_builder[*args];
                let called_ty = ir.types.add(TypeInfo::Unknown);
                fn gen_call(
                    scope: &mut Scope,
                    ctx: &mut GenCtx,
                    expr: &Expr,
                    func: SymbolKey,
                    this_arg: Option<(Ref, TypeTableIndex, TSpan)>,
                    args: impl ExactSizeIterator<Item = ExprRef>,
                    ir: &mut IrBuilder,
                    mut info: ExprInfo,
                ) -> Ref {
                    let arg_count = args.len() + if this_arg.is_some() { 1 } else { 0 };
                    
                    let header = ctx.ctx.funcs[func.idx()].header();
                    let return_type = header.return_type.as_info(&mut ir.types);

                    ir.specify(info.expected, return_type, &mut ctx.errors, expr.span(ctx.ast), &ctx.ctx);
                    if let TypeInfo::Primitive(Primitive::Never) = return_type {
                        *info.noreturn = true;
                    }

                    let invalid_arg_count = if header.varargs {
                        arg_count < header.params.len()
                    } else {
                        arg_count != header.params.len()
                    };
                    if invalid_arg_count {
                        ctx.errors.emit_span(Error::InvalidArgCount, expr.span(ctx.ast).in_mod(ctx.module));
                        Ref::UNDEF
                    } else {
                        let params = header.params.iter().map(|(_, ty)| Some(ty.clone()));
                        let params = if header.varargs {
                            params
                                .chain(std::iter::repeat(None))
                                .take(arg_count)
                                .collect::<Vec<_>>()
                        } else {
                            params.collect::<Vec<_>>()
                        };
                        let mut bytes = Vec::with_capacity(8 + 4 * arg_count);
                        bytes.extend(&func.bytes());
                        let mut param_iter = params.iter();
                        if let Some((this, this_ty, this_span)) = this_arg {
                            let ty = param_iter.next().unwrap(); // argument count was checked above, this can't fail
                            match ty {
                                Some(ty) => {
                                    let info = ty.as_info(&mut ir.types);
                                    ir.types.specify(this_ty, info, &mut ctx.errors,
                                        this_span.in_mod(ctx.module), &ctx.ctx
                                    );
                                    bytes.extend(this.to_bytes());
                                }
                                None => {
                                    ctx.errors.emit_span(Error::NotAnInstanceMethod, this_span.in_mod(ctx.module));
                                }
                            }
                        }
                        for (arg, ty) in args.zip(param_iter) {
                            let type_info = ty.as_ref().map_or(TypeInfo::Unknown, |ty| ty.as_info(&mut ir.types));
                            let ty = ir
                                .types
                                .add(type_info);
                            let expr = scope.reduce_expr_idx_val(ctx, ir, arg, info.with_expected(ty));
                            bytes.extend(&expr.to_bytes());
                        }
                        let extra = ir.extra_data(&bytes);
                        ir.add(Data { extra_len: (extra, arg_count as u32) }, Tag::Call, info.expected)
                    }
                }
                let called = &ctx.ast[*func];
                (match self.reduce_expr(ctx, ir, called, info.with_expected(called_ty)) {
                    ExprResult::Func(key) => {
                        gen_call(self, ctx, expr, key, None, args.iter().copied(), ir, info)
                    }
                    //TODO: Trait function calls
                    ExprResult::Method(self_var, key) => {
                        let called_span = called.span(ctx.ast);
                        let this = Some((self_var, called_ty, called_span));
                        gen_call(self, ctx, expr, key, this, args.iter().copied(), ir, info)
                    }
                    ExprResult::Type(ty) => {
                        let (_, TypeDef::Struct(struct_)) = &ctx.ctx.types[ty.idx()] else {
                            ctx.errors.emit_span(Error::FunctionOrStructTypeExpected, ctx.span(called));
                            return (ExprResult::Val(Ref::UNDEF), false)
                        };
                        let generics = ir.types.add_multiple((0..struct_.generic_count).map(|_| TypeInfo::Unknown));
                        ir.specify(info.expected, TypeInfo::Resolved(ty, generics), &mut ctx.errors, expr.span(ctx.ast),
                            &ctx.ctx);

                        if args.len() == struct_.members.len() {
                            let var = get_var(ir);
                            let member_types: Vec<_> =
                                struct_.members.iter()
                                    .map(|(_, ty)| ty.as_info_generic(&mut ir.types, generics))
                                    .collect();
                            let i32_ty = ir.types.add(TypeInfo::Primitive(Primitive::I32));
                            for (i, (member_val, member_ty)) in
                                args.iter().zip(member_types).enumerate()
                            {
                                let member_ty = ir.types.add_info_or_idx(member_ty);
                                let member_val =
                                    self.reduce_expr_idx_val(ctx, ir, *member_val, info.with_expected(member_ty));
                                let idx = ir.add(Data { int: i as u64 }, Tag::Int, i32_ty);
                                let member = ir.add(
                                    Data {
                                        bin_op: (var, idx),
                                    },
                                    Tag::Member,
                                    member_ty,
                                );
                                ir.add_untyped(Tag::Store, Data { bin_op: (member, member_val) });
                            }
                            return (ExprResult::Stored(var), true);
                        } else {
                            ctx.errors.emit_span(Error::InvalidArgCount, expr.span(ctx.ast).in_mod(ctx.module));
                            return (ExprResult::Val(Ref::UNDEF), true)
                        }
                    }
                    _ => {
                        if !ir.types.get_type(called_ty).is_invalid() {
                            ctx.errors.emit_span(
                                Error::FunctionOrStructTypeExpected,
                                called.span(ctx.ast).in_mod(ctx.module)
                            );
                        }
                        ir.invalidate(info.expected);
                        Ref::UNDEF
                    }
                }, false)
            }
            ast::Expr::UnOp(_, un_op, val) => {
                let span = expr.span(ctx.ast);
                let (inner_expected, tag) = match un_op {
                    UnOp::Neg => (info.expected, Tag::Neg),
                    UnOp::Not => (ir.types.add(TypeInfo::Primitive(Primitive::Bool)), Tag::Not),
                    UnOp::Ref => {
                        let ptr_ty = TypeInfo::Pointer(ir.types.add(TypeInfo::Unknown));
                        ir.types.specify(info.expected, ptr_ty, &mut ctx.errors, span.in_mod(ctx.module), &ctx.ctx);
                        let inner_expected = match ir.types.get_type(info.expected) {
                            TypeInfo::Pointer(inner) => inner,
                            _ => ir.types.add(TypeInfo::Invalid)
                        };
                        return (ExprResult::Val(match 
                            self.reduce_expr(ctx, ir, &ctx.ast[*val], info.with_expected(inner_expected))
                        {
                            ExprResult::VarRef(r) | ExprResult::Stored(r) => {
                                ir.types.specify(info.expected, TypeInfo::Pointer(inner_expected),
                                    &mut ctx.errors, span.in_mod(ctx.module), &ctx.ctx);
                                ir.add(Data { un_op: r }, Tag::AsPointer, info.expected)
                            }
                            ExprResult::Val(val) => {
                                let val_expected = match ir.types.get_type(info.expected) {
                                    TypeInfo::Pointer(inner) => inner,
                                    _ => ir.types.add(TypeInfo::Invalid)
                                };
                                let var = ir.add(Data { none: () }, Tag::Decl, val_expected);
                                ir.add_unused_untyped(Tag::Store, Data { bin_op: (var, val) });
                                ir.add(Data { un_op: var }, Tag::AsPointer, info.expected)
                            }
                            _ => {
                                ctx.errors.emit_span(Error::CantTakeRef, expr.span(ctx.ast).in_mod(ctx.module));
                                Ref::UNDEF
                            }
                        }), true)
                    }
                    UnOp::Deref => {
                        let expected = ir.types.add(TypeInfo::Pointer(info.expected));
                        let pointer_val = 
                            self.reduce_expr_idx_val(ctx, ir, *val, info.with_expected(expected));
                        return (ExprResult::VarRef(pointer_val), true); // just use the pointer value as variable
                    }
                };
                let inner = self.reduce_expr_idx_val(ctx, ir, *val, info.with_expected(inner_expected));
                let res = match un_op {
                    UnOp::Neg => match ir.types.get_type(inner_expected) {
                        TypeInfo::Float | TypeInfo::Int | TypeInfo::Unknown => Ok(()),
                        TypeInfo::Primitive(p) => {
                            if let Some(int) = p.as_int() {
                                if int.is_signed() {
                                    Ok(())
                                } else {
                                    Err(Error::CantNegateType)
                                }
                            } else if p.as_float().is_some() {
                                Ok(())
                            } else {
                                Err(Error::CantNegateType)
                            }
                        }
                        _ => Err(Error::CantNegateType),
                    }
                    UnOp::Not => Ok(()), // type was already constrained before
                    UnOp::Ref | UnOp::Deref => unreachable!(),
                };
                if let Err(err) = res {
                    ctx.errors.emit_span(err, ctx.span(expr));
                }
                (ir.add(Data { un_op: inner }, tag, inner_expected), true)
            }
            ast::Expr::BinOp(op, l, r) => {
                if let Operator::Assignment(assignment) = op {
                    ir.specify(info.expected, TypeInfo::UNIT, &mut ctx.errors, expr.span(ctx.ast), &ctx.ctx);
                    let var_ty = ir.types.add_unknown();
                    let lval = self.reduce_lval_expr(ctx, ir, &ctx.ast[*l], info.with_expected(var_ty),
                        Error::CantAssignTo);
                    let r = self.reduce_expr_idx_val(ctx, ir, *r, info.with_expected(var_ty));

                    let val = if *assignment == AssignType::Assign {
                        r
                    } else {
                        let left_val = ir.add(Data { un_op: lval }, Tag::Load, var_ty);
                        let tag = match assignment {
                            AssignType::Assign => unreachable!(),
                            AssignType::AddAssign => Tag::Add,
                            AssignType::SubAssign => Tag::Sub,
                            AssignType::MulAssign => Tag::Mul,
                            AssignType::DivAssign => Tag::Div,
                            AssignType::ModAssign => Tag::Mod,
                        };
                        ir.add(Data { bin_op: (left_val, r) }, tag, var_ty)
                    };
                    ir.add_untyped(Tag::Store, Data { bin_op: (lval, val) });
                    (Ref::UNDEF, false)
                } else {
                    // binary operations always require the same type on both sides right now
                    let inner_ty = if op.is_boolean() {
                        ir.types.add(TypeInfo::Primitive(Primitive::Bool))
                    } else if op.is_logical() {
                        ir.types.add(TypeInfo::Unknown)
                    } else {
                        info.expected
                    };
                    let l = self.reduce_expr_idx_val(ctx, ir, *l, info.with_expected(inner_ty));
                    let r = self.reduce_expr_idx_val(ctx, ir, *r, info.with_expected(inner_ty));
                    let tag = match op {
                        Operator::Add => Tag::Add,
                        Operator::Sub => Tag::Sub,
                        Operator::Mul => Tag::Mul,
                        Operator::Div => Tag::Div,
                        Operator::Mod => Tag::Mod,

                        Operator::Or => Tag::Or,
                        Operator::And => Tag::And,
    
                        Operator::Equals => Tag::Eq,
                        Operator::NotEquals => Tag::Ne,
    
                        Operator::LT => Tag::LT,
                        Operator::GT => Tag::GT,
                        Operator::LE => Tag::LE,
                        Operator::GE => Tag::GE,

                        Operator::Assignment(_) => unreachable!()
                    };
                    (ir.add(Data { bin_op: (l, r) }, tag, info.expected), true)
                }
            }
            ast::Expr::MemberAccess { left, name: name_span } => {
                let member = &ctx.ast.src(ctx.module).0[name_span.range()];
                let left_ty = ir.types.add(TypeInfo::Unknown);
                enum MemberAccessType {
                    Var(Ref),
                    Module(ModuleId),
                    Associated(SymbolKey),
                    TraitFunction(SymbolKey),
                    Invalid
                }
                let left = &ctx.ast[*left];
                let left_val = match self.reduce_expr(ctx, ir, left, info.with_expected(left_ty)) {
                    ExprResult::VarRef(r) | ExprResult::Stored(r) => MemberAccessType::Var(r),
                    ExprResult::Val(val) => {
                        let var = ir.add(Data { none: () }, Tag::Decl, info.expected);
                        ir.add_unused_untyped(Tag::Store, Data { bin_op: (var, val) });
                        MemberAccessType::Var(var)
                    }
                    ExprResult::Type(ty) => MemberAccessType::Associated(ty),
                    ExprResult::Trait(t) => MemberAccessType::TraitFunction(t),
                    ExprResult::Func(_) | ExprResult::TraitFunc(_, _) | ExprResult::Method(_, _)
                    | ExprResult::LocalType(_) => {
                        ctx.errors.emit_span(Error::NonexistantMember, name_span.in_mod(ctx.module));
                        MemberAccessType::Invalid
                    }
                    ExprResult::Module(id) => MemberAccessType::Module(id),
                };

                (match left_val {
                    MemberAccessType::Var(var) => {
                        let (ty, idx) = match ir.types.get_type(left_ty) {
                            TypeInfo::Resolved(key, generics) => {
                                match &ctx.ctx.types[key.idx()].1 {
                                    TypeDef::Struct(struct_) => {
                                        if let Some(method) = struct_.methods.get(member) {
                                            return (ExprResult::Method(var, *method), true);
                                        } else if let Some((i, (_, ty))) = struct_
                                            .members
                                            .iter()
                                            .enumerate()
                                            .find(|(_, (name, _))| name == member)
                                        {
                                            (ty.as_info_generic(&mut ir.types, generics), i)
                                        } else {
                                            ctx.errors.emit_span(Error::NonexistantMember, name_span.in_mod(ctx.module));
                                            (TypeInfo::Invalid.into(), 0)
                                        }
                                    }
                                    TypeDef::Enum(_) => {
                                        todo!("Enum functions")
                                    }
                                    TypeDef::NotGenerated { .. } => unreachable!()
                                }
                            }
                            TypeInfo::Invalid => (TypeInfo::Invalid.into(), 0),
                            TypeInfo::Unknown => {
                                ctx.errors.emit_span(Error::TypeMustBeKnownHere, ctx.span(left));
                                (TypeInfo::Invalid.into(), 0)
                            }
                            _ => {
                                ctx.errors.emit_span(Error::NonexistantMember, name_span.in_mod(ctx.module));
                                (TypeInfo::Invalid.into(), 0)
                            }
                        };
                        ir.types.specify_or_merge(info.expected, ty, &mut ctx.errors, ctx.module, expr.span(ctx.ast),
                            &ctx.ctx);
                        let i32_ty = ir.types.add(TypeInfo::Primitive(Primitive::I32));
                        let idx = ir.add(
                            Data { int: idx as u64 },
                            Tag::Int,
                            i32_ty
                        );
                        let member = ir.add(Data { bin_op: (var, idx) }, Tag::Member, info.expected);
                        return (ExprResult::VarRef(member), true);
                    }
                    MemberAccessType::Module(id) => {
                        if let Some(symbol) = resolve_module_symbol(ctx, id, member) {
                            return (match symbol {
                                Symbol::Func(f) => ExprResult::Func(f),
                                Symbol::Type(t) => ExprResult::Type(t),
                                Symbol::Trait(t) => ExprResult::Trait(t),
                                Symbol::LocalType(t) => ExprResult::LocalType(t),
                                Symbol::Generic(_) => todo!(), // is this a possibility
                                Symbol::Module(m) => ExprResult::Module(m),
                                Symbol::Var { .. } => unreachable!("vars in module shouldn't exist"),
                                Symbol::GlobalVar(key) => {
                                    let (ty, _) = ctx.ctx.get_global(key);
                                    let ty_info = ty.as_info(&mut ir.types);
                                    let span = name_span.in_mod(ctx.module);
                                    ir.types.specify(info.expected, ty_info, &mut ctx.errors, span, &ctx.ctx);
                                    ExprResult::VarRef(ir.add(Data { symbol: key }, Tag::Global, info.expected))
                                }
                                Symbol::Const(key) => {
                                    let val = ctx.ctx.get_const(key);
                                    self.const_val_to_result(val, ir, info)
                                }
                                Symbol::Invalid => {
                                    ir.invalidate(info.expected);
                                    ExprResult::Val(Ref::UNDEF)
                                }
                            }, true);
                        } else {
                            ctx.errors.emit_span(Error::UnknownIdent, name_span.in_mod(ctx.module));
                            ir.invalidate(info.expected);
                            Ref::UNDEF
                        }
                    }
                    MemberAccessType::Associated(key) => {
                        match ctx.ctx.get_type(key) {
                            TypeDef::Struct(def) => {
                                if let Some(method) = def.methods.get(member) {
                                    return (ExprResult::Func(*method), true);
                                } else {
                                    ctx.errors.emit_span(Error::UnknownFunction, name_span.in_mod(ctx.module));
                                    ir.invalidate(info.expected);
                                    Ref::UNDEF
                                }
                            }
                            TypeDef::Enum(def) => {
                                let expr_span = ctx.span(expr);
                                return (if let Some(&variant) = def.variants.get(member) {
                                    ir.types.specify(info.expected, TypeInfo::Resolved(key, TypeTableIndices::EMPTY),
                                        &mut ctx.errors, expr_span, &ctx.ctx);
                                    let r = ir.add(Data { int: variant as u64 }, Tag::Int, info.expected);
                                    ExprResult::Val(r)
                                } else {
                                    ctx.errors.emit_span(Error::NonexistantEnumVariant, name_span.in_mod(ctx.module));
                                    ir.invalidate(info.expected);
                                    ExprResult::Val(Ref::UNDEF)
                                }, true)
                            }
                            TypeDef::NotGenerated { .. } => unreachable!()
                        }
                    }
                    MemberAccessType::TraitFunction(t) => {
                        if let Some((idx, _)) = ctx.ctx.get_trait(t).functions.get(member) {
                            return (ExprResult::TraitFunc(t, *idx), true);
                        } else {
                            ctx.errors.emit_span(Error::UnknownFunction, name_span.in_mod(ctx.module));
                            ir.invalidate(info.expected);
                            Ref::UNDEF
                        }
                    }
                    MemberAccessType::Invalid => {
                        ir.invalidate(info.expected);
                        Ref::UNDEF
                    }
                }, true)
            }
            ast::Expr::Index { expr: indexed, idx, end: _ } => {
                let array_ty = ir.types.add(TypeInfo::Array(None, info.expected));
                let indexed = &ctx.ast[*indexed];
                let val = self.reduce_lval_expr(ctx, ir, indexed, info.with_expected(array_ty), Error::CantIndex);
                
                let idx_ty = ir.types.add(TypeInfo::Int);
                let idx_expr = &ctx.ast[*idx];
                let idx = self.reduce_expr_val_spanned(ctx, ir, idx_expr,
                    idx_expr.span(ctx.ast), info.with_expected(idx_ty));
                return (ExprResult::VarRef(
                    ir.add(Data { bin_op: (val, idx) }, Tag::Member, info.expected)
                ), true)
            }
            ast::Expr::TupleIdx { expr: indexed, idx, end: _ } => {
                let indexed_ty = ir.types.add(TypeInfo::Unknown);
                let res = self.reduce_expr(ctx, ir, &ctx.ast[*indexed], info.with_expected(indexed_ty));
                let expr_var = match res {
                    ExprResult::VarRef(r) | ExprResult::Stored(r) => r,
                    ExprResult::Val(val) => {
                        let var = ir.add(Data { none: () }, Tag::Decl, info.expected);
                        ir.add_unused_untyped(Tag::Store, Data { bin_op: (var, val) });
                        var
                    }
                    ExprResult::Func(_) | ExprResult::TraitFunc(_, _) | ExprResult::Method(_, _) 
                    | ExprResult::Type(_)
                    | ExprResult::Trait(_)
                    | ExprResult::LocalType(_)
                    | ExprResult::Module(_) => {
                        ctx.errors.emit_span(Error::TupleIndexingOnNonValue, ctx.span(expr));
                        ir.invalidate(info.expected);
                        return (ExprResult::Val(Ref::UNDEF), true)
                    }
                };
                let TypeInfo::Tuple(elems) = ir.types.get_type(indexed_ty) else {
                    ctx.errors.emit_span(Error::TypeMustBeKnownHere, ctx.span(expr));
                    return (ExprResult::Val(Ref::UNDEF), true)
                };
                let Some(elem_ty) = elems.iter().nth(*idx as usize) else {
                    ctx.errors.emit_span(Error::TupleIndexOutOfRange, ctx.span(expr));
                    return (ExprResult::Val(Ref::UNDEF), true)
                };
                ir.types.merge(info.expected, elem_ty, &mut ctx.errors, ctx.module, expr.span(ctx.ast), &ctx.ctx);
                let i32_ty = ir.types.add(TypeInfo::Primitive(Primitive::I32));
                let idx = ir.add(Data { int: *idx as _ }, Tag::Int, i32_ty);
                return (ExprResult::VarRef(ir.add(Data { bin_op: (expr_var, idx) }, Tag::Member, elem_ty)), true);
            }
            ast::Expr::Cast(span, target, val) => {
                let target = match self.resolve_type(target, &mut ir.types, ctx) {
                    Ok(target) => target,
                    Err(err) => {
                        ctx.errors.emit_span(err, span.in_mod(ctx.module));
                        TypeInfo::Invalid
                    }
                };

                ir.specify(info.expected, target, &mut ctx.errors, expr.span(ctx.ast), &ctx.ctx);
                let inner_ty = ir.types.add(TypeInfo::Unknown);
                let val = self.reduce_expr_idx_val(ctx, ir, *val, info.with_expected(inner_ty));
                //TODO: check table for available casts
                (ir.add(Data { un_op: val, }, Tag::Cast, info.expected), true)
            }
            ast::Expr::Root(_) => {
                return (ExprResult::Module(ModuleId::ROOT), true)
            }
            ast::Expr::Asm { span: _, asm_str_span, args } => {
                let expr_refs = ctx.ast.get_extra(*args).iter()
                .map(|arg| {
                    let expr = &ctx.ast[*arg];
                    let info = info.with_expected(ir.types.add_unknown());
                    self.reduce_expr_val_spanned(ctx, ir, expr, expr.span(ctx.ast), info)
                })
                .collect::<Vec<_>>();
                assert!(expr_refs.len() <= u16::MAX as usize, "too many arguments for inline assembly");
                
                let asm_str = ctx.src(TSpan::new(asm_str_span.start + 1, asm_str_span.end - 1));
                assert!(asm_str.len() <= u16::MAX as usize, "inline assembly string is too long");
                let extra = ir.extra_data(asm_str.as_bytes());
                for &r in &expr_refs {
                    ir.extra_data(&r.to_bytes());
                }
                ir.add_unused_untyped(Tag::Asm, Data { asm: (extra, asm_str.len() as u16, expr_refs.len() as u16) });
                return (ExprResult::Val(Ref::UNDEF), false)
            }
        };
        (ExprResult::Val(r), should_use)
    }

    fn gen_if_then(&mut self, ctx: &mut GenCtx, ir: &mut IrBuilder, cond: ExprRef, ret: TypeTableIndex,
        noreturn: &mut bool)
    -> BlockIndex {
        let b = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
        let cond = self.reduce_expr_idx_val(ctx, ir, cond, ExprInfo { expected: b, ret, noreturn });
        let then_block = ir.create_block();
        let other_block = ir.create_block();

        let branch_extra = ir.extra_data(&then_block.0.to_le_bytes());
        ir.extra_data(&other_block.0.to_le_bytes());

        ir.add_untyped(Tag::Branch, Data { branch: (cond, branch_extra) });
        ir.begin_block(then_block);
        other_block
    }

    fn get_or_gen_const<'a>(&'a mut self, ctx: &'a mut GenCtx, key: SymbolKey, span: TSpan) -> &'a ConstVal {
        if let ConstVal::NotGenerated = ctx.ctx.get_const_mut(key) {
            ctx.errors.emit_span(Error::RecursiveDefinition, span.in_mod(ctx.module));
            ctx.ctx.consts[key.idx()] = ConstVal::Invalid;
        }
        &ctx.ctx.consts[key.idx()]
    }

    fn const_val_to_result(&self, val: &ConstVal, ir: &mut IrBuilder, info: ExprInfo)
    -> ExprResult {
        /*
        else {
            let const_ty = val.type_info(&mut ir.types);
            let val = build_const_val(val, name_span.in_mod(module),
                ir, info.expected, errors);
            ir.specify(info.expected, const_ty, errors, expr.span(self.ast), self.ctx);
            ExprResult::Val(val)
        }
        */
        ExprResult::Val(match val {
            &ConstVal::Symbol(symbol) => {
                return match symbol {
                    Symbol::Func(key) => ExprResult::Func(key),
                    Symbol::Type(key) => ExprResult::Type(key),
                    Symbol::Trait(key) => ExprResult::Trait(key),
                    Symbol::LocalType(..) => unreachable!(),
                    Symbol::Generic(_) => todo!(),
                    Symbol::Module(key) => ExprResult::Module(key),
                    Symbol::Invalid => {
                        ir.invalidate(info.expected);
                        ExprResult::Val(Ref::UNDEF)
                    }
                    Symbol::Var { .. } | Symbol::GlobalVar(_) | Symbol::Const(_) => unreachable!(),
                }
            }
            ConstVal::Invalid => Ref::UNDEF,
            ConstVal::Unit => Ref::UNIT,
            ConstVal::Int(val) => {
                if *val > u64::MAX as i128 || *val < -(u64::MAX as i128) {
                    todo!("Large ints aren't implemented");
                }
                if *val < 0 {
                    let positive_val = ir.add(Data { int: (-*val) as u64 }, Tag::Int, info.expected);
                    ir.add(Data { un_op: positive_val }, Tag::Neg, info.expected)
                } else {
                    ir.add(Data { int: *val as u64 }, Tag::Int, info.expected)
                }
            }
            ConstVal::Float(val) => ir.add(Data { float: *val }, Tag::Float, info.expected),
            ConstVal::String(val) => {
                let extra = ir.extra_data(val.as_bytes());
                ir.add(Data { extra_len: (extra, val.len() as u32) }, Tag::String, info.expected)
            }
            ConstVal::EnumVariant(variant) => {
                let extra = ir.extra_data(variant.as_bytes());
                ir.add(Data { extra_len: (extra, variant.len() as u32) }, Tag::EnumLit, info.expected)
            }
            ConstVal::Bool(false) => Ref::val(RefVal::False),
            ConstVal::Bool(true) => Ref::val(RefVal::True),
            ConstVal::NotGenerated { .. } => todo!("Handle recursive const evaluation"),
        })
    }

    // move to types.rs
    fn eval_const(&mut self, ctx: &mut GenCtx, ty: Option<&ast::UnresolvedType>, val: ExprRef)
    -> EyeResult<ConstVal> {
        #![allow(unused)]
        use crate::error::CompileError;

        let expr = &ctx.ast[val];
        Ok(match expr {
            // ast::Expr::Block { span, items, defs } => todo!(),
            // ast::Expr::Declare { name, annotated_ty, end } => todo!(),
            // ast::Expr::DeclareWithVal { name, annotated_ty, val } => todo!(),
            // ast::Expr::Return { start, val } => todo!(),
            ast::Expr::IntLiteral(span) => ConstVal::Int(ctx.src(*span).parse().unwrap()),
            ast::Expr::FloatLiteral(span) => ConstVal::Float(ctx.src(*span).parse().unwrap()),
            ast::Expr::StringLiteral(span) => ConstVal::String(string_literal(*span, ctx.ast.src(ctx.module).0)),
            ast::Expr::BoolLiteral { start, val } => ConstVal::Bool(*val),
            ast::Expr::EnumLiteral { dot, ident } => ConstVal::EnumVariant(ctx.src(*ident).to_owned()),
            ast::Expr::Nested(_, inner) => self.eval_const(ctx, ty, *inner)?,
            ast::Expr::Unit(_) => ConstVal::Unit,
            ast::Expr::Variable(span) => {
                let name = ctx.src(*span).to_owned(); // PERF: ownership
                let symbol = self.resolve(&name, ctx)
                    .ok_or_else(|| Error::UnknownIdent.at_span(span.in_mod(ctx.module)))?;
                match symbol {
                    Symbol::Var { .. } => todo!(),
                    Symbol::Func(key) => ConstVal::Symbol(Symbol::Func(key)),
                    Symbol::Type(key) => ConstVal::Symbol(Symbol::Type(key)),
                    Symbol::Trait(key) => ConstVal::Symbol(Symbol::Trait(key)),
                    Symbol::Module(key) => ConstVal::Symbol(Symbol::Module(key)),
                    Symbol::Const(key) => {
                        self.get_or_gen_const(ctx, key, *span).clone()
                    }
                    Symbol::Invalid => ConstVal::Invalid,
                    Symbol::LocalType(_)
                    | Symbol::GlobalVar(_)
                    | Symbol::Generic(_) => return Err(Error::NotConst.at_span(span.in_mod(ctx.module))),
                }
            }
            // ast::Expr::Array(_, _) => todo!(),
            // ast::Expr::Tuple(_, _) => todo!(),
            ast::Expr::If { .. }
            | ast::Expr::IfElse { .. }
            | ast::Expr::While { .. }
            | ast::Expr::FunctionCall { .. }
            => return Err(CompileError::new(Error::NotConst, ctx.span(expr))),
            ast::Expr::UnOp(_, op, inner) => {
                let val = self.eval_const(ctx, ty, *inner)?;
                if val.is_invalid() { return Ok(ConstVal::Invalid) }
                match op {
                    ast::UnOp::Neg => {
                        let ConstVal::Int(int_val) = val else {
                            return Err(CompileError::new(Error::CantNegateType, ctx.span(&ctx.ast[*inner])));
                        };
                        ConstVal::Int(-int_val)
                    }
                    ast::UnOp::Not => {
                        let ConstVal::Bool(bool_val) = val else {
                            return Err(CompileError::new(Error::UnexpectedType, ctx.span(&ctx.ast[*inner])));
                        };
                        ConstVal::Bool(!bool_val)
                    }
                    ast::UnOp::Ref | ast::UnOp::Deref => return Err(CompileError::new(
                        Error::UnexpectedType, ctx.span(expr))),
                }
            }
            ast::Expr::BinOp(op, l, r) => {
                let l_val = self.eval_const(ctx, None, *l)?;
                let r_val = self.eval_const(ctx, None, *r)?;

                if l_val.is_invalid() || r_val.is_invalid() { return Ok(ConstVal::Invalid); }


                match op {
                    Operator::Assignment(_) => {
                        return Err(Error::NotConst.at_span(ctx.span(expr)));
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
                                                        Error::MismatchedType, ctx.span(expr)
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
                            Error::UnexpectedType, ctx.span(&ctx.ast[*l]))) };
                        let ConstVal::Bool(r) = r_val else { return Err(CompileError::new(
                            Error::UnexpectedType, ctx.span(&ctx.ast[*r]))) };
                        ConstVal::Bool(match op {
                            Operator::Or => l || r,
                            Operator::And => l && r,
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
                                                    Error::MismatchedType, ctx.span(expr)
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
            _ => return Err(CompileError::new(Error::NotConst, ctx.span(expr)))
        })
    }
}

pub fn string_literal(span: TSpan, src: &str) -> String {
    src[span.start as usize + 1 ..= span.end as usize - 1]
        .replace("\\n", "\n")
        .replace("\\t", "\t")
        .replace("\\r", "\r")
        .replace("\\0", "\0")
        .replace("\\\"", "\"")
}

fn gen_string(string: &str, ir: &mut IrBuilder, expected: TypeTableIndex, span: TSpan, errors: &mut Errors,
    ctx: &TypingCtx) -> Ref 
{
    let i8_ty = ir.types.add(TypeInfo::Primitive(Primitive::I8));
    ir.specify(expected, TypeInfo::Pointer(i8_ty), errors, span, ctx);
        
    let extra_len = ir._extra_len(string.as_bytes());
    // add zero byte
    ir.extra_data(&[b'\0']);
    ir.add(Data { extra_len }, Tag::String, expected)
}
