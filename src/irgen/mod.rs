use std::{ptr::NonNull, mem};

use crate::{
    ast::{self, Expr, ModuleId, ExprRef, IdentPath, UnresolvedType},
    error::{Error, Errors, EyeResult},
    token::IntLiteral,
    types::{Primitive, IntType},
    span::{Span, TSpan},
    dmap::{self, DHashMap}, resolve::types::SymbolTable,
}; 

mod call;
mod const_eval;
mod expr;
mod pat;

pub use crate::ir::builder::IrBuilder;

pub struct GenCtx<'s> {
    pub ast: &'s ast::Ast,
    pub symbols: &'s SymbolTable,
    pub module: ModuleId,
    pub errors: Errors,
}
impl<'s> GenCtx<'s> {
    pub fn span(&self, expr: &Expr) -> Span {
        expr.span_in(self.ast, self.module)
    }
    pub fn ref_span(&self, expr: ExprRef) -> Span {
        self.ast[expr].span_in(self.ast, self.module)
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

#[derive(Debug)]
enum ExprResult {
    // not actually a value of the specified type but a pointer.
    // Necessary for assignments/patterns etc and to save loads/stores.
    VarRef(Ref),
    Val(Ref),

    // Ignore the result (underscore token: _). Used mostly in lhs.
    Hole,

    /// method call on a variable: x.method
    Method {
        self_val: Ref,
        self_ty: TypeTableIndex,
        method_symbol: StructMemberSymbol
    },
    
    Symbol(ConstSymbol),
}
impl ExprResult {
    const UNDEF: Self = Self::Val(Ref::UNDEF);

    pub fn get_or_load(
        self,
        ir: &mut IrBuilder,
        ctx: &TypingCtx,
        ty: TypeTableIndex,
        errors: &mut Errors,
        span: Span,
    ) -> Ref {
        match self {
            ExprResult::VarRef(var) => {
                ir.build_load(var, ty)
            }
            ExprResult::Val(val) => val,
            ExprResult::Hole => {
                errors.emit_span(Error::ExpectedValueFoundHole, span);
                Ref::UNDEF
            }
            ExprResult::Method { .. } => {
                errors.emit_span(Error::ExpectedValueFoundFunction, span);
                Ref::UNDEF
            }
            ExprResult::Symbol(symbol) => {
                symbol.add_instruction(ir, ctx, ty, errors, span)
            }
        }
    }
}

pub fn reduce(ast: &ast::Ast, main_module: ModuleId, mut errors: Errors, require_main_func: bool)
-> (Result<(ir::Module, Globals), ()>, Errors) {
    let mut ctx = TypingCtx::new();
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

    
    let main = if require_main_func {
        if let Some(&Symbol::Func(func)) = globals[main_module].get("main") {
            let mut gen_ctx = GenCtx { ctx, globals, ast, module: main_module, errors };

            let FunctionOrHeader::Func(eye_main) = &mut gen_ctx.ctx.funcs[func.idx()] else { unreachable!() };
            debug_assert_eq!(eye_main.header.name, "main");
            eye_main.header.name = "eyemain".to_owned();
            
            let return_type = eye_main.header.return_type.clone();
            let res = main_wrapper(func, &mut gen_ctx, return_type);

            errors = gen_ctx.errors;
            globals = gen_ctx.globals;
            ctx = gen_ctx.ctx;

            match res {
                Ok(main) => Some(main),
                Err(err) => {
                    errors.emit_err(err);
                    return (Err(()), errors)
                }
            }
        } else {
            return (Err(()), errors);
        }
    } else { None };

    let global_vars: Vec<_> = globals.iter().filter_map(|(name, symbol)| {
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
        });

    let funcs = if let Some(main) = main {
        funcs.chain(std::iter::once(main)).collect()
    } else {
        funcs.collect()
    };
    (
        Ok((
            ir::Module {
                name: "MainModule".to_owned(),
                funcs,
                globals: global_vars,
                types: ctx.types,
            },
            globals
        )),
        errors,
    )
}

/// Add hidden function wrapping and calling main to handle exit codes properly.
/// This will return the main functions exit code casted to i32 if it is an integer.
/// If the main returns unit, it will always return 0.
fn main_wrapper(eye_main: SymbolKey, ctx: &mut GenCtx, main_return_ty: Type) -> EyeResult<Function> {
    let mut builder = IrBuilder::new(ctx.module);
    //let extra = builder.extra_data(&eye_main.bytes());

    let main_return = match main_return_ty {
        Type::Prim(Primitive::Unit) => None,
        Type::Prim(p) if p.is_int() => Some(p.as_int().unwrap()),
        _ => {
            let ty_string = main_return_ty.display_fn(|key| &ctx.ctx.funcs[key.idx()].header().name).to_string();
            return Err(Error::InvalidMainReturnType(ty_string).at_span(Span::_todo(ctx.module)))
        }
    };

    let main_ret_ty = builder.types.add(
        main_return.map_or(TypeInfo::UNIT, |int_ty| TypeInfo::Primitive(int_ty.into()))
    );
    let i32_ty = builder.types.add(TypeInfo::Primitive(Primitive::I32));

    let main_val = builder.build_call(eye_main, [], main_ret_ty);
    let exit_code = match main_return {
        Some(IntType::I32) => main_val,
        Some(_) => builder.build_cast(main_val, i32_ty),
        None => builder.build_int(0, i32_ty)
    };
    builder.build_ret(exit_code);
    
    let ir = builder.finish(ctx);

    Ok(Function {
        header: FunctionHeader {
            name: "main".to_owned(),
            params: vec![],
            varargs: false,
            return_type: Type::Prim(Primitive::I32)
        },
        ir: Some(ir)
    })
}

fn generate_bodies(
    scope: &mut Scope,
    defs: &DHashMap<String, ast::Definition>,
    gen_ctx: &mut GenCtx,
) {
    for (name, def) in defs {
        if scope.get_scope_symbol(gen_ctx.globals.get_ref(), name).is_some() { continue }
        gen_definition(name, def, scope, gen_ctx,
            |scope, name, symbol, ctx| scope.add_symbol(name, symbol, &mut ctx.globals));
    }
}

fn gen_definition(
    name: &str,
    def: &ast::Definition,
    scope: &mut Scope,
    ctx: &mut GenCtx,
    add_symbol: impl FnOnce(&mut Scope, String, Symbol, &mut GenCtx)
) -> Symbol {
    match def {
        // TODO: extra_generics should be passed to func_def for generic functions in generic functions
        ast::Definition::Function(func) => func_def(func, name, scope, ctx, vec![], add_symbol),
        ast::Definition::Struct(def) => {
            let key = ctx.ctx.add_proto_ty(name.to_owned(), def.generics.len() as _);
            add_symbol(scope, name.to_owned(), Symbol::Type(key), ctx);
            gen_struct(def, ctx, scope, key);
            Symbol::Type(key)
        }
        ast::Definition::Enum(def) => {
            let key = ctx.ctx.add_proto_ty(name.to_owned(), def.generics.len() as _);
            add_symbol(scope, name.to_owned(), Symbol::Type(key), ctx);
            gen_enum(def, ctx, scope, key);
            Symbol::Type(key)
        }
        ast::Definition::Trait(def) => {
            let trait_ = gen_trait(def, ctx, scope);
            let symbol = Symbol::Trait(ctx.ctx.add_trait(trait_));
            add_symbol(scope, name.to_owned(), symbol.clone(), ctx);
            symbol
        }
        ast::Definition::Module(id) => {
            add_symbol(scope, name.to_owned(), Symbol::Module(*id), ctx);
            Symbol::Module(*id)
        }
        ast::Definition::Use(path) => {
            let symbol = resolve_path(path, ctx, scope);
            add_symbol(scope, name.to_owned(), symbol.clone(), ctx);
            symbol
        },
        ast::Definition::Const(ty, expr) => {
            let key = ctx.ctx.add_const(ConstVal::NotGenerated);
            add_symbol(scope, name.to_owned(), Symbol::Const(key), ctx);
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
            add_symbol(scope, name.to_owned(), symbol.clone(), ctx);
            symbol
        }
    }
}

fn func_def(func: &ast::Function, name: &str, scope: &mut Scope, ctx: &mut GenCtx,
    extra_generics: Vec<String>,
    add_symbol: impl FnOnce(&mut Scope, String, Symbol, &mut GenCtx)
) -> Symbol {
    if func.generics.is_empty() && extra_generics.len() == 0 {
        let func_info = gen_func_header(name.to_owned(), func, scope, ctx);
        let header = FunctionOrHeader::Header(func_info);
        let key = ctx.ctx.add_func(header);
        add_symbol(scope, name.to_owned(), Symbol::Func(key), ctx);
        gen_func_body(func, key, scope, ctx, []);
        Symbol::Func(key)
    } else {
        if func.generics.len() + extra_generics.len() > u8::MAX as usize {
            ctx.errors.emit_span(Error::TooManyGenerics(func.generics.len()), func.span.in_mod(ctx.module));
        }
        let mut symbols = dmap::new();
        for (i, name) in func.generics.iter().enumerate() {
            let name = ctx.src(*name);
            symbols.insert(name.to_owned(), Symbol::Generic((extra_generics.len() + i) as u8));
        }
        let defs = dmap::new();

        let mut func_scope = scope.child(&mut symbols, &defs);
        let header = gen_func_header(name.to_owned(), func, &mut func_scope, ctx);
        crate::log!("Header of {}: {:?}", name, header);
        // TODO: PERF: cloning here is kind of ugly

        let mut generics = extra_generics;
        for name in &func.generics {
            generics.push(ctx.src(*name).to_owned());
        }

        let symbol = Symbol::GenericFunc(ctx.ctx.add_generic_func(GenericFunc {
            name: name.to_owned(),
            header, 
            def: func.clone(), // PERF: cloning is suboptimal here
            generics,
            instantiations: dmap::new(),
            module: ctx.module,
        }));
        add_symbol(scope, name.to_owned(), symbol.clone(), ctx);
        symbol
    }
}

fn gen_func_header(name: String, func: &ast::Function, scope: &mut Scope, ctx: &mut GenCtx)
-> FunctionHeader {
    let params = func.params.iter()
        .map(|(name, unresolved, _, _)| {
            let ty = scope.resolve_uninferred_type(unresolved, ctx);
            (name.clone(), ty)
        })
        .collect();
    let return_type = scope.resolve_uninferred_type(&func.return_type, ctx);

    FunctionHeader {
        name,
        params,
        varargs: func.varargs,
        return_type,
    }
}
pub fn gen_func_body<'a>(def: &ast::Function, key: SymbolKey, scope: &mut Scope, ctx: &mut GenCtx,
    generics: impl IntoIterator<Item = (&'a str, Type)>
) {
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
        
        for (name, generic) in generics.into_iter() {
            scope_symbols.insert(name.to_owned(), Symbol::TypeValue(generic));
        }
        for (i, (name, ty)) in header.params.iter().enumerate() {
            let info = ty.as_info(&mut builder.types);
            let ty = builder.types.add(info);
            let ptr_ty = builder.types.add(TypeInfo::Pointer(ty));
            let param = builder.build_param(i as u32, ptr_ty);
            scope_symbols.insert(name.clone(), Symbol::Var { ty, var: param });
        }
        let scope_defs = dmap::new();
        let mut scope: Scope<'_> = scope.child(&mut scope_symbols, &scope_defs);
        let return_type = header.return_type.as_info(&mut builder.types);
        let expected = builder.types.add(return_type);
        let mut noreturn = false;
        let val = expr::val_expr(&mut scope, ctx, &mut builder, *body,
            expr::ExprInfo { expected, ret: expected, noreturn: &mut noreturn });
        if !noreturn {
            if header.return_type == Type::Prim(Primitive::Unit) {
                builder.build_ret(Ref::UNIT);
            } else if !ctx.ast[*body].is_block() {
                builder.build_ret(val);
            } else {
                ctx.errors.emit_span(Error::MissingReturnValue, ctx.ref_span(*body));
            }
        } else if !builder.currently_terminated() {
            builder.build_ret_undef();
        }
        builder.finish(ctx)
    });

    ctx.ctx.funcs[func_idx] = FunctionOrHeader::Func(Function {
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
    if def.generics.len() > u8::MAX as _ {
        ctx.errors.emit_span(Error::TooManyGenerics(def.generics.len()), Span::_todo(ctx.module));
    }
    let mut symbols = def.generics.iter()
        .enumerate()
        .map(|(i, span)| (ctx.src(*span).to_owned(), Symbol::Generic(i as u8)))
        .collect();
    let scope_defs = dmap::new();
    let mut scope = scope.child(&mut symbols, &scope_defs);

    let members = def.members.iter().map(|(name, unresolved, _start, _end)| {
        let ty = scope.resolve_uninferred_type(unresolved, ctx);
        (
            name.clone(),
            ty,
        )
    }).collect::<Vec<_>>();

    let loc = ctx.ctx.get_type_mut(key);
    let TypeDef::NotGenerated { name, .. } = loc else { unreachable!() };
    let name = mem::take(name);
    *loc = TypeDef::Struct(Struct {
        name,
        members,
        symbols: dmap::with_capacity(def.members.len()),
        generic_count: def.generics.len() as u8,
    });

    for (method_name, method) in &def.methods {
        let generics = def.generics
            .iter()
            .map(|span| ctx.src(*span).to_owned())
            .collect();
        func_def(method, &method_name, &mut scope, ctx, generics,
            |scope, name, symbol, ctx| {
                scope.add_symbol(name, symbol.clone(), &mut ctx.globals);
                let TypeDef::Struct(Struct { symbols, .. }) = ctx.ctx.get_type_mut(key) else {
                    unreachable!()
                };

                let symbol = match symbol {
                    Symbol::Func(s) => StructMemberSymbol::Func(s),
                    Symbol::GenericFunc(s) => StructMemberSymbol::GenericFunc(s),
                    _ => unreachable!()
                };
                symbols.insert(method_name.clone(), symbol);
        });
    }
}

fn gen_enum(
    def: &ast::EnumDefinition,
    ctx: &mut GenCtx,
    scope: &mut Scope,
    key: SymbolKey,
) {
    let mut generic_symbols = def.generics.iter()
    .enumerate()
    .map(|(i, span)| (ctx.src(*span).to_owned(), Symbol::Generic(i as u8)))
    .collect();
    let scope_defs = dmap::new();
    let mut _scope = scope.child(&mut generic_symbols, &scope_defs);

    let variants = def.variants.iter()
        .enumerate()
        .map(|(idx, (_span, name))| (name.clone(), idx as u32))
        .collect();

    let loc = ctx.ctx.get_type_mut(key);
    let TypeDef::NotGenerated { name, .. } = loc else { unreachable!() };
    let name = mem::take(name);
    *loc = TypeDef::Enum(Enum {
        name,
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
        .map(|(i, (name, (_span, func)))| (
            name.clone(),
            (i as u32, gen_func_header(name.to_owned(), func, &mut scope, ctx))
        ))
        .collect();
    TraitDef { functions }
}

fn resolve_path(path: &IdentPath, ctx: &mut GenCtx, scope: &mut Scope) -> Symbol {
    enum State {
        Local,
        Module(ModuleId)
    }
    let (root, segments, last) = path.segments(ctx.ast.src(ctx.module).0);
    let mut state = if root.is_some() { State::Module(ctx.ast[ctx.module].root_module) } else { State::Local };
    
    for (segment, segment_span) in segments {
        let symbol = match state {
            State::Local => scope.resolve(segment, ctx),
            State::Module(id) => ctx.resolve_module_symbol(id, segment)
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
            State::Module(id) => ctx.resolve_module_symbol(id, last)
        };
        if let Some(symbol) = symbol {
            symbol
        } else {
            ctx.errors.emit_span(Error::UnknownIdent, last_span.in_mod(ctx.module));
            Symbol::Invalid
        }
    } else {
        // there can't be no last symbol and not a single module because then there wouldn't be any path.
        let State::Module(id) = state else { unreachable!() };
        Symbol::Module(id)
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
        }.get(name).cloned()
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
                &mut Scope::Module(id) => return ctx.resolve_module_symbol(id, name),
                Scope::Local { parent: _, symbols, defs } => {
                    if let Some(symbol) = symbols.get(name).cloned()
                    .or_else(|| defs.get(name).map(|def| gen_definition(name, def, current, ctx,
                        |scope, name, symbol, ctx| scope.add_symbol(name, symbol, &mut ctx.globals)
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
        

    fn resolve_type(&mut self, unresolved: &UnresolvedType, types: &mut TypeTable, ctx: &mut GenCtx)
    -> Result<TypeInfo, Error> {
        // TODO: using ctx.module might lead to bugs in multiple places here
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
                    ModuleOrLocal::Module(ctx.ast[ctx.module].root_module)
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
                        types.add_multiple_unknown(generic_count as _)
                    })
                };
                let resolved = match current_module {
                    ModuleOrLocal::Module(m) => ctx.globals[m]
                        .get(last.0)
                        .ok_or(Error::UnknownIdent)?.clone(),
                    ModuleOrLocal::Local => self.resolve(last.0, ctx).ok_or(Error::UnknownIdent)?
                };

                match resolved  {
                    Symbol::Type(ty) => {
                        let generics = resolve_generics(ctx, self, ty)?;
                        Ok(TypeInfo::Resolved(ty, generics))
                    }
                    Symbol::Const(key) => {
                        match ctx.ctx.get_const(key) {
                            &ConstVal::Symbol(ConstSymbol::Type(key)) => {
                                let generics = resolve_generics(ctx, self, key)?;
                                Ok(TypeInfo::Resolved(key, generics))
                            }
                            _ => Err(Error::TypeExpected)
                        }
                    }
                    Symbol::TypeValue(ty) => {
                        Ok(ty.as_info(types))
                    }
                    _ => Err(Error::TypeExpected)
                } 
            }
            ast::UnresolvedType::Pointer(ptr) => {
                let (inner, _) = &**ptr;
                let inner = self.resolve_type(inner, types, ctx)?;
                Ok(TypeInfo::Pointer(types.add(inner)))
            }
            ast::UnresolvedType::Array(array) => {
                let (inner, _, count) = &**array;
                let inner = self.resolve_type(inner, types, ctx)?;
                let inner = types.add(inner);
                Ok(TypeInfo::Array(*count, inner))
            }
            ast::UnresolvedType::Tuple(elems, _) => {
                let elems = elems.iter().map(|ty| self.resolve_type(ty, types, ctx)).collect::<Result<Vec<_>, _>>()?;
                Ok(TypeInfo::Tuple(types.add_multiple(elems), ir::TupleCountMode::Exact))
            }
            ast::UnresolvedType::Infer(_) => Ok(TypeInfo::Unknown)
        }
    }

    // fn resolve_uninferred_type(&mut self, unresolved: &UnresolvedType, ctx: &mut GenCtx) -> Type { panic!() }
    fn resolve_uninferred_type(&mut self, unresolved: &UnresolvedType, ctx: &mut GenCtx)
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
                    ModuleOrLocal::Module(ctx.ast[ctx.module].root_module)
                } else {
                    ModuleOrLocal::Local
                };

                for segment in iter {
                    let look_from = match current_module {
                        ModuleOrLocal::Module(m) => m,
                        ModuleOrLocal::Local => ctx.module
                    };
                    match ctx.resolve_module_symbol(look_from, segment.0) {
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
                    } else if generic_count != 0 {
                        ctx.errors.emit_span(
                            Error::InvalidGenericCount { expected: generic_count, found: 0 },
                            unresolved.span().in_mod(ctx.module)
                        );
                        return Err(())
                    } else {
                        Vec::new()
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
                                if let Ok(generics) = resolve_generics(ctx, self, ty) {
                                    Type::Id(ty, generics)
                                } else {
                                    Type::Invalid
                                }
                                // let Ok(generics) = resolve_generics(ctx, self, ty) else { return Type::Invalid };
                                // Type::Id(ty, generics)
                            }
                            Some(Symbol::Const(key)) => {
                                if let &ConstVal::Symbol(ConstSymbol::Type(key)) = ctx.ctx.get_const(*key) {
                                    if let Ok(generics) = resolve_generics(ctx, self, key) {
                                        Type::Id(key, generics)
                                    } else {
                                        Type::Invalid
                                    }
                                } else {
                                    ctx.errors.emit_span(Error::TypeExpected, last.1.in_mod(ctx.module));
                                    Type::Invalid
                                }
                            }
                            _ => {
                                ctx.errors.emit_span(Error::TypeExpected, last.1.in_mod(ctx.module));
                                Type::Invalid
                            }
                        },
                    ModuleOrLocal::Local => match self.resolve(last.0, ctx) {
                        Some(Symbol::Type(ty)) => {
                            if let Ok(generics) = resolve_generics(ctx, self, ty) {
                                Type::Id(ty, generics)
                            } else {
                                Type::Invalid
                            }
                        }
                        Some(Symbol::Generic(i)) => Type::Generic(i),
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
            ast::UnresolvedType::Pointer(ptr) => {
                let (inner, _) = &**ptr;
                let inner = self.resolve_uninferred_type(inner, ctx);
                Type::Pointer(Box::new(inner))
            }
            ast::UnresolvedType::Array(array) => {
                let (inner, _, count) = &**array;
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

    pub fn declare_var(&mut self, ir: &mut IrBuilder, name: String, ty: TypeTableIndex) -> Ref {
        let var = ir.build_decl(ty);
        match self {
            Scope::Module(_) => unreachable!("There shouldn't be variables defined in the global scope"),
            Scope::Local { symbols, .. } => {
                symbols.insert(name, Symbol::Var { ty, var  });
            }
        }
        var
    }

    fn get_or_gen_const<'a>(ctx: &'a mut GenCtx, key: SymbolKey, span: TSpan) -> &'a ConstVal {
        if let ConstVal::NotGenerated = ctx.ctx.get_const_mut(key) {
            ctx.errors.emit_span(Error::RecursiveDefinition, span.in_mod(ctx.module));
            ctx.ctx.consts[key.idx()] = ConstVal::Invalid;
        }
        &ctx.ctx.consts[key.idx()]
    }

    // move to types.rs
    fn eval_const(&mut self, ctx: &mut GenCtx, ty: Option<&UnresolvedType>, val: ExprRef)
    -> EyeResult<ConstVal> {
        let err_count = ctx.errors.error_count();
        let mut builder = IrBuilder::new(ctx.module);
        let expected = ty.map_or(Ok(TypeInfo::Unknown),
            |t| self.resolve_type(t, &mut builder.types, ctx).map_err(|e| e.at_span(t.span().in_mod(ctx.module))))?;
        let expected_info = builder.types.add(expected);
        let mut noreturn = false;
        let r = expr::val_expr(self, ctx, &mut builder, val, expr::ExprInfo {
            expected: expected_info,
            ret: expected_info,
            noreturn: &mut noreturn,
        });
        if !noreturn {
            if matches!(expected, TypeInfo::Primitive(Primitive::Unit)) {
                builder.build_ret(Ref::UNIT);
            } else if !ctx.ast[val].is_block() {
                builder.build_ret(r);
            } else {
                ctx.errors.emit_span(Error::MissingReturnValue, ctx.ref_span(val));
            }
        } else if !builder.currently_terminated() {
            builder.build_ret_undef();
        }

        if err_count != ctx.errors.error_count() {
            eprintln!("Errors found while evaluating constant: {:?}", ctx.errors);
        }
        
        ir::eval::eval(&builder, &[])
            .map_err(|err| err.at_span(ctx.ref_span(val)))
    }
}

pub fn string_literal(span: TSpan, src: &str) -> String {
    src[span.start as usize + 1 .. span.end as usize]
        .replace("\\n", "\n")
        .replace("\\t", "\t")
        .replace("\\r", "\r")
        .replace("\\0", "\0")
        .replace("\\\"", "\"")
}

fn int_literal(lit: IntLiteral, span: TSpan, ir: &mut IrBuilder, expected: TypeTableIndex, ctx: &mut GenCtx) -> Ref {
    // TODO: check int type for overflow
    let int_ty = lit
        .ty
        .map_or(TypeInfo::Int, |int_ty| TypeInfo::Primitive(int_ty.into()));
    ir.specify(expected, int_ty, &mut ctx.errors, span, &ctx.ctx);
    
    if lit.val <= std::u64::MAX as u128 {
        ir.build_int(lit.val as u64, expected)
    } else {
        ir.build_large_int(lit.val, expected)
    }
}

fn gen_string(string: &str, ir: &mut IrBuilder, expected: TypeTableIndex, span: TSpan, errors: &mut Errors,
    ctx: &TypingCtx) -> Ref {
    let i8_ty = ir.types.add(TypeInfo::Primitive(Primitive::I8));
    ir.specify(expected, TypeInfo::Pointer(i8_ty), errors, span, ctx);
        
    ir.build_string(string.as_bytes(), true, expected)
}
