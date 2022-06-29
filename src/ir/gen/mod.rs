use crate::{
    ast::{self, Expr, ModuleId, UnOp, ExprRef},
    error::{Error, Errors, EyeResult},
    lexer::tokens::{Operator, AssignType, IntLiteral, FloatLiteral},
    types::Primitive, span::{Span, TSpan},
};
use std::{borrow::{Cow, Borrow}, collections::HashMap, ptr::NonNull};
use builder::IrBuilder;
use self::types::{GlobalsRef, Globals};

use super::{typing::*, *};

mod types;
mod builder;

pub fn reduce(ast: &ast::Ast, mut errors: Errors, require_main_func: bool) 
-> Result<(Module, Globals), Errors> {
    let mut ctx = TypingCtx {
        funcs: Vec::new(),
        types: Vec::new(),
        traits: Vec::new(),
        consts: Vec::new(),
    };
    let globals = types::gen_globals(ast, &mut ctx, &mut errors);

    for (id, module) in ast.modules.iter().enumerate() {
        let id = ModuleId::new(id as u32);
        let mut scope = Scope::new(&mut ctx, &globals[id], &ast[module.definitions], globals.get_ref(), ast, id);

        generate_bodies(&mut scope, &ast[module.definitions], &mut errors,
            |scope, name| scope.globals[scope.module].get(name)
        );
    }
    if errors.has_errors() {
        return Err(errors);
    }
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
            return Err(errors)
        });
    }
    

    Ok((
        Module {
            name: "MainModule".to_owned(),
            funcs,
            main,
            types: ctx.types,
        },
        globals
    ))
}

// should be called after gen_globals or gen_locals to generate the bodies of all the prototypes that were created
fn generate_bodies(
    scope: &mut Scope,
    defs: &HashMap<String, ast::Definition>,
    errors: &mut Errors,
    get_symbol: impl for<'a> Fn(&'a mut Scope, &str) -> Option<&'a Symbol>,
) {
    let gen = |name: &String, def: &ast::Function, key: SymbolKey, scope: &mut Scope, errors: &mut Errors| {
        let func_idx = key.idx();
        let header = match &scope.ctx.funcs[func_idx] {
            FunctionOrHeader::Func(_) => {
                // this might happen in the future when functions need to know other function's bodies
                unreachable!("Function shouldn't already be defined here")
            }
            FunctionOrHeader::Header(header) => header.clone(),
        };
        let ir = def.body.as_ref().map(|body| {
            let mut builder = IrBuilder::new(scope.module);
            let mut scope_symbols = HashMap::with_capacity(header.params.len() + def.generics.len());
            
            for generic in &def.generics {
                let name = &scope.ast.src(scope.module).0[generic.range()];
                let generic_ty = builder.types.add(TypeInfo::Unknown);
                scope_symbols.insert(name.to_owned(), Symbol::LocalType(generic_ty));
            }
            for (i, (name, ty)) in header.params.iter().enumerate() {
                let info = ty.as_info(&mut builder.types);
                let ty = builder.types.add(info);
                let param = builder.add(Data { int32: i as u32 }, Tag::Param, ty);
                scope_symbols.insert(name.clone(), Symbol::Var { ty, var: param });
            }
            let mut scope: Scope<'_> = scope.child(scope_symbols, defs);
            let return_type = header.return_type.as_info(&mut builder.types);
            let expected = builder.types.add(return_type);
            let mut noreturn = false;
            let body = &scope.ast[*body];
            let body_span = body.span(scope.ast);
            let val = scope.reduce_expr_val_spanned(errors, &mut builder, body, body_span,
                ExprInfo { expected, ret: expected, noreturn: &mut noreturn });
            if !noreturn {
                if header.return_type == Type::Prim(Primitive::Unit) {
                    builder.add_unused_untyped(Tag::Ret, Data { un_op: Ref::UNIT });
                } else if !body.is_block() {
                    builder.add_unused_untyped(Tag::Ret, Data { un_op: val });
                } else {
                    errors.emit_span(Error::MissingReturnValue, body_span.in_mod(scope.module));
                }
            } else if !builder.currently_terminated() {
                builder.add_unused_untyped(Tag::RetUndef, Data { none: () });
            }
            builder.finish()
        });

        scope.ctx.funcs[func_idx] = FunctionOrHeader::Func(Function {
            name: name.clone(),
            header,
            ir,
        });
    };
    for (name, def) in defs {
        match def {
            ast::Definition::Function(func) => {
                let Symbol::Func(key) = get_symbol(scope, name)
                    .expect("Missing function after definition phase")
                    else { panic!("Function expected") };
                gen(name, func, *key, scope, errors);
            }
            ast::Definition::Struct(struct_) => {
                let Some(&Symbol::Type(ty)) = get_symbol(scope, name)
                    else { panic!("Struct expected") };
                let TypeDef::Struct(def) = scope.ctx.get_type(ty) else { unreachable!() };
                // this is a bit ugly for borrowing reasons, maybe the allocation can be removed
                let methods = def.methods.clone();

                for (name, method) in &struct_.methods {
                    let key = methods.get(name).unwrap();
                    gen(name, method, *key, scope, errors);
                }
            }
            ast::Definition::Const(ty, expr) => {
                let &Symbol::Const(key) = get_symbol(scope, name)
                    .expect("Missing constant after definition phase")
                    else { panic!("Const expected") };

                let val = match scope.eval_const(Some(ty), *expr, errors) {
                    Ok(val) => val,
                    Err(err) => {
                        errors.emit_err(err);
                        ConstVal::Invalid
                    }
                };
                scope.ctx.consts[key.idx()] = val;
            }
            _ => {}
        }
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
    Const(SymbolKey),
}

struct ScopeInfo<'a> {
    parent: Option<NonNull<ScopeInfo<'a>>>,
    symbols: Cow<'a, HashMap<String, Symbol>>,
    defs: &'a HashMap<String, ast::Definition>,
}
impl<'a> ScopeInfo<'a> {
    fn parent(&self) -> Option<&ScopeInfo<'a>> {
        self.parent
            .as_ref()
            .map(|parent| unsafe { parent.as_ref() })
    }
    fn reborrow(&self) -> ScopeInfo {
        ScopeInfo { parent: self.parent, symbols: Cow::Borrowed(self.symbols.borrow()), defs: self.defs }
    }

    fn resolve_local(&self, name: &str) -> Result<Resolved, Error> {
        self.resolve_local_recursive(name, 0)
    }

    fn resolve_local_recursive(&self, name: &str, depth: usize) -> Result<Resolved, Error> {
        //TODO: check if this is recursing with some kind of stack and return recursive type def error.
        if let Some(symbol) = self.symbols.get(name) {
            Ok(match symbol {
                Symbol::Func(f) => Resolved::Func(*f),
                Symbol::Type(t) => Resolved::Type(*t),
                Symbol::Trait(t) => Resolved::Trait(*t),
                Symbol::LocalType(t) => Resolved::LocalType(*t),
                Symbol::Generic(_) => todo!(),
                Symbol::Module(m) => Resolved::Module(*m),
                Symbol::Var { ty, var } => Resolved::Var(*ty, *var),
                Symbol::Const(c) => Resolved::Const(*c),
            })
        } else {
            self.parent()
                .map(|parent| parent.resolve_local_recursive(name, depth + 1))
                .transpose()?
                .ok_or(Error::UnknownIdent)
        }
    }
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
    pub fn add_trait(&mut self, t: TraitDef) -> SymbolKey {
        let key = SymbolKey(self.traits.len() as u64);
        self.traits.push(t);
        key
    }
    pub fn add_proto_ty(&mut self, name: String, generic_count: u8) -> SymbolKey {
        self.add_type(name, TypeDef::Struct(Struct {
            members: Vec::new(),
            methods: HashMap::new(),
            generic_count,
            name: String::new()
        }))
    }
    pub fn add_const(&mut self, c: ConstVal) -> SymbolKey {
        let key = SymbolKey(self.consts.len() as u64);
        self.consts.push(c);
        key
    }
    pub fn get_type(&self, key: SymbolKey) -> &TypeDef { &self.types[key.idx()].1 }
    pub fn get_type_mut(&mut self, key: SymbolKey) -> &mut TypeDef { &mut self.types[key.idx()].1 }
    //pub fn get_func(&self, key: SymbolKey) -> &FunctionOrHeader { &self.funcs[key.idx()] }
    //pub fn get_func_mut(&mut self, key: SymbolKey) -> &mut FunctionOrHeader { &mut self.funcs[key.idx()] }
    pub fn get_trait(&self, key: SymbolKey) -> &TraitDef { &self.traits[key.idx()] }
    pub fn get_const(&self, key: SymbolKey) -> &ConstVal { &self.consts[key.idx()] }
    pub fn get_const_mut(&mut self, key: SymbolKey) -> &mut ConstVal { &mut self.consts[key.idx()] }
}

enum Resolved {
    Var(TypeTableIndex, Ref),
    Func(SymbolKey),
    Type(SymbolKey),
    Trait(SymbolKey),
    LocalType(TypeTableIndex),
    Module(ModuleId),
    Const(SymbolKey),
}
impl Resolved {
    pub fn into_symbol(self) -> Option<Symbol> {
        match self {
            Resolved::Var(_, _) | Resolved::LocalType(_) => None,
            Resolved::Func(id) => Some(Symbol::Func(id)),
            Resolved::Type(id) => Some(Symbol::Type(id)),
            Resolved::Trait(t) => Some(Symbol::Trait(t)),
            Resolved::Module(id) => Some(Symbol::Module(id)),
            Resolved::Const(id) => Some(Symbol::Const(id)),
        }
    }
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

pub struct Scope<'s> {
    ctx: &'s mut TypingCtx,
    globals: GlobalsRef<'s>,
    pub ast: &'s ast::Ast,
    module: ModuleId,
    info: ScopeInfo<'s>,
}

impl<'s> Scope<'s> {
    pub fn new(
        ctx: &'s mut TypingCtx,
        symbols: &'s HashMap<String, Symbol>,
        defs: &'s HashMap<String, ast::Definition>,
        globals: GlobalsRef<'s>,
        ast: &'s ast::Ast,
        module: ModuleId,
    ) -> Self {
        Self {
            ctx,
            globals,
            ast,
            module,
            info: ScopeInfo {
                parent: None,
                symbols: Cow::Borrowed(symbols),
                defs
            },
        }
    }
    pub fn reborrow(&mut self) -> Scope {
        Scope {
            ctx: &mut *self.ctx,
            globals: self.globals,
            ast: self.ast,
            module: self.module,
            info: self.info.reborrow()
        }
    }
    pub fn tspan(&self, expr: ExprRef) -> TSpan {
        self.ast[expr].span(self.ast)
    }
    pub fn span(&self, expr: &Expr) -> Span {
        expr.span_in(self.ast, self.module)
    }
    pub fn src(&self, span: TSpan) -> &str {
        &self.ast.sources()[self.module.idx()].0[span.range()]
    }
    pub fn child<'c>(&'c mut self, symbols: HashMap<String, Symbol>, defs: &'c HashMap<String, ast::Definition>)
    -> Scope<'c>
    where 's: 'c {
        Scope {
            ctx: &mut *self.ctx,
            globals: self.globals,
            ast: self.ast,
            module: self.module,
            info: ScopeInfo {
                parent: Some(NonNull::from(&mut self.info)),
                symbols: Cow::Owned(symbols),
                defs,
            },
        }
    }

    fn resolve(&self, name: &str) -> Result<Resolved, Error> {
        self.info.resolve_local(name)
    }

    fn resolve_type(&mut self, unresolved: &ast::UnresolvedType, types: &mut TypeTable) -> Result<TypeInfo, Error> {
        match unresolved {
            ast::UnresolvedType::Primitive(p, _) => Ok(TypeInfo::Primitive(*p)),
            ast::UnresolvedType::Unresolved(path, generics) => {
                let (root, iter, last) = path.segments(self.ast.src(self.module).0);
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
                        ModuleOrLocal::Local => self.module
                    };
                    match self.globals[look_from].get(segment.0) {
                        Some(Symbol::Module(m)) => current_module = ModuleOrLocal::Module(*m),
                        Some(_) => panic!("1"),//return Err(Error::ModuleExpected),
                        None => return Err(Error::UnknownModule)
                    }
                }
                let mut resolve_generics = |s: &mut Scope, key: SymbolKey| {
                    let generic_count = s.ctx.get_type(key).generic_count();
                    Ok(if let Some((generics, _)) = generics {
                        if generics.len() != generic_count as usize {
                            return Err(Error::InvalidGenericCount {
                                expected: generic_count,
                                found: generics.len() as u8
                            })
                        }
                        let generics = generics.iter()
                            .map(|ty| s.resolve_type(ty, types))
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
                    ModuleOrLocal::Module(m) => match self.globals[m]
                        .get(last.0)
                        .ok_or(Error::UnknownIdent)? {
                            &Symbol::Type(ty) => {
                                let generics = resolve_generics(self, ty)?;
                                Ok(TypeInfo::Resolved(ty, generics))
                            }
                            // TODO: might require a new solution to allow inference of local types
                            Symbol::LocalType(ty) => Ok(types.get_type(*ty)),
                            Symbol::Const(key) => {
                                match self.ctx.get_const(*key) {
                                    &ConstVal::Symbol(Symbol::Type(key)) => {
                                        let generics = resolve_generics(self, key)?;
                                        Ok(TypeInfo::Resolved(key, generics))
                                    }
                                    _ => Err(Error::TypeExpected)
                                }
                            }
                            _ => Err(Error::TypeExpected)
                        },
                    ModuleOrLocal::Local => match self.info.resolve_local(last.0)? {
                        Resolved::Type(ty) => {
                            let generics = resolve_generics(self, ty)?;
                            Ok(TypeInfo::Resolved(ty, generics))
                        }
                        //TODO: local generics?
                        Resolved::LocalType(ty) => Ok(types.get_type(ty)),
                        _ => Err(Error::TypeExpected)
                    }
                }
            }
            ast::UnresolvedType::Pointer(box (inner, _)) => {
                let inner = self.resolve_type(inner, types)?;
                Ok(TypeInfo::Pointer(types.add(inner)))
            }
            ast::UnresolvedType::Array(box (inner, _, count)) => {
                let inner = self.resolve_type(inner, types)?;
                let inner = types.add(inner);
                Ok(TypeInfo::Array(*count, inner))
            }
            ast::UnresolvedType::Tuple(elems, _) => {
                let elems = elems.iter().map(|ty| self.resolve_type(ty, types)).collect::<Result<Vec<_>, _>>()?;
                Ok(TypeInfo::Tuple(types.add_multiple(elems)))
            }
            ast::UnresolvedType::Infer(_) => Ok(TypeInfo::Unknown)
        }
    }

    fn declare_var(&mut self, ir: &mut IrBuilder, name: String, ty: TypeTableIndex) -> Ref {
        let var = ir.add(Data { none: () }, Tag::Decl, ty);
        self.info
            .symbols
            .to_mut()
            .insert(name, Symbol::Var { ty, var });
        var
    }

    fn reduce_expr_val_spanned(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        expr: &Expr,
        span: TSpan,
        mut info: ExprInfo,
    ) -> Ref {
        self.reduce_expr(errors, ir, expr, info.reborrow())
            .get_or_load(ir, info.expected, errors, span.in_mod(self.module))
    }

    fn reduce_expr_idx_val(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        expr: ExprRef,
        info: ExprInfo,
    ) -> Ref {
        self.reduce_expr_val_spanned(errors, ir, &self.ast[expr], self.tspan(expr), info)
    }

    fn reduce_expr(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        expr: &Expr,
        mut info: ExprInfo,
    ) -> ExprResult {
        let expected = info.expected;
        self.reduce_expr_any(
            errors, ir, expr, info.reborrow(),
            |ir| ir.add(Data { none: () }, Tag::Decl, expected), // declare new var
        )
    }

    fn reduce_expr_store_into_var(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        expr: &Expr,
        var: Ref,
        mut info: ExprInfo,
    ) {
        let val = match self.reduce_expr_any(errors, ir, expr, info.reborrow(), |_| var) {
            ExprResult::Stored(_) => return,
            ExprResult::VarRef(other_var) => ir.add(Data { un_op: other_var }, Tag::Load, info.expected),
            ExprResult::Val(val) => val,
            _ => {
                errors.emit_span(Error::ExpectedValueFoundDefinition, expr.span(self.ast).in_mod(self.module));
                Ref::UNDEF
            }
        };
        ir.add_unused_untyped(Tag::Store, Data { bin_op: (var, val) });
    }

    fn reduce_lval_expr(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        expr: &Expr,
        mut info: ExprInfo,
        error: Error,
    ) -> Ref {
        let expected = info.expected;
        match self.reduce_expr_any(
            errors, ir, expr, info.reborrow(),
            |ir| ir.add(Data { none: () }, Tag::Decl, expected)
        ) {
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
                    errors.emit_span(error, expr.span(self.ast).in_mod(self.module));
                }
                Ref::UNDEF
            }
        }
    }

    fn reduce_expr_any(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        expr: &Expr,
        mut info: ExprInfo,
        get_var: impl Fn(&mut IrBuilder) -> Ref,
    ) -> ExprResult {
        let r = match expr {
            ast::Expr::Block { span, items, defs } => {
                let locals = types::gen_locals(self, *defs, errors);
                let defs = &self.ast.expr_builder[*defs];
                
                let mut block_scope = self.child(locals, defs);
                generate_bodies(&mut block_scope, defs, errors,
                    |scope, name| scope.info.symbols.get(name)
                );
                let prev_emit = ir.emit;
                let mut block_noreturn = false;
                for item in block_scope.ast.get_extra(*items) {
                    let item_ty = ir.types.add(TypeInfo::Unknown);
                    block_scope.reduce_expr(errors, ir, &block_scope.ast[*item],
                        info.with_expected(item_ty).with_noreturn(&mut block_noreturn));
                    ir.emit = prev_emit && !block_noreturn;
                }
                ir.emit = prev_emit;
                *info.noreturn |= block_noreturn;
                if !block_noreturn {
                    ir.specify(info.expected, TypeInfo::UNIT, errors, *span, self.ctx);
                }
                Ref::UNIT
            }
            ast::Expr::Declare { name, end: _, annotated_ty } => {
                ir.types.specify(info.expected, TypeInfo::UNIT, errors, self.span(expr), self.ctx);
                let ty = match self.resolve_type(annotated_ty, &mut ir.types) {
                    Ok(t) => t,
                    Err(err) => {
                        errors.emit_span(err, annotated_ty.span().in_mod(self.module));
                        TypeInfo::Invalid
                    }
                };
                let ty = ir.types.add(ty);

                self.declare_var(ir, self.src(*name).to_owned(), ty);

                Ref::UNIT
            }
            ast::Expr::DeclareWithVal { name, annotated_ty, val } => {
                let ty = match self.resolve_type(annotated_ty, &mut ir.types) {
                    Ok(t) => t,
                    Err(err) => {
                        errors.emit_span(err, annotated_ty.span().in_mod(self.module));
                        TypeInfo::Invalid
                    }
                };
                let ty = ir.types.add(ty);

                let var = self.declare_var(ir, self.src(*name).to_owned(), ty);

                self.reduce_expr_store_into_var(errors, ir, &self.ast[*val], var, info.with_expected(ty));
                Ref::UNIT
            }
            ast::Expr::Return { start: _, val } => {
                info.mark_noreturn();
                let r = self.reduce_expr_idx_val(errors, ir, *val, info.with_expected(info.ret));
                ir.specify(info.expected, TypeInfo::Primitive(Primitive::Never), errors, self.tspan(*val), self.ctx);
                ir.add_untyped(Tag::Ret, Data { un_op: r });
                Ref::UNDEF
            }
            ast::Expr::IntLiteral(span) => {
                let s = self.src(*span);
                let lit = IntLiteral::parse(s);
                let int_ty = lit
                    .ty
                    .map_or(TypeInfo::Int, |int_ty| TypeInfo::Primitive(int_ty.into()));
                ir.specify(info.expected, int_ty, errors, *span, self.ctx);
                if lit.val <= std::u64::MAX as u128 {
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
                }
            }
            ast::Expr::FloatLiteral(span) => {
                let lit = FloatLiteral::parse(self.src(*span));
                let float_ty = lit.ty.map_or(TypeInfo::Float, |float_ty| {
                    TypeInfo::Primitive(float_ty.into())
                });
                ir.specify(info.expected, float_ty, errors, *span, self.ctx);
                ir.add(Data { float: lit.val }, Tag::Float, info.expected)
            }
            ast::Expr::StringLiteral(span) => {
                let lit = string_literal(*span, self.ast.src(self.module).0);
                gen_string(&lit, ir, info.expected, *span, errors, self.ctx)
            }
            ast::Expr::BoolLiteral { val, start } => {
                let span = TSpan::new(*start, start + if *val {4} else {5});
                ir.specify(info.expected, TypeInfo::Primitive(Primitive::Bool), errors, span, self.ctx);
                Ref::val(if *val { RefVal::True } else { RefVal::False })
            }
            ast::Expr::EnumLiteral { dot: _, ident } => {
                let variant_name = self.src(*ident);
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
                        errors,
                        expr.span(self.ast).in_mod(self.module),
                        self.ctx,
                    );
                }
                let extra = ir.extra_data(variant_name.as_bytes());
                ir.add(Data { extra_len: (extra, variant_name.len() as u32)  }, Tag::EnumLit, info.expected)
            }
            ast::Expr::Nested(_, inner) => {
                return self.reduce_expr_any(errors, ir, &self.ast[*inner], info, get_var);
            }
            ast::Expr::Unit(span) => {
                ir.specify(info.expected, TypeInfo::Primitive(Primitive::Unit), errors, *span, self.ctx);
                Ref::UNIT
            }
            ast::Expr::Variable(span) => {
                let name = &self.ast.sources[self.module.idx()].0[span.range()];
                match self.resolve(name) {
                    Ok(resolved) => match resolved {
                        Resolved::Var(ty, var) => {
                            ir.types.merge(ty, info.expected, errors, self.module, *span, self.ctx);
                            return ExprResult::VarRef(var);
                        }
                        Resolved::Func(f) => return ExprResult::Func(f),
                        Resolved::Type(t) => return ExprResult::Type(t),
                        Resolved::Trait(t) => return ExprResult::Trait(t),
                        Resolved::LocalType(t) => return ExprResult::LocalType(t),
                        Resolved::Module(m) => return ExprResult::Module(m),
                        Resolved::Const(c) => {
                            let const_ty = self.get_or_gen_const(c, *span, errors).type_info(&mut ir.types);
                            ir.specify(info.expected, const_ty, errors, *span, self.ctx);
                            let val = self.ctx.get_const(c);
                            return self.const_val_to_result(val, ir, info);
                        }
                    },
                    Err(err) => {
                        errors.emit_span(err, span.in_mod(self.module));
                        ir.invalidate(info.expected);
                        Ref::UNDEF
                    }
                }
            }
            ast::Expr::Array(span, elems) => {
                let elems = &self.ast.expr_builder[*elems];
                let elem_ty = ir.types.add(TypeInfo::Unknown);
                let arr_ty = TypeInfo::Array(Some(elems.len() as u32), elem_ty);
                ir.types.specify(info.expected, arr_ty, errors, span.in_mod(self.module), self.ctx);
                //let arr = ir.add(Data { none: () }, Tag::Decl, expected);
                let arr = get_var(ir);
                let u64_ty = ir.types.add(TypeInfo::Primitive(Primitive::U64));
                for (i, elem) in elems.iter().enumerate() {
                    let elem_val = self.reduce_expr_val_spanned(errors, ir, &self.ast[*elem], *span,
                        info.with_expected(elem_ty));
                    let idx = ir.add(Data { int: i as u64 }, Tag::Int, u64_ty);
                    let elem_ptr = ir.add(Data { bin_op: (arr, idx) }, Tag::Member, elem_ty);
                    ir.add_untyped(Tag::Store, Data { bin_op: (elem_ptr, elem_val) });
                }
                return ExprResult::Stored(arr)
            }
            ast::Expr::Tuple(span, elems) => {
                let elems = self.ast.get_extra(*elems);
                let var = get_var(ir);
                let i32_ty = ir.types.add(TypeInfo::Primitive(Primitive::I32));
                let types = ir.types.add_multiple(std::iter::repeat(TypeInfo::Unknown).take(elems.len()));
                ir.types.specify(info.expected, TypeInfo::Tuple(types), errors, span.in_mod(self.module), self.ctx);
                for (i, elem) in elems.iter().enumerate() {
                    let member_ty = types.iter().nth(i).unwrap();
                    let member_val = self.reduce_expr_idx_val(errors, ir, *elem, info.with_expected(member_ty));
                    let idx = ir.add(Data { int: i as u64 }, Tag::Int, i32_ty);
                    let member = ir.add(Data { bin_op: (var, idx) }, Tag::Member, member_ty);
                    ir.add_untyped(Tag::Store, Data { bin_op: (member, member_val) });
                }
                return ExprResult::Stored(var);
            }
            ast::Expr::If { start: _, cond, then } => {
                let after_block = self.gen_if_then(ir, errors, *cond, info.ret, info.noreturn);

                ir.specify(info.expected, TypeInfo::Primitive(Primitive::Unit), errors, expr.span(self.ast), self.ctx);
                let then_ty = ir.types.add(TypeInfo::Unknown);
                let mut then_noreturn = false;
                self.reduce_expr(errors, ir, &self.ast[*then],
                    ExprInfo { expected: then_ty, noreturn: &mut then_noreturn, ret: info.ret});
                if !then_noreturn {
                    ir.add_untyped(Tag::Goto, Data { int32: after_block.0 });
                } else if !ir.currently_terminated() {
                    ir.add_unused_untyped(Tag::RetUndef, Data { none: () });
                }
                ir.begin_block(after_block);
                Ref::UNIT
            }
            ast::Expr::IfElse { start: _, cond, then, else_ } => {
                let else_block = self.gen_if_then(ir, errors, *cond, info.ret, info.noreturn);
                let mut then_noreturn = false;
                let then_val = self.reduce_expr_idx_val(errors, ir, *then, info.with_noreturn(&mut then_noreturn));
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
                let else_val = self.reduce_expr_idx_val(errors, ir, *else_, info.with_noreturn(&mut else_noreturn));
                let else_exit = ir.current_block();
                if then_noreturn && else_noreturn {
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
                }
            }
            ast::Expr::While { start: _, cond, body } => {
                ir.specify(info.expected, TypeInfo::Primitive(Primitive::Unit), errors, expr.span(self.ast), self.ctx);

                let cond_block = ir.create_block();
                let body_block = ir.create_block();
                let after_block = ir.create_block();

                ir.add_untyped(Tag::Goto, Data { int32: cond_block.0 });
                ir.begin_block(cond_block);
                
                let b = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
                let cond = self.reduce_expr_idx_val(errors, ir, *cond, info.with_expected(b));

                let branch_extra = ir.extra_data(&body_block.0.to_le_bytes());
                ir.extra_data(&after_block.0.to_le_bytes());
                ir.add_untyped(Tag::Branch, Data { branch: (cond, branch_extra) });
                ir.begin_block(body_block);
                let body_ty = ir.types.add(TypeInfo::Unknown);
                let mut body_noreturn = false;
                self.reduce_expr_idx_val(errors, ir, *body,
                    ExprInfo { expected: body_ty, ret: info.ret, noreturn: &mut body_noreturn });
                if !body_noreturn {
                    ir.add_untyped(Tag::Goto, Data { int32: cond_block.0 });
                } else if !ir.currently_terminated() {
                    ir.add_unused_untyped(Tag::RetUndef, Data { none: () });
                }
                ir.begin_block(after_block);
                Ref::UNIT
            }
            ast::Expr::FunctionCall { func, args, end: _ } => {
                let args = &self.ast.expr_builder[*args];
                let called_ty = ir.types.add(TypeInfo::Unknown);
                fn gen_call(
                    scope: &mut Scope,
                    expr: &Expr,
                    func: SymbolKey,
                    this_arg: Option<(Ref, TypeTableIndex, TSpan)>,
                    args: impl ExactSizeIterator<Item = ExprRef>,
                    ir: &mut IrBuilder,
                    mut info: ExprInfo,
                    errors: &mut Errors
                ) -> Ref {
                    let arg_count = args.len() + if this_arg.is_some() { 1 } else { 0 };
                    
                    let header = scope.ctx.funcs[func.idx()].header();
                    let return_type = header.return_type.as_info(&mut ir.types);

                    ir.specify(info.expected, return_type, errors, expr.span(scope.ast), scope.ctx);
                    if let TypeInfo::Primitive(Primitive::Never) = return_type {
                        *info.noreturn = true;
                    }

                    let invalid_arg_count = if header.varargs {
                        arg_count < header.params.len()
                    } else {
                        arg_count != header.params.len()
                    };
                    if invalid_arg_count {
                        errors.emit_span(Error::InvalidArgCount, expr.span(scope.ast).in_mod(scope.module));
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
                                    ir.types.specify(this_ty, info, errors,
                                        this_span.in_mod(scope.module), scope.ctx
                                    );
                                    bytes.extend(this.to_bytes());
                                }
                                None => {
                                    errors.emit_span(Error::NotAnInstanceMethod, this_span.in_mod(scope.module));
                                }
                            }
                        }
                        for (arg, ty) in args.zip(param_iter) {
                            let type_info = ty.as_ref().map_or(TypeInfo::Unknown, |ty| ty.as_info(&mut ir.types));
                            let ty = ir
                                .types
                                .add(type_info);
                            let expr = scope.reduce_expr_idx_val(errors, ir, arg, info.with_expected(ty));
                            bytes.extend(&expr.to_bytes());
                        }
                        let extra = ir.extra_data(&bytes);
                        ir.add(Data { extra_len: (extra, arg_count as u32) }, Tag::Call, info.expected)
                    }
                }
                let called = &self.ast[*func];
                match self.reduce_expr(errors, ir, called, info.with_expected(called_ty)) {
                    ExprResult::Func(key) => {
                        gen_call(self, expr, key, None, args.iter().copied(), ir, info, errors)
                    }
                    //TODO: Trait function calls
                    ExprResult::Method(self_var, key) => {
                        let called_span = called.span(self.ast);
                        let this = Some((self_var, called_ty, called_span));
                        gen_call(self, expr, key, this, args.iter().copied(), ir, info, errors)
                    }
                    ExprResult::Type(ty) => {
                        let (_, TypeDef::Struct(struct_)) = &self.ctx.types[ty.idx()] else {
                            errors.emit_span(Error::FunctionOrStructTypeExpected, self.span(called));
                            return ExprResult::Val(Ref::UNDEF)
                        };
                        let generics = ir.types.add_multiple((0..struct_.generic_count).map(|_| TypeInfo::Unknown));
                        ir.specify(info.expected, TypeInfo::Resolved(ty, generics), errors, expr.span(self.ast),
                            self.ctx);

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
                                    self.reduce_expr_idx_val(errors, ir, *member_val, info.with_expected(member_ty));
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
                            return ExprResult::Stored(var);
                        } else {
                            errors.emit_span(Error::InvalidArgCount, expr.span(self.ast).in_mod(self.module));
                            Ref::UNDEF
                        }
                    }
                    _ => {
                        if !ir.types.get_type(called_ty).is_invalid() {
                            errors.emit_span(
                                Error::FunctionOrStructTypeExpected,
                                called.span(self.ast).in_mod(self.module)
                            );
                        }
                        ir.invalidate(info.expected);
                        Ref::UNDEF
                    }
                }
            }
            ast::Expr::UnOp(_, un_op, val) => {
                let span = expr.span(self.ast);
                let (inner_expected, tag) = match un_op {
                    UnOp::Neg => (info.expected, Tag::Neg),
                    UnOp::Not => (ir.types.add(TypeInfo::Primitive(Primitive::Bool)), Tag::Not),
                    UnOp::Ref => {
                        let ptr_ty = TypeInfo::Pointer(ir.types.add(TypeInfo::Unknown));
                        ir.types.specify(info.expected, ptr_ty, errors, span.in_mod(self.module), self.ctx);
                        let inner_expected = match ir.types.get_type(info.expected) {
                            TypeInfo::Pointer(inner) => inner,
                            _ => ir.types.add(TypeInfo::Invalid)
                        };
                        return ExprResult::Val(match 
                            self.reduce_expr(errors, ir, &self.ast[*val], info.with_expected(inner_expected))
                        {
                            ExprResult::VarRef(r) | ExprResult::Stored(r) => {
                                ir.types.specify(info.expected, TypeInfo::Pointer(inner_expected),
                                    errors, span.in_mod(self.module), self.ctx);
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
                                errors.emit_span(Error::CantTakeRef, expr.span(self.ast).in_mod(self.module));
                                Ref::UNDEF
                            }
                        })
                    }
                    UnOp::Deref => {
                        let expected = ir.types.add(TypeInfo::Pointer(info.expected));
                        let pointer_val = 
                            self.reduce_expr_idx_val(errors, ir, *val, info.with_expected(expected));
                        return ExprResult::VarRef(pointer_val); // just use the pointer value as variable
                    }
                };
                let inner = self.reduce_expr_idx_val(errors, ir, *val, info.with_expected(inner_expected));
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
                    errors.emit_span(err, expr.span(self.ast).in_mod(self.module));
                }
                ir.add(Data { un_op: inner }, tag, inner_expected)
            }
            ast::Expr::BinOp(op, l, r) => {
                if let Operator::Assignment(assignment) = op {
                    ir.specify(info.expected, TypeInfo::UNIT, errors, expr.span(self.ast), self.ctx);
                    let var_ty = ir.types.add_unknown();
                    let lval = self.reduce_lval_expr(errors, ir, &self.ast[*l], info.with_expected(var_ty),
                        Error::CantAssignTo);
                    let r = self.reduce_expr_idx_val(errors, ir, *r, info.with_expected(var_ty));

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
                    Ref::UNDEF
                } else {
                    
    
                    // binary operations always require the same type on both sides right now
                    let inner_ty = if op.is_boolean() {
                        ir.types.add(TypeInfo::Primitive(Primitive::Bool))
                    } else if op.is_logical() {
                        ir.types.add(TypeInfo::Unknown)
                    } else {
                        info.expected
                    };
                    let l = self.reduce_expr_idx_val(errors, ir, *l, info.with_expected(inner_ty));
                    let r = self.reduce_expr_idx_val(errors, ir, *r, info.with_expected(inner_ty));
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
                    ir.add(Data { bin_op: (l, r) }, tag, info.expected)
                }
            }
            ast::Expr::MemberAccess { left, name: name_span } => {
                let member = &self.ast.src(self.module).0[name_span.range()];
                let left_ty = ir.types.add(TypeInfo::Unknown);
                enum MemberAccessType {
                    Var(Ref),
                    Module(ModuleId),
                    Associated(SymbolKey),
                    TraitFunction(SymbolKey),
                    Invalid
                }
                let left = &self.ast[*left];
                let left_val = match self.reduce_expr(errors, ir, left, info.with_expected(left_ty)) {
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
                        errors.emit_span(Error::NonexistantMember, name_span.in_mod(self.module));
                        MemberAccessType::Invalid
                    }
                    ExprResult::Module(id) => MemberAccessType::Module(id),
                };

                match left_val {
                    MemberAccessType::Var(var) => {
                        let (ty, idx) = match ir.types.get_type(left_ty) {
                            TypeInfo::Resolved(key, generics) => {
                                match &self.ctx.types[key.idx()].1 {
                                    TypeDef::Struct(struct_) => {
                                        if let Some(method) = struct_.methods.get(member) {
                                            return ExprResult::Method(var, *method);
                                        } else if let Some((i, (_, ty))) = struct_
                                            .members
                                            .iter()
                                            .enumerate()
                                            .find(|(_, (name, _))| name == member)
                                        {
                                            (ty.as_info_generic(&mut ir.types, generics), i)
                                        } else {
                                            errors.emit_span(Error::NonexistantMember, name_span.in_mod(self.module));
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
                                errors.emit_span(Error::TypeMustBeKnownHere, left.span_in(self.ast, self.module));
                                (TypeInfo::Invalid.into(), 0)
                            }
                            _ => {
                                errors.emit_span(Error::NonexistantMember, name_span.in_mod(self.module));
                                (TypeInfo::Invalid.into(), 0)
                            }
                        };
                        ir.types.specify_or_merge(info.expected, ty, errors, self.module, expr.span(self.ast),
                            self.ctx);
                        let i32_ty = ir.types.add(TypeInfo::Primitive(Primitive::I32));
                        let idx = ir.add(
                            Data { int: idx as u64 },
                            Tag::Int,
                            i32_ty
                        );
                        let member = ir.add(Data { bin_op: (var, idx) }, Tag::Member, info.expected);
                        return ExprResult::VarRef(member);
                    }
                    MemberAccessType::Module(id) => {
                        let module = &self.globals[id];
                        if let Some(symbol) = module.get(member) {
                            return match *symbol {
                                Symbol::Func(f) => ExprResult::Func(f),
                                Symbol::Type(t) => ExprResult::Type(t),
                                Symbol::Trait(t) => ExprResult::Trait(t),
                                Symbol::LocalType(t) => ExprResult::LocalType(t),
                                Symbol::Generic(_) => todo!(), // is this a possibility
                                Symbol::Module(m) => ExprResult::Module(m),
                                Symbol::Var { ty: _, var } => ExprResult::VarRef(var),
                                Symbol::Const(key) => {
                                    let val = self.ctx.get_const(key);
                                    self.const_val_to_result(val, ir, info)
                                }
                            };
                        } else {
                            errors.emit_span(Error::UnknownIdent, name_span.in_mod(self.module));
                            ir.invalidate(info.expected);
                            Ref::UNDEF
                        }
                    }
                    MemberAccessType::Associated(key) => {
                        match self.ctx.get_type(key) {
                            TypeDef::Struct(def) => {
                                if let Some(method) = def.methods.get(member) {
                                    return ExprResult::Func(*method);
                                } else {
                                    errors.emit_span(Error::UnknownFunction, name_span.in_mod(self.module));
                                    ir.invalidate(info.expected);
                                    Ref::UNDEF
                                }
                            }
                            TypeDef::Enum(def) => {
                                if let Some(&variant) = def.variants.get(member) {
                                    ir.types.specify(info.expected, TypeInfo::Resolved(key, TypeTableIndices::EMPTY),
                                        errors, self.span(expr), self.ctx);
                                    let r = ir.add(Data { int: variant as u64 }, Tag::Int, info.expected);
                                    return ExprResult::Val(r)
                                } else {
                                    errors.emit_span(Error::NonexistantEnumVariant, name_span.in_mod(self.module));
                                    ir.invalidate(info.expected);
                                    return ExprResult::Val(Ref::UNDEF)
                                }
                            }
                            TypeDef::NotGenerated { .. } => unreachable!()
                        }
                    }
                    MemberAccessType::TraitFunction(t) => {
                        if let Some((idx, _)) = self.ctx.get_trait(t).functions.get(member) {
                            return ExprResult::TraitFunc(t, *idx);
                        } else {
                            errors.emit_span(Error::UnknownFunction, name_span.in_mod(self.module));
                            ir.invalidate(info.expected);
                            Ref::UNDEF
                        }
                    }
                    MemberAccessType::Invalid => {
                        ir.invalidate(info.expected);
                        Ref::UNDEF
                    }
                }
            }
            ast::Expr::Index { expr: indexed, idx, end: _ } => {
                let array_ty = ir.types.add(TypeInfo::Array(None, info.expected));
                let indexed = &self.ast[*indexed];
                let val = self.reduce_lval_expr(errors, ir, indexed, info.with_expected(array_ty), Error::CantIndex);
                
                let idx_ty = ir.types.add(TypeInfo::Int);
                let idx_expr = &self.ast[*idx];
                let idx = self.reduce_expr_val_spanned(errors, ir, idx_expr,
                    idx_expr.span(self.ast), info.with_expected(idx_ty));
                return ExprResult::VarRef(
                    ir.add(Data { bin_op: (val, idx) }, Tag::Member, info.expected)
                )
            }
            ast::Expr::TupleIdx { expr: indexed, idx, end: _ } => {
                let indexed_ty = ir.types.add(TypeInfo::Unknown);
                let res = self.reduce_expr(errors, ir, &self.ast[*indexed], info.with_expected(indexed_ty));
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
                        errors.emit_span(Error::TupleIndexingOnNonValue, expr.span_in(self.ast, self.module));
                        ir.invalidate(info.expected);
                        return ExprResult::Val(Ref::UNDEF)
                    }
                };
                let TypeInfo::Tuple(elems) = ir.types.get_type(indexed_ty) else {
                    eprintln!("Indexing {:?}", ir.types.get_type(indexed_ty));
                    errors.emit_span(Error::TypeMustBeKnownHere, expr.span_in(self.ast, self.module));
                    return ExprResult::Val(Ref::UNDEF)
                };
                let Some(elem_ty) = elems.iter().nth(*idx as usize) else {
                    errors.emit_span(Error::TupleIndexOutOfRange, expr.span_in(self.ast, self.module));
                    return ExprResult::Val(Ref::UNDEF)
                };
                ir.types.merge(info.expected, elem_ty, errors, self.module, expr.span(self.ast), self.ctx);
                let i32_ty = ir.types.add(TypeInfo::Primitive(Primitive::I32));
                let idx = ir.add(Data { int: *idx as _ }, Tag::Int, i32_ty);
                return ExprResult::VarRef(ir.add(Data { bin_op: (expr_var, idx) }, Tag::Member, elem_ty));
            }
            ast::Expr::Cast(span, target, val) => {
                let target = match self.resolve_type(target, &mut ir.types) {
                    Ok(target) => target,
                    Err(err) => {
                        errors.emit_span(err, span.in_mod(self.module));
                        TypeInfo::Invalid
                    }
                };

                ir.specify(info.expected, target, errors, expr.span(self.ast), self.ctx);
                let inner_ty = ir.types.add(TypeInfo::Unknown);
                let val = self.reduce_expr_idx_val(errors, ir, *val, info.with_expected(inner_ty));
                //TODO: check table for available casts
                ir.add(Data { un_op: val, }, Tag::Cast, info.expected)
            }
            ast::Expr::Root(_) => {
                return ExprResult::Module(ModuleId::ROOT)
            }
            ast::Expr::Asm { span: _, asm_str_span, args } => {
                let expr_refs = self.ast.get_extra(*args).iter()
                .map(|arg| {
                    let expr = &self.ast[*arg];
                    let info = info.with_expected(ir.types.add_unknown());
                    self.reduce_expr_val_spanned(errors, ir, expr, expr.span(&self.ast), info)
                })
                .collect::<Vec<_>>();
                assert!(expr_refs.len() <= u16::MAX as usize, "too many arguments for inline assembly");
                
                let asm_str = self.src(TSpan::new(asm_str_span.start + 1, asm_str_span.end - 1));
                assert!(asm_str.len() <= u16::MAX as usize, "inline assembly string is too long");
                let extra = ir.extra_data(asm_str.as_bytes());
                for &r in &expr_refs {
                    ir.extra_data(&r.to_bytes());
                }
                ir.add_unused_untyped(Tag::Asm, Data { asm: (extra, asm_str.len() as u16, expr_refs.len() as u16) });
                return ExprResult::Val(Ref::UNDEF)
            }
        };
        ExprResult::Val(r)
    }

    fn gen_if_then(&mut self, ir: &mut IrBuilder, errors: &mut Errors, cond: ExprRef, ret: TypeTableIndex,
        noreturn: &mut bool)
    -> BlockIndex {
        let b = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
        let cond = self.reduce_expr_idx_val(errors, ir, cond, ExprInfo { expected: b, ret, noreturn });
        let then_block = ir.create_block();
        let other_block = ir.create_block();

        let branch_extra = ir.extra_data(&then_block.0.to_le_bytes());
        ir.extra_data(&other_block.0.to_le_bytes());

        ir.add_untyped(Tag::Branch, Data { branch: (cond, branch_extra) });
        ir.begin_block(then_block);
        other_block
    }

    fn get_or_gen_const(&mut self, key: SymbolKey, span: TSpan, errors: &mut Errors) -> &ConstVal {
        if let ConstVal::NotGenerated { defs, generating } = self.ctx.get_const_mut(key) {
            let val = if *generating {
                errors.emit_span(Error::RecursiveDefinition, span.in_mod(self.module));
                ConstVal::Invalid
            } else {
                *generating = true;
                let Some(ast::Definition::Const(ty, expr)) = &self.ast[*defs].get(self.src(span))
                    else { unreachable!() };
                match self.eval_const(Some(ty), *expr, errors) {
                    Ok(val) => val,
                    Err(err) => {
                        errors.emit_err(err);
                        ConstVal::Invalid
                    }
                }
            };
            
            self.ctx.consts[key.idx()] = val;
        }
        &self.ctx.consts[key.idx()]
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
                    Symbol::Var { .. } => unreachable!(),
                    Symbol::Const(_) => unreachable!(),
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
    fn eval_const(&mut self, ty: Option<&ast::UnresolvedType>, val: ExprRef, errors: &mut Errors)
    -> EyeResult<ConstVal> {
        #![allow(unused)]
        use crate::error::CompileError;

        let expr = &self.ast[val];
        Ok(match expr {
            // ast::Expr::Block { span, items, defs } => todo!(),
            // ast::Expr::Declare { name, annotated_ty, end } => todo!(),
            // ast::Expr::DeclareWithVal { name, annotated_ty, val } => todo!(),
            // ast::Expr::Return { start, val } => todo!(),
            ast::Expr::IntLiteral(span) => ConstVal::Int(self.src(*span).parse().unwrap()),
            ast::Expr::FloatLiteral(span) => ConstVal::Float(self.src(*span).parse().unwrap()),
            ast::Expr::StringLiteral(span) => ConstVal::String(string_literal(*span, self.ast.src(self.module).0)),
            ast::Expr::BoolLiteral { start, val } => ConstVal::Bool(*val),
            ast::Expr::EnumLiteral { dot, ident } => ConstVal::EnumVariant(self.src(*ident).to_owned()),
            ast::Expr::Nested(_, inner) => self.eval_const(ty, *inner, errors)?,
            ast::Expr::Unit(_) => ConstVal::Unit,
            ast::Expr::Variable(span) => {
                let name = self.src(*span);
                match self.resolve(self.src(*span)).map_err(|err| err.at_span(span.in_mod(self.module)))? {
                    Resolved::Var(_, _) => todo!(),
                    Resolved::Func(key) => ConstVal::Symbol(Symbol::Func(key)),
                    Resolved::Type(key) => ConstVal::Symbol(Symbol::Type(key)),
                    Resolved::Trait(key) => ConstVal::Symbol(Symbol::Trait(key)),
                    Resolved::Module(key) => ConstVal::Symbol(Symbol::Module(key)),
                    Resolved::Const(key) => {
                        let name = name.to_owned(); // PERF: ownership
                        self.get_or_gen_const(key, *span, errors).clone()
                    }
                    Resolved::LocalType(_) => return Err(Error::NotConst.at_span(span.in_mod(self.module)))
                }
            }
            // ast::Expr::Array(_, _) => todo!(),
            // ast::Expr::Tuple(_, _) => todo!(),
            ast::Expr::If { .. }
            | ast::Expr::IfElse { .. }
            | ast::Expr::While { .. }
            | ast::Expr::FunctionCall { .. }
            => return Err(CompileError::new(Error::NotConst, self.span(expr))),
            ast::Expr::UnOp(_, op, inner) => {
                let val = self.eval_const(ty, *inner, errors)?;
                if val.is_invalid() { return Ok(ConstVal::Invalid) }
                match op {
                    ast::UnOp::Neg => {
                        let ConstVal::Int(int_val) = val else {
                            return Err(CompileError::new(Error::CantNegateType, self.span(&self.ast[*inner])));
                        };
                        ConstVal::Int(-int_val)
                    }
                    ast::UnOp::Not => {
                        let ConstVal::Bool(bool_val) = val else {
                            return Err(CompileError::new(Error::UnexpectedType, self.span(&self.ast[*inner])));
                        };
                        ConstVal::Bool(!bool_val)
                    }
                    ast::UnOp::Ref | ast::UnOp::Deref => return Err(CompileError::new(
                        Error::UnexpectedType, self.span(expr))),
                }
            }
            ast::Expr::BinOp(op, l, r) => {
                let l_val = self.eval_const(None, *l, errors)?;
                let r_val = self.eval_const(None, *r, errors)?;

                if l_val.is_invalid() || r_val.is_invalid() { return Ok(ConstVal::Invalid); }


                match op {
                    Operator::Assignment(_) => {
                        return Err(Error::NotConst.at_span(self.span(expr)));
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
                                                        Error::MismatchedType, self.span(expr)
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
                            Error::UnexpectedType, self.span(&self.ast[*l]))) };
                        let ConstVal::Bool(r) = r_val else { return Err(CompileError::new(
                            Error::UnexpectedType, self.span(&self.ast[*r]))) };
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
                                                    Error::MismatchedType, self.span(expr)
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
            _ => return Err(CompileError::new(Error::NotConst, self.span(expr)))
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
