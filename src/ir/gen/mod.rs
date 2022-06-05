use crate::{
    ast::{self, Expr, ModuleId, UnOp, TSpan, ExprRef},
    error::{Error, Errors},
    lexer::{tokens::{Operator, AssignType, IntLiteral, FloatLiteral}, Span},
    types::Primitive,
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
    };
    let globals = types::gen_globals(ast, &mut ctx, &mut errors);

    // scope accessible from all modules containing dependencies etc.
    // let global_scope = Scope::new(&mut ctx, deps, &glo, module);

    for (id, module) in ast.modules.iter().enumerate() {
        let id = ModuleId::new(id as u32);
        let mut scope = Scope::new(&mut ctx, &globals[id], globals.get_ref(), ast, id);

        gen_func_bodies(&mut scope, &module.definitions, &mut errors,
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

fn gen_func_bodies(
    scope: &mut Scope,
    defs: &HashMap<String, ast::Definition>,
    errors: &mut Errors,
    get_symbol: impl for<'a> Fn(&'a mut Scope, &str) -> Option<&'a Symbol>,
) {
    let mut gen = |name: &String, def: &ast::Function, key: SymbolKey, scope: &mut Scope| {
        let func_idx = key.idx();
        let header = match &scope.ctx.funcs[func_idx] {
            FunctionOrHeader::Func(_) => {
                unreachable!("Function shouldn't already be defined here")
            }
            FunctionOrHeader::Header(header) => header.clone(),
        };
        let ir = def.body.as_ref().map(|body| {
            let mut builder = IrBuilder::new(scope.module);
            let mut scope_defs = HashMap::with_capacity(header.params.len() + def.generics.len());
            
            for generic in &def.generics {
                let name = &scope.ast.src(scope.module).0[generic.range()];
                let generic_ty = builder.types.add(TypeInfo::Unknown);
                scope_defs.insert(name.to_owned(), Symbol::LocalType(generic_ty));
            }
            for (i, (name, ty)) in header.params.iter().enumerate() {
                let info = ty.as_info(&mut builder.types);
                let ty = builder.types.add(info);
                let param = builder.add(Data { int32: i as u32 }, Tag::Param, ty);
                scope_defs.insert(name.clone(), Symbol::Var { ty, var: param });
            }
            let mut scope: Scope<'_> = scope.child(scope_defs);
            let return_type = header.return_type.as_info(&mut builder.types);
            let expected = builder.types.add(return_type);
            let body = &scope.ast[*body];
            let val = scope.reduce_expr_val_spanned(
                errors,
                &mut builder,
                body,
                expected,
                expected,
                body.span(scope.ast)
            );
            //TODO: refactor to branch return analysis
            if header.return_type == Type::Prim(Primitive::Unit) {
                builder.add_unused_untyped(Tag::Ret, Data { un_op: Ref::UNIT });
            } else if !body.is_block() {
                builder.add_unused_untyped(Tag::Ret, Data { un_op: val });
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
                gen(name, func, *key, scope);
            }
            ast::Definition::Struct(struct_) => {
                let &Symbol::Type(ty) = get_symbol(scope, name)
                    .expect("Missing struct after definition phase")
                    else { panic!("Struct expected") };
                let TypeDef::Struct(def) = scope.ctx.get_type(ty);
                // this is a bit ugly for borrowing reasons, maybe the allocation can be removed
                let methods = def.methods.clone();

                for (name, method) in &struct_.methods {
                    let key = methods.get(name).unwrap();
                    gen(name, method, *key, scope);
                }
            }
            _ => {}
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Symbol {
    Func(SymbolKey),
    Type(SymbolKey),
    LocalType(TypeTableIndex),
    TypeProto(SymbolKey),
    Generic(u8),
    Module(ModuleId),
    Var { ty: TypeTableIndex, var: Ref }
}

struct ScopeInfo<'a> {
    parent: Option<NonNull<ScopeInfo<'a>>>,
    symbols: Cow<'a, HashMap<String, Symbol>>,
}
impl<'a> ScopeInfo<'a> {
    fn parent(&self) -> Option<&ScopeInfo<'a>> {
        self.parent
            .as_ref()
            .map(|parent| unsafe { parent.as_ref() })
    }
    fn reborrow(&self) -> ScopeInfo {
        ScopeInfo { parent: self.parent, symbols: Cow::Borrowed(self.symbols.borrow()) }
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
                Symbol::LocalType(t) => Resolved::LocalType(*t),
                Symbol::TypeProto(t) => Resolved::TypeProto(*t),
                Symbol::Generic(_) => todo!(),
                Symbol::Module(m) => Resolved::Module(*m),
                Symbol::Var { ty, var } => Resolved::Var(*ty, *var),
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
    types: Vec<TypeDef>,
}
impl TypingCtx {
    pub fn add_func(&mut self, func: FunctionOrHeader) -> SymbolKey {
        self.funcs.push(func);
        SymbolKey((self.funcs.len() - 1) as u64)
    }
    pub fn add_type(&mut self, ty: TypeDef) -> SymbolKey {
        self.types.push(ty);
        SymbolKey((self.types.len() - 1) as u64)
    }
    pub fn add_proto_ty(&mut self) -> SymbolKey {
        self.add_type(TypeDef::Struct(Struct {
            members: Vec::new(),
            methods: HashMap::new(),
            generic_count: 0,
            name: String::new()
        }))
    }
    pub fn get_type(&self, key: SymbolKey) -> &TypeDef { &self.types[key.idx()] }
    pub fn get_type_mut(&mut self, key: SymbolKey) -> &mut TypeDef { &mut self.types[key.idx()] }
    //pub fn get_func(&self, key: SymbolKey) -> &FunctionOrHeader { &self.funcs[key.idx()] }
    //pub fn get_func_mut(&mut self, key: SymbolKey) -> &mut FunctionOrHeader { &mut self.funcs[key.idx()] }
}

enum Resolved {
    Var(TypeTableIndex, Ref),
    Func(SymbolKey),
    Type(SymbolKey),
    LocalType(TypeTableIndex),
    TypeProto(SymbolKey),
    Module(ModuleId),
}
impl Resolved {
    pub fn into_symbol(self) -> Option<Symbol> {
        match self {
            Resolved::Var(_, _) | Resolved::LocalType(_) => None,
            Resolved::Func(id) => Some(Symbol::Func(id)),
            Resolved::Type(id) => Some(Symbol::Type(id)),
            Resolved::TypeProto(id) => Some(Symbol::TypeProto(id)),
            Resolved::Module(id) => Some(Symbol::Module(id)),
        }
    }
}

#[derive(Debug)]
enum ExprResult {
    VarRef(Ref),
    Val(Ref),
    Func(SymbolKey),
    /// method call on a variable: x.method
    Method(Ref, SymbolKey),
    Type(SymbolKey),
    LocalType(TypeTableIndex),
    TypeProto(SymbolKey),
    Module(ModuleId),
    Stored(Ref),
}

impl ExprResult {
    pub fn get_or_load(
        self,
        ir: &mut IrBuilder,
        ty: TypeTableIndex,
        errors: &mut Errors,
        span: Span
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
pub struct Scope<'s> {
    ctx: &'s mut TypingCtx,
    globals: GlobalsRef<'s>,
    ast: &'s ast::Ast,
    module: ModuleId,
    info: ScopeInfo<'s>,
}

impl<'s> Scope<'s> {
    pub fn new(
        ctx: &'s mut TypingCtx,
        symbols: &'s HashMap<String, Symbol>,
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
            },
        }
    }
    pub fn reborrow(&mut self) -> Scope {
        Scope {
            ctx: &mut *self.ctx,
            globals: self.globals,
            ast: &*self.ast,
            module: self.module,
            info: self.info.reborrow()
        }
    }
    pub fn tspan(&self, expr: ExprRef) -> TSpan {
        self.ast[expr].span(self.ast)
    }
    pub fn _span(&self, expr: ExprRef) -> Span {
        self.ast[expr].span_in(self.ast, self.module)
    }
    pub fn src(&self, span: TSpan) -> &str {
        &self.ast.sources()[self.module.idx()].0[span.range()]
    }
    pub fn child(&mut self,symbols: HashMap<String, Symbol>) -> Scope {
        Scope {
            ctx: &mut *self.ctx,
            globals: self.globals,
            ast: self.ast,
            module: self.module,
            info: ScopeInfo {
                parent: Some(NonNull::from(&mut self.info)),
                symbols: Cow::Owned(symbols),
            },
        }
    }

    fn resolve(&self, name: &str) -> Result<Resolved, Error> {
        self.info.resolve_local(name)
    }

    fn resolve_type(&mut self, unresolved: &ast::UnresolvedType, types: &mut TypeTable) -> Result<TypeInfo, Error> {
        match unresolved {
            ast::UnresolvedType::Primitive(p, _) => Ok(TypeInfo::Primitive(*p)),
            ast::UnresolvedType::Unresolved(path) => {
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
                match current_module {
                    ModuleOrLocal::Module(m) => match self.globals[m]
                        .get(last.0)
                        .ok_or(Error::UnknownIdent)? {
                            Symbol::Type(ty) => {
                                let TypeDef::Struct(struct_) = self.ctx.get_type(*ty);
                                let generics = types.add_multiple(
                                    (0..struct_.generic_count)
                                        .map(|_| TypeInfo::Unknown)
                                );
                                Ok(TypeInfo::Resolved(*ty, generics))
                            }
                            // TODO: might require a new solution to allow inference of local types
                            Symbol::LocalType(ty) => Ok(types.get_type(*ty)),
                            _ => Err(Error::TypeExpected)
                        },
                    ModuleOrLocal::Local => match self.info.resolve_local(last.0)? {
                        Resolved::Type(ty) => {
                            let TypeDef::Struct(struct_) = self.ctx.get_type(ty);
                            let generics = types.add_multiple(
                                (0..struct_.generic_count)
                                    .map(|_| TypeInfo::Unknown)
                            );
                            Ok(TypeInfo::Resolved(ty, generics))
                        }
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
        let var = ir.add(Data { ty }, Tag::Decl, ty);
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
        expected: TypeTableIndex,
        ret: TypeTableIndex,
        span: TSpan
    ) -> Ref {
        self.reduce_expr(errors, ir, expr, expected, ret)
            .get_or_load(ir, expected, errors, span.in_mod(self.module))
    }

    fn reduce_expr_idx_val(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        expr: ExprRef,
        expected: TypeTableIndex,
        ret: TypeTableIndex
    ) -> Ref {
        self.reduce_expr_val_spanned(errors, ir, &self.ast[expr], expected, ret, self.tspan(expr))
    }

    fn reduce_expr(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        expr: &Expr,
        expected: TypeTableIndex,
        ret: TypeTableIndex,
    ) -> ExprResult {
        self.reduce_expr_any(
            errors, ir, expr, expected, ret,
            |ir| ir.add(Data { ty: expected }, Tag::Decl, expected), // declare new var
        )
    }

    fn reduce_expr_store_into_var(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        expr: &Expr,
        var: Ref,
        expected: TypeTableIndex,
        ret: TypeTableIndex,
    ) {
        let val = match self.reduce_expr_any(errors, ir, expr, expected, ret, |_| var) {
            ExprResult::Stored(_) => return,
            ExprResult::VarRef(other_var) => ir.add(Data { un_op: other_var }, Tag::Load, expected),
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
        expected: TypeTableIndex,
        ret: TypeTableIndex
    ) -> Ref {
        match self.reduce_expr_any(
            errors, ir, expr, expected, ret,
            |ir| ir.add(Data { ty: expected }, Tag::Decl, expected)
        ) {
            ExprResult::VarRef(var) | ExprResult::Stored(var) => var,
            ExprResult::Val(_)
            | ExprResult::Func(_)
            | ExprResult::Method(_, _)
            | ExprResult::Type(_)
            | ExprResult::LocalType(_)
            | ExprResult::TypeProto(_)
            | ExprResult::Module(_)
            => {
                if !ir.types.get_type(expected).is_invalid() {
                    errors.emit_span(Error::CantAssignTo, expr.span(self.ast).in_mod(self.module));
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
        expected: TypeTableIndex,
        ret: TypeTableIndex,
        get_var: impl Fn(&mut IrBuilder) -> Ref,
    ) -> ExprResult {
        let r = match &expr {
            ast::Expr::Block { span: _, items, defs } => {
                let defs = &self.ast.expr_builder[*defs];
                let locals = types::gen_locals(self, defs,  errors);
                let mut block_scope = self.child(locals);
                gen_func_bodies(&mut block_scope, defs, errors,
                    |scope, name| scope.info.symbols.get(name)
                );
                //TODO: specify return value (and later yield value)
                //ir.types.specify(expected, TypeInfo::Primitive(Primitive::Unit), errors);
                for item in block_scope.ast.get_extra(*items) {
                    let item_ty = ir.types.add(TypeInfo::Unknown);
                    block_scope.reduce_expr(errors, ir, &block_scope.ast[*item], item_ty, ret);
                }
                Ref::val(RefVal::Undef)
            }
            ast::Expr::Declare { name, end: _, annotated_ty } => {
                let ty = match self.resolve_type(annotated_ty, &mut ir.types) {
                    Ok(t) => t,
                    Err(err) => {
                        errors.emit_span(err, annotated_ty.span(&self.ast.expr_builder).in_mod(self.module));
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
                        errors.emit_span(err, annotated_ty.span(&self.ast.expr_builder).in_mod(self.module));
                        TypeInfo::Invalid
                    }
                };
                let ty = ir.types.add(ty);

                let var = self.declare_var(ir, self.src(*name).to_owned(), ty);

                self.reduce_expr_store_into_var(errors, ir, &self.ast[*val], var, ty, ret);
                Ref::UNIT
            }
            ast::Expr::Return { start: _, val } => {
                let r = self.reduce_expr_idx_val(errors, ir, *val, ret, ret);
                ir.specify(expected, TypeInfo::Primitive(Primitive::Never), errors, self.tspan(*val));
                ir.add_untyped(Tag::Ret, Data { un_op: r });
                Ref::val(RefVal::Undef)
            }
            ast::Expr::IntLiteral(span) => {
                let s = self.src(*span);
                let lit = IntLiteral::parse(s);
                let int_ty = lit
                    .ty
                    .map_or(TypeInfo::Int, |int_ty| TypeInfo::Primitive(int_ty.into()));
                ir.specify(expected, int_ty, errors, *span);
                if lit.val <= std::u64::MAX as u128 {
                    ir.add(
                        Data {
                            int: lit.val as u64,
                        },
                        Tag::Int,
                        expected,
                    )
                } else {
                    let extra = ir.extra_data(&lit.val.to_le_bytes());
                    ir.add(Data { extra }, Tag::LargeInt, expected)
                }
            }
            ast::Expr::FloatLiteral(span) => {
                let lit = FloatLiteral::parse(self.src(*span));
                let float_ty = lit.ty.map_or(TypeInfo::Float, |float_ty| {
                    TypeInfo::Primitive(float_ty.into())
                });
                ir.specify(expected, float_ty, errors, *span);
                ir.add(Data { float: lit.val }, Tag::Float, expected)
            }
            ast::Expr::StringLiteral(span) => {
                let i8_ty = ir.types.add(TypeInfo::Primitive(Primitive::I8));
                ir.specify(expected, TypeInfo::Pointer(i8_ty), errors, *span);
                
                let string = self.src(TSpan::new(span.start + 1, span.end - 1))
                    .replace("\\n", "\n")
                    .replace("\\t", "\t")
                    .replace("\\r", "\r")
                    .replace("\\0", "\0")
                    .replace("\\\"", "\"");
                let extra_len = ir._extra_len(string.as_bytes());
                // add zero byte
                ir.extra_data(&[b'\0']);
                ir.add(Data { extra_len }, Tag::String, expected)
            }
            ast::Expr::BoolLiteral { val, start } => {
                let span = TSpan::new(*start, start + if *val {4} else {5});
                ir.specify(expected, TypeInfo::Primitive(Primitive::Bool), errors, span);
                Ref::val(if *val { RefVal::True } else { RefVal::False })
            }
            ast::Expr::EnumLiteral { dot: _, ident } => {
                let variant_name = self.src(*ident);
                // avoid creating enum TypeInfo unnecessarily to avoid allocations and complex comparisons
                if let TypeInfo::Enum(names) = ir.types.get_type(expected) {
                    if !ir.types.get_names(names).iter().any(|s| *s == variant_name) {
                        let new_names = ir.types.extend_names(names, std::iter::once(variant_name.to_owned()));
                        ir.types.update_type(expected, TypeInfo::Enum(new_names));
                    }
                } else {
                    let variant = ir.types.add_names(std::iter::once(variant_name.to_owned()));
                    ir.types.specify(
                        expected,
                        TypeInfo::Enum(variant),
                        errors,
                        expr.span(self.ast).in_mod(self.module)
                    );
                }
                let extra = ir.extra_data(variant_name.as_bytes());
                ir.add(Data { extra_len: (extra, variant_name.len() as u32)  }, Tag::EnumLit, expected)
            }
            ast::Expr::Nested(_, inner) => {
                return self.reduce_expr_any(errors, ir, &self.ast[*inner], expected, ret, get_var);
            }
            ast::Expr::Unit(span) => {
                ir.specify(expected, TypeInfo::Primitive(Primitive::Unit), errors, *span);
                Ref::val(RefVal::Unit)
            }
            ast::Expr::Variable(span) => {
                let name = &self.ast.sources[self.module.idx()].0[span.range()];
                match self.resolve(name) {
                    Ok(resolved) => match resolved {
                        Resolved::Var(ty, var) => {
                            ir.types.merge(ty, expected, errors, self.module, *span);
                            return ExprResult::VarRef(var);
                        }
                        Resolved::Func(f) => return ExprResult::Func(f),
                        Resolved::Type(t) => return ExprResult::Type(t),
                        Resolved::LocalType(t) => return ExprResult::LocalType(t),
                        Resolved::TypeProto(t) => return ExprResult::TypeProto(t),
                        Resolved::Module(m) => return ExprResult::Module(m),
                    },
                    Err(err) => {
                        errors.emit_span(err, span.in_mod(self.module));
                        ir.invalidate(expected);
                        Ref::val(RefVal::Undef)
                    }
                }
            }
            ast::Expr::Array(span, elems) => {
                let elems = &self.ast.expr_builder[*elems];
                let elem_ty = ir.types.add(TypeInfo::Unknown);
                let arr_ty = TypeInfo::Array(Some(elems.len() as u32), elem_ty);
                ir.types.specify(expected, arr_ty, errors, span.in_mod(self.module));
                //let arr = ir.add(Data { ty: expected }, Tag::Decl, expected);
                let arr = get_var(ir);
                let u64_ty = ir.types.add(TypeInfo::Primitive(Primitive::U64));
                for (i, elem) in elems.iter().enumerate() {
                    let elem_val = self.reduce_expr_val_spanned(errors, ir, &self.ast[*elem], elem_ty, ret, *span);
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
                ir.types.specify(expected, TypeInfo::Tuple(types), errors, span.in_mod(self.module));
                for (i, elem) in elems.iter().enumerate() {
                    let member_ty = types.iter().nth(i).unwrap();
                    let member_val = self.reduce_expr_idx_val(errors, ir, *elem, member_ty, ret);
                    let idx = ir.add(Data { int: i as u64 }, Tag::Int, i32_ty);
                    let member = ir.add(Data { bin_op: (var, idx) }, Tag::Member, member_ty);
                    ir.add_untyped(Tag::Store, Data { bin_op: (member, member_val) });
                }
                return ExprResult::Stored(var);
            }
            ast::Expr::If { start: _, cond, then } => {
                let after_block = self.gen_if_then(ir, errors, *cond, ret);

                ir.specify(expected, TypeInfo::Primitive(Primitive::Unit), errors, expr.span(self.ast));
                let then_ty = ir.types.add(TypeInfo::Unknown);
                self.reduce_expr(errors, ir, &self.ast[*then], then_ty, ret);
                ir.add_untyped(Tag::Goto, Data { int32: after_block.0 });
                ir.begin_block(after_block);
                Ref::UNIT
            }
            ast::Expr::IfElse { start: _, cond, then, else_ } => {
                let else_block = self.gen_if_then(ir, errors, *cond, ret);

                let after_block = ir.create_block();
                let then_val = self.reduce_expr_idx_val(errors, ir, *then, expected, ret);
                let then_exit = ir.current_block();
                ir.add_untyped(Tag::Goto, Data { int32: after_block.0, });
                ir.begin_block(else_block);
                let else_val = self.reduce_expr_idx_val(errors, ir, *else_, expected, ret);
                let else_exit = ir.current_block();
                ir.add_untyped(Tag::Goto, Data { int32: after_block.0, });
                ir.begin_block(after_block);

                let extra = ir.extra_data(&then_exit.bytes());
                ir.extra_data(&then_val.to_bytes());
                ir.extra_data(&else_exit.bytes());
                ir.extra_data(&else_val.to_bytes());
                ir.add(Data { extra_len: (extra, 2) }, Tag::Phi, expected)
            }
            ast::Expr::While { start: _, cond, body } => {
                ir.specify(expected, TypeInfo::Primitive(Primitive::Unit), errors, expr.span(self.ast));

                let cond_block = ir.create_block();
                let body_block = ir.create_block();
                let after_block = ir.create_block();

                ir.add_untyped(Tag::Goto, Data { int32: cond_block.0 });
                ir.begin_block(cond_block);
                
                let b = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
                let cond = self.reduce_expr_idx_val(errors, ir, *cond, b, ret);

                let branch_extra = ir.extra_data(&body_block.0.to_le_bytes());
                ir.extra_data(&after_block.0.to_le_bytes());
                ir.add_untyped(Tag::Branch, Data { branch: (cond, branch_extra) });
                ir.begin_block(body_block);
                let body_ty = ir.types.add(TypeInfo::Unknown);
                self.reduce_expr_idx_val(errors, ir, *body, body_ty, ret);
                ir.add_untyped(Tag::Goto, Data { int32: cond_block.0 });
                ir.begin_block(after_block);
                Ref::val(RefVal::Unit)
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
                    expected: TypeTableIndex,
                    ret: TypeTableIndex,
                    errors: &mut Errors
                ) -> Ref {
                    let arg_count = args.len() + if this_arg.is_some() { 1 } else { 0 };
                    
                    let header = scope.ctx.funcs[func.idx()].header();
                    let info = header.return_type.as_info(&mut ir.types);

                    ir.specify(expected, info, errors, expr.span(scope.ast));
                    let invalid_arg_count = if header.varargs {
                        arg_count < header.params.len()
                    } else {
                        arg_count != header.params.len()
                    };
                    if invalid_arg_count {
                        errors.emit_span(Error::InvalidArgCount, expr.span(scope.ast).in_mod(scope.module));
                        Ref::val(RefVal::Undef)
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
                                        this_span.in_mod(scope.module)
                                    );
                                    bytes.extend(this.to_bytes());
                                }
                                None => {
                                    errors.emit_span(Error::NotAnInstanceMethod, this_span.in_mod(scope.module))
                                }
                            }
                        }
                        for (arg, ty) in args.zip(param_iter) {
                            let info = ty.as_ref().map_or(TypeInfo::Unknown, |ty| ty.as_info(&mut ir.types));
                            let ty = ir
                                .types
                                .add(info);
                            let expr = scope.reduce_expr_idx_val(errors, ir, arg, ty, ret);
                            bytes.extend(&expr.to_bytes());
                        }
                        let extra = ir.extra_data(&bytes);
                        ir.add(Data { extra_len: (extra, arg_count as u32) }, Tag::Call, expected)
                    }
                }
                let called = &self.ast[*func];
                match self.reduce_expr(errors, ir, called, called_ty, ret) {
                    ExprResult::Func(key) => {
                        gen_call(self, expr, key, None, args.iter().copied(), ir, expected, ret, errors)
                    }
                    ExprResult::Method(self_var, key) => {
                        let called_span = called.span(self.ast);
                        let this = Some((self_var, called_ty, called_span));
                        gen_call(self, expr, key, this, args.iter().copied(), ir, expected, ret, errors)
                    }
                    ExprResult::Type(ty) => {
                        let TypeDef::Struct(struct_) = &self.ctx.types[ty.idx()];
                        let generics = ir.types.add_multiple((0..struct_.generic_count).map(|_| TypeInfo::Unknown));
                        ir.specify(expected, TypeInfo::Resolved(ty, generics), errors, expr.span(self.ast));

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
                                    self.reduce_expr_idx_val(errors, ir, *member_val, member_ty, ret);
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
                            Ref::val(RefVal::Undef)
                        }
                    }
                    ExprResult::VarRef(val) => {
                        let span = self.ast[*func].span(self.ast);

                        match ir.types.get_type(called_ty) {
                            TypeInfo::Invalid => { ir.invalidate(expected); Ref::UNDEF }
                            TypeInfo::Array(_, member_ty) => {
                                ir.types.merge(expected, member_ty, errors, self.module, span);

                                if args.len() != 1 {
                                    errors.emit_span(
                                        Error::InvalidArgumentCountForArrayIndex,
                                        expr.span_in(self.ast, self.module)
                                    );
                                    ir.invalidate(expected);
                                    Ref::UNDEF
                                } else {
                                    let idx_ty = ir.types.add(TypeInfo::Int);
                                    let idx_expr = &self.ast[args[0]];
                                    let idx = self.reduce_expr_val_spanned(
                                        errors, ir, idx_expr, idx_ty, ret,
                                        idx_expr.span(self.ast)
                                    );
                                    return ExprResult::VarRef(
                                        ir.add(Data { bin_op: (val, idx) }, Tag::Member, expected)
                                    )
                                }
                            }
                            TypeInfo::Unknown => {
                                errors.emit_span(Error::TypeMustBeKnownHere, span.in_mod(self.module));
                                ir.invalidate(expected);
                                Ref::UNDEF
                            }
                            _ => {
                                errors.emit_span(Error::UnexpectedType, span.in_mod(self.module));
                                ir.invalidate(expected);
                                Ref::UNDEF
                            }
                        }
                    }
                    _ => {
                        if !ir.types.get_type(called_ty).is_invalid() {
                            errors.emit_span(Error::FunctionOrTypeExpected, expr.span(self.ast).in_mod(self.module));
                        }
                        ir.invalidate(expected);
                        Ref::val(RefVal::Undef)
                    }
                }
            }
            ast::Expr::UnOp(_, un_op, val) => {
                let span = expr.span(self.ast);
                let (expected, tag) = match un_op {
                    UnOp::Neg => (expected, Tag::Neg),
                    UnOp::Not => (ir.types.add(TypeInfo::Primitive(Primitive::Bool)), Tag::Not),
                    UnOp::Ref => {
                        let unknown_ty = ir.types.add(TypeInfo::Unknown);
                        let ptr_ty = TypeInfo::Pointer(unknown_ty);
                        ir.types.specify(expected, ptr_ty, errors, span.in_mod(self.module));
                        let inner_expected = match ir.types.get_type(expected) {
                            TypeInfo::Pointer(inner) => inner,
                            _ => ir.types.add(TypeInfo::Invalid)
                        };
                        return ExprResult::Val(match 
                            self.reduce_expr(errors, ir, &self.ast[*val], inner_expected, ret)
                        {
                            ExprResult::VarRef(r) | ExprResult::Stored(r) => {
                                let idx = r.into_ref().expect("VarRef should never be constant");
                                let inner_ty =ir.ir()[idx as usize].ty;

                                ir.types.specify(
                                    expected,
                                    TypeInfo::Pointer(inner_ty), errors,
                                    span.in_mod(self.module));
                                ir.add(Data { un_op: r }, Tag::AsPointer, expected)
                            }
                            ExprResult::Val(val) => {
                                let val_expected = match ir.types.get_type(expected) {
                                    TypeInfo::Pointer(inner) => inner,
                                    _ => ir.types.add(TypeInfo::Invalid)
                                };
                                let var = ir.add(Data { ty: val_expected }, Tag::Decl, val_expected);
                                ir.add_unused_untyped(Tag::Store, Data { bin_op: (var, val) });
                                ir.add(Data { un_op: var }, Tag::AsPointer, expected)
                            }
                            _ => {
                                errors.emit_span(Error::CantTakeRef, expr.span(self.ast).in_mod(self.module));
                                Ref::UNDEF
                            }
                        })
                    }
                    UnOp::Deref => {
                        let expected = ir.types.add(TypeInfo::Pointer(expected));
                        let pointer_val = 
                            self.reduce_expr_idx_val(errors, ir, *val, expected, ret);
                        return ExprResult::VarRef(pointer_val); // just use the pointer value as variable
                    }
                };
                let inner = self.reduce_expr_idx_val(errors, ir, *val, expected, ret);
                let res = match un_op {
                    UnOp::Neg => match ir.types.get_type(expected) {
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
                ir.add(Data { un_op: inner }, tag, expected)
            }
            ast::Expr::BinOp(op, l, r) => {
                if let Operator::Assignment(assignment) = op {
                    ir.specify(expected, TypeInfo::Primitive(Primitive::Unit), errors, expr.span(self.ast));
                    let var_ty = ir.types.add_unknown();
                    let lval = self.reduce_lval_expr(errors, ir, &self.ast[*l], var_ty, ret);
                    let r = self.reduce_expr_idx_val(errors, ir, *r, var_ty, ret);

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
                    let is_boolean = matches!(
                        op,
                        Operator::Or | Operator::And
                    );
                    let is_logical = matches!(
                        op,
                        Operator::Equals |Operator::NotEquals 
                        | Operator::LT | Operator::GT | Operator::LE | Operator::GE
                    );
    
                    // binary operations always require the same type on both sides right now
                    let inner_ty = if is_boolean {
                        ir.types.add(TypeInfo::Primitive(Primitive::Bool))
                    } else if is_logical {
                        ir.types.add(TypeInfo::Unknown)
                    } else {
                        expected
                    };
                    let l = self.reduce_expr_idx_val(errors, ir, *l, inner_ty, ret);
                    let r = self.reduce_expr_idx_val(errors, ir, *r, inner_ty, ret);
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
                    ir.add(Data { bin_op: (l, r) }, tag, expected)
                }
            }
            ast::Expr::MemberAccess { left, name } => {
                let member = &self.ast.src(self.module).0[name.range()];
                let left_ty = ir.types.add(TypeInfo::Unknown);
                enum MemberAccessType {
                    Var(Ref),
                    Module(ModuleId),
                    AssociatedFunction(SymbolKey),
                    Invalid
                }
                let left = &self.ast[*left];
                let left_val = match self.reduce_expr(errors, ir, left, left_ty, ret) {
                    ExprResult::VarRef(r) | ExprResult::Stored(r) => MemberAccessType::Var(r),
                    ExprResult::Val(val) => {
                        let var = ir.add(Data { ty: expected }, Tag::Decl, expected);
                        ir.add_unused_untyped(Tag::Store, Data { bin_op: (var, val) });
                        MemberAccessType::Var(var)
                    }
                    ExprResult::Type(ty) => MemberAccessType::AssociatedFunction(ty),
                    ExprResult::Func(_) | ExprResult::Method(_, _)
                    | ExprResult::LocalType(_) | ExprResult::TypeProto(_) => {
                        errors.emit_span(Error::NonexistantMember, name.in_mod(self.module));
                        MemberAccessType::Invalid
                    }
                    ExprResult::Module(id) => MemberAccessType::Module(id),
                };

                match left_val {
                    MemberAccessType::Var(var) => {
                        let (ty, idx) = match ir.types.get_type(left_ty) {
                            TypeInfo::Resolved(key, generics) => {
                                let TypeDef::Struct(struct_) = &self.ctx.types[key.idx()];
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
                                    errors.emit_span(Error::NonexistantMember, name.in_mod(self.module));
                                    (TypeInfo::Invalid.into(), 0)
                                }
                            }
                            TypeInfo::Invalid => (TypeInfo::Invalid.into(), 0),
                            TypeInfo::Unknown => {
                                errors.emit_span(Error::TypeMustBeKnownHere, left.span_in(self.ast, self.module));
                                (TypeInfo::Invalid.into(), 0)
                            }
                            _ => {
                                errors.emit_span(Error::NonexistantMember, left.span_in(self.ast, self.module));
                                (TypeInfo::Invalid.into(), 0)
                            }
                        };
                        ir.specify_or_merge(expected, ty, errors, self.module, expr.span(self.ast));
                        let i32_ty = ir.types.add(TypeInfo::Primitive(Primitive::I32));
                        let idx = ir.add(
                            Data { int: idx as u64 },
                            Tag::Int,
                            i32_ty
                        );
                        let member = ir.add(
                            Data {
                                bin_op: (var, idx),
                            },
                            Tag::Member,
                            expected,
                        );
                        return ExprResult::VarRef(member);
                    }
                    MemberAccessType::Module(id) => {
                        let module = &self.globals[id];
                        if let Some(symbol) = module.get(member) {
                            return match *symbol {
                                Symbol::Func(f) => ExprResult::Func(f),
                                Symbol::Type(t) => ExprResult::Type(t),
                                Symbol::LocalType(t) => ExprResult::LocalType(t),
                                Symbol::TypeProto(t) => ExprResult::TypeProto(t),
                                Symbol::Generic(_) => todo!(), // is this a possibility
                                Symbol::Module(m) => ExprResult::Module(m),
                                Symbol::Var { ty: _, var } => ExprResult::VarRef(var),
                            };
                        } else {
                            errors.emit_span(Error::UnknownIdent, name.in_mod(self.module));
                            ir.invalidate(expected);
                            Ref::UNDEF
                        }
                    }
                    MemberAccessType::AssociatedFunction(key) => {
                        let TypeDef::Struct(ty) = self.ctx.get_type(key);
                        if let Some(method) = ty.methods.get(member) {
                            return ExprResult::Func(*method);
                        } else {
                            errors.emit_span(Error::UnknownFunction, name.in_mod(self.module));
                            ir.invalidate(expected);
                            Ref::UNDEF
                        }
                    }
                    MemberAccessType::Invalid => {
                        ir.invalidate(expected);
                        Ref::UNDEF
                    }
                }
            }
            ast::Expr::TupleIdx { expr: indexed, idx, end: _ } => {
                let indexed_ty = ir.types.add(TypeInfo::Unknown);
                let expr_var = match self.reduce_expr(errors, ir, &self.ast[*indexed], indexed_ty, ret) {
                    ExprResult::VarRef(r) | ExprResult::Stored(r) => r,
                    ExprResult::Val(val) => {
                        let var = ir.add(Data { ty: expected }, Tag::Decl, expected);
                        ir.add_unused_untyped(Tag::Store, Data { bin_op: (var, val) });
                        var
                    }
                    ExprResult::Func(_) | ExprResult::Method(_, _) 
                    | ExprResult::Type(_) | ExprResult::LocalType(_) | ExprResult::TypeProto(_)
                    | ExprResult::Module(_) => {
                        errors.emit_span(Error::TupleIndexingOnNonValue, expr.span_in(self.ast, self.module));
                        ir.invalidate(expected);
                        return ExprResult::Val(Ref::UNDEF)
                    }
                };
                let TypeInfo::Tuple(elems) = ir.types.get_type(indexed_ty) else {
                    println!("Indexing non-tuple");
                    errors.emit_span(Error::TypeMustBeKnownHere, expr.span_in(self.ast, self.module));
                    return ExprResult::Val(Ref::UNDEF)
                };
                let Some(elem_ty) = elems.iter().nth(*idx as usize) else {
                    errors.emit_span(Error::TupleIndexOutOfRange, expr.span_in(self.ast, self.module));
                    return ExprResult::Val(Ref::UNDEF)
                };
                ir.types.merge(expected, elem_ty, errors, self.module, expr.span(self.ast));
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

                ir.specify(expected, target, errors, expr.span(self.ast));
                let inner_ty = ir.types.add(TypeInfo::Unknown);
                let val = self.reduce_expr_idx_val(errors, ir, *val, inner_ty, ret);
                //TODO: check table for available casts
                ir.add(Data { un_op: val, }, Tag::Cast, expected)
            }
            ast::Expr::Root(_) => {
                return ExprResult::Module(ModuleId::ROOT)
            }
        };
        ExprResult::Val(r)
    }

    fn gen_if_then(&mut self, ir: &mut IrBuilder, errors: &mut Errors, cond: ExprRef, ret: TypeTableIndex)
    -> BlockIndex {
        let b = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
        let cond = self.reduce_expr_idx_val(errors, ir, cond, b, ret);
        let then_block = ir.create_block();
        let other_block = ir.create_block();

        let branch_extra = ir.extra_data(&then_block.0.to_le_bytes());
        ir.extra_data(&other_block.0.to_le_bytes());

        ir.add_untyped(Tag::Branch, Data { branch: (cond, branch_extra) });
        ir.begin_block(then_block);
        other_block
    }
}
