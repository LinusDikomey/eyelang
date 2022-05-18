use crate::{
    ast::{self, Expr, ModuleId, UnOp, TSpan, ExprRef},
    error::{Error, Errors},
    lexer::{tokens::{Operator, AssignType, IntLiteral, FloatLiteral}, Span},
    types::Primitive,
};
use std::{borrow::Cow, collections::HashMap, ptr::NonNull};
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
    get_func: impl for<'a> Fn(&'a mut Scope, &str) -> Option<&'a Symbol>,
) {
    for (name, def) in defs {
        let ast::Definition::Function(def) = def else { continue };
        let Symbol::Func(func) = get_func(scope, name)
            .expect("Missing function after definition phase")
            else { panic!("Function expected") };
        
        let func_idx = func.idx();
        let header = match &scope.ctx.funcs[func_idx] {
            FunctionOrHeader::Func(_) => {
                unreachable!("Function shouldn't already be defined here")
            }
            FunctionOrHeader::Header(header) => header.clone(),
        };
        let ir = def.body.as_ref().map(|body| {
            let mut builder = IrBuilder::new(scope.module);
            let mut scope: Scope<'_> = scope.child(HashMap::with_capacity(header.params.len()));
            for (i, (name, ty)) in header.params.iter().enumerate() {
                let info = ty.into_info(&mut builder.types);
                let ty = builder.types.add(info);
                let param = builder.add(Data { int32: i as u32 }, Tag::Param, ty);
                scope
                    .info
                    .symbols
                    .to_mut()
                    .insert(name.clone(), Symbol::Var { ty, var: param });
            }
            let return_type = header.return_type.into_info(&mut builder.types);
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
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Symbol {
    Func(SymbolKey),
    Type(SymbolKey),
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

    fn resolve_local(&self, name: &str) -> Result<Resolved, Error> {
        self.resolve_local_recursive(name, 0)
    }

    fn resolve_local_recursive(&self, name: &str, depth: usize) -> Result<Resolved, Error> {
        //TODO: check if this is recursing with some kind of stack and return recursive type def error.
        if let Some(symbol) = self.symbols.get(name) {
            Ok(match symbol {
                Symbol::Func(f) => Resolved::Func(*f),
                Symbol::Type(t) => Resolved::Type(*t),
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
}

enum Resolved {
    Var(TypeTableIndex, Ref),
    Func(SymbolKey),
    Type(SymbolKey),
    Module(ModuleId),
}
impl Resolved {
    pub fn into_symbol(self) -> Option<Symbol> {
        match self {
            Resolved::Var(_, _) => None,
            Resolved::Func(id) => Some(Symbol::Func(id)),
            Resolved::Type(id) => Some(Symbol::Type(id)),
            Resolved::Module(id) => Some(Symbol::Module(id)),
        }
    }
}

#[derive(Debug)]
enum ExprResult {
    VarRef(Ref),
    Val(Ref),
    Func(SymbolKey),
    Type(SymbolKey),
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
                            Symbol::Type(ty) => Ok(TypeInfo::Resolved(*ty)),
                            _ => Err(Error::TypeExpected)
                        },
                    ModuleOrLocal::Local => match self.info.resolve_local(last.0)? {
                        Resolved::Type(ty) => Ok(TypeInfo::Resolved(ty)),
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
            ExprResult::Val(_) | ExprResult::Func(_) | ExprResult::Type(_) | ExprResult::Module(_) => {
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
            },
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
                match self.reduce_expr(errors, ir, &self.ast[*func], called_ty, ret) {
                    ExprResult::Func(key) => {
                        let header = self.ctx.funcs[key.idx()].header();
                        let info = header.return_type.into_info(&mut ir.types);
                        ir.specify(expected, info, errors, expr.span(self.ast));
                        let invalid_arg_count = if header.varargs {
                            args.len() < header.params.len()
                        } else {
                            args.len() != header.params.len()
                        };
                        if invalid_arg_count {
                            errors.emit_span(Error::InvalidArgCount, expr.span(self.ast).in_mod(self.module));
                            Ref::val(RefVal::Undef)
                        } else {
                            let params = header.params.iter().map(|(_, ty)| Some(ty.clone()));
                            let params = if header.varargs {
                                params
                                    .chain(std::iter::repeat(None))
                                    .take(args.len())
                                    .collect::<Vec<_>>()
                            } else {
                                params.collect::<Vec<_>>()
                            };
                            let mut bytes = Vec::with_capacity(8 + 4 * args.len());
                            bytes.extend(&key.bytes());
                            for (arg, ty) in args.iter().zip(params) {
                                let info = ty.map_or(TypeInfo::Unknown, |ty| ty.into_info(&mut ir.types));
                                let ty = ir
                                    .types
                                    .add(info);
                                let expr = self.reduce_expr_idx_val(errors, ir, *arg, ty, ret);
                                bytes.extend(&expr.to_bytes());
                            }
                            let extra = ir.extra_data(&bytes);
                            ir.add(
                                Data {
                                    extra_len: (extra, args.len() as u32),
                                },
                                Tag::Call,
                                expected,
                            )
                        }
                    }
                    ExprResult::Type(ty) => {
                        let TypeDef::Struct(struct_) = &self.ctx.types[ty.idx()];
                        ir.specify(expected, TypeInfo::Resolved(ty), errors, expr.span(self.ast));

                        if args.len() == struct_.members.len() {
                            let var = get_var(ir);
                            let member_types: Vec<TypeInfo> =
                                struct_.members.iter().map(|(_, ty)| ty.into_info(&mut ir.types)).collect();
                            let i32_ty = ir.types.add(TypeInfo::Primitive(Primitive::I32));
                            for (i, (member_val, member_ty)) in
                                args.iter().zip(member_types).enumerate()
                            {
                                let member_ty = ir.types.add(member_ty);
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
                    ExprResult::Func(_) | ExprResult::Type(_) => {
                        errors.emit_span(Error::NonexistantMember, name.in_mod(self.module));
                        MemberAccessType::Invalid
                    }
                    ExprResult::Module(id) => MemberAccessType::Module(id),
                };

                match left_val {
                    MemberAccessType::Var(var) => {
                        let (ty, idx) = match ir.types.get_type(left_ty) {
                            TypeInfo::Resolved(key) => {
                                let TypeDef::Struct(struct_) = &self.ctx.types[key.idx()];
                                if let Some((i, (_, ty))) = struct_
                                    .members
                                    .iter()
                                    .enumerate()
                                    .find(|(_, (name, _))| name == member)
                                {
                                    (ty.into_info(&mut ir.types), i)
                                } else {
                                    errors.emit_span(Error::NonexistantMember, name.in_mod(self.module));
                                    (TypeInfo::Invalid, 0)
                                }
                            }
                            TypeInfo::Invalid => (TypeInfo::Invalid, 0),
                            TypeInfo::Unknown => {
                                errors.emit_span(Error::TypeMustBeKnownHere, left.span_in(self.ast, self.module));
                                (TypeInfo::Invalid, 0)
                            }
                            _ => {
                                errors.emit_span(Error::NonexistantMember, left.span_in(self.ast, self.module));
                                (TypeInfo::Invalid, 0)
                            }
                        };
                        ir.specify(expected, ty, errors, expr.span(self.ast));
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
                                Symbol::Module(m) => ExprResult::Module(m),
                                Symbol::Var { ty: _, var } => ExprResult::VarRef(var),
                            };
                        } else {
                            errors.emit_span(Error::UnknownIdent, name.in_mod(self.module));
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
