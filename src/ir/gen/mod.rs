use crate::{
    ast::{self, BlockItem, Expr, ModuleId, UnOp},
    error::{Error, Errors},
    lexer::tokens::{Operator, AssignType},
    types::Primitive,
};
use std::{borrow::Cow, collections::HashMap, ptr::NonNull};

use self::builder::IrBuilder;

use super::{typing::*, *};

mod scope;
mod types;
mod builder;

pub fn reduce(modules: &ast::Modules, mut errors: Errors) -> Result<Module, Errors> {
    let mut ctx = TypingCtx {
        funcs: Vec::new(),
        types: Vec::new(),
    };
    let globals = types::gen_globals(modules, &mut ctx, &mut errors);

    for (id, ast) in modules.iter() {
        let mut scope = Scope::new(&mut ctx, &globals[id.idx()], &globals, id);

        for (name, def) in &ast.definitions {
            let module_globals = &globals[id.idx()];
            match def {
                ast::Definition::Function(def) => {
                    let Symbol::Func(func) = module_globals.get(name)
                        .expect("Missing function after global definition phase")
                        else { panic!("Function expected") };
                    let header = match &scope.ctx.funcs[func.idx()] {
                        FunctionOrHeader::Func(_) => {
                            unreachable!("Function shouldn't already be defined here")
                        }
                        FunctionOrHeader::Header(header) => header.clone(),
                    };
                    let ir = def.body.as_ref().map(|body| {
                        let mut builder = IrBuilder::new(id);
                        let mut scope: Scope<'_> = scope.child();
                        for (i, (name, ty)) in header.params.iter().enumerate() {
                            let ty = builder.types.add((*ty).into());
                            let param = builder.add(Data { int32: i as u32 }, Tag::Param, ty);
                            scope
                                .info
                                .symbols
                                .to_mut()
                                .insert(name.clone(), Symbol::Var { ty, var: param });
                        }
                        let expected = builder.types.add(header.return_type.into());
                        let (val, block) = scope.reduce_block_or_expr(
                            &mut errors,
                            &mut builder,
                            body,
                            expected,
                            expected,
                        );
                        if block == false
                            || header.return_type == TypeRef::Primitive(Primitive::Unit)
                        {
                            builder.add_unused_untyped(Tag::Ret, Data { un_op: val });
                        }
                        builder.finish()
                    });

                    scope.ctx.funcs[func.idx()] = FunctionOrHeader::Func(Function {
                        name: name.clone(),
                        header,
                        ir,
                    });
                }
                _ => {}
            }
        }
    }
    if errors.has_errors() {
        return Err(errors);
    }
    let funcs = ctx
        .funcs
        .into_iter()
        .map(|func| match func {
            FunctionOrHeader::Header(_) => panic!("Function was generated"),
            FunctionOrHeader::Func(func) => func.finalize(),
        })
        .collect();
    Ok(Module {
        name: "MainModule".to_owned(),
        funcs,
        types: ctx.types.into_iter().map(|def| def.finalize()).collect(),
    })
}

#[derive(Clone, Copy)]
pub enum Symbol {
    Func(SymbolKey),
    Type(SymbolKey),
    Module(ModuleId),
    Var { ty: TypeTableIndex, var: Ref },
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
                .map(|parent| parent.resolve_local(name))
                .transpose()?
                .ok_or_else(|| Error::UnknownIdent)
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
            Self::Func(f) => f.header(),
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

/*
fn define_type(
    info: &mut ScopeInfo,
    ctx: &mut TypingCtx,
    types: Option<&mut TypeTable>,
    name: &str,
    def: &StructDefinition,
    module: ModuleId,
    errors: &mut Errors
) -> SymbolKey {
    let members = def.members.iter().map(|(name, ty, start, end)| {
        let resolved = if let Some(types) = types {
            resolve_type(info, ctx, types, ty, errors)
        } else {
            resolve_type_noinfer(info, ctx, ty, errors)
        };
        (
            name.clone(),
            match resolved {
                Ok(ty) => ty,
                Err(err) => {
                    errors.emit(err, *start, *end, module);
                    TypeRef::Invalid
                }
            }
        )
    }).collect();
    let key = SymbolKey::new(ctx.types.len() as u64);
    ctx.types.push(TypeDef::Struct(Struct { members, name: name.to_owned() }));
    debug_assert!(previous.is_none(), "Duplicate type definition inserted");
    let previous = info.symbols.insert(name.to_owned(), Symbol::Type(key));
    key
}
*/

/*fn define_func_header<'a>(
    info: &mut ScopeInfo,
    ctx: &mut TypingCtx,
    name: String,
    func: &ast::Function,
    errors: &mut Errors
) -> FunctionHeader {
    let params = func
        .params
        .iter()
        .map(|(name, arg, start, end)| {
            let t = match resolve_type_noinfer(info, ctx, arg, errors) {
                Ok(t) => t,
                Err(err) => {
                    errors.emit(err, *start, *end, info.module);
                    TypeRef::Invalid
                }
            };
            (name.clone(), t)
        })
        .collect();
    /*let vararg = func.vararg.as_ref().map(|(name, ty, start, end)| {
        Ok((
            name.clone(),
            resolve_type_noinfer(info, ctx, ty, errors)
                .map_err(|err| CompileError { err, start: *start, end: *end })?
        ))
    }).transpose();
    let vararg = errors.emit_unwrap(vararg, None);
    */

    let return_type = resolve_type_noinfer(info, ctx, &func.return_type.0, errors)
        .map_err(|err| CompileError { err, span: Span::new(func.return_type.1, func.return_type.2, info.module) });
    let return_type = errors.emit_unwrap(return_type, TypeRef::Invalid);
    FunctionHeader { params, return_type, varargs: func.varargs, name }
}*/

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
        module: ModuleId,
    ) -> Ref {
        self.try_get_or_load(ir, ty).unwrap_or_else(|| {
            errors.emit(Error::ExpectedValueFoundDefinition, 0, 0, module);
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
struct Scope<'s> {
    ctx: &'s mut TypingCtx,
    globals: &'s [HashMap<String, Symbol>],
    module: ModuleId,
    info: ScopeInfo<'s>,
}

impl<'s> Scope<'s> {
    pub fn new(
        ctx: &'s mut TypingCtx,
        symbols: &'s HashMap<String, Symbol>,
        globals: &'s [HashMap<String, Symbol>],
        module: ModuleId,
    ) -> Self {
        Self {
            ctx,
            globals,
            module,
            info: ScopeInfo {
                parent: None,
                symbols: Cow::Borrowed(symbols),
            },
        }
    }
    pub fn child<'c>(&'c mut self) -> Scope<'c> {
        Scope {
            ctx: &mut *self.ctx,
            globals: self.globals,
            module: self.module,
            info: ScopeInfo {
                parent: Some(NonNull::from(&mut self.info)),
                symbols: Cow::Owned(HashMap::new()),
            },
        }
    }

    fn resolve(&mut self, _types: &mut TypeTable, name: &str) -> Result<Resolved, Error> {
        self.info.resolve_local(name)
    }

    fn resolve_type(&mut self, unresolved: &ast::UnresolvedType) -> Result<TypeRef, Error> {
        match unresolved {
            ast::UnresolvedType::Primitive(p) => Ok(TypeRef::Primitive(*p)),
            ast::UnresolvedType::Unresolved(path) => {
                let (root, iter, last) = path.segments();
                // no last segment means it must point to the root module
                let Some(last) = last else { return Err(Error::TypeExpected) };
                enum ModuleOrLocal {
                    Module(ModuleId),
                    Local
                }
                
                let mut current_module = if root {
                    ModuleOrLocal::Module(ModuleId::ROOT)
                } else {
                    ModuleOrLocal::Local
                };

                for name in iter {
                    let look_from = match current_module {
                        ModuleOrLocal::Module(m) => m,
                        ModuleOrLocal::Local => self.module
                    };
                    match self.globals[look_from.idx()].get(name) {
                        Some(Symbol::Module(m)) => current_module = ModuleOrLocal::Module(*m),
                        Some(_) => panic!("1"),//return Err(Error::ModuleExpected),
                        None => return Err(Error::UnknownModule)
                    }
                }
                match current_module {
                    ModuleOrLocal::Module(m) => match self.globals[m.idx()]
                        .get(last.as_str())
                        .ok_or(Error::UnknownIdent)? {
                            Symbol::Type(ty) => Ok(TypeRef::Resolved(*ty)),
                            _ => Err(Error::TypeExpected)
                        },
                    ModuleOrLocal::Local => match self.info.resolve_local(last.as_str())? {
                        Resolved::Type(ty) => Ok(TypeRef::Resolved(ty)),
                        _ => Err(Error::TypeExpected)
                    }
                }
            }
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

    // returns (ref, is_block)
    fn reduce_block_or_expr(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        be: &ast::BlockOrExpr,
        expected: TypeTableIndex,
        ret: TypeTableIndex,
    ) -> (Ref, bool) {
        match be {
            ast::BlockOrExpr::Block(block) => {
                self.reduce_block(errors, ir, block, expected, ret);
                (Ref::val(RefVal::Unit), true)
            }
            ast::BlockOrExpr::Expr(expr) => {
                (self.reduce_expr_val(errors, ir, expr, expected, ret), false)
            }
        }
    }

    fn reduce_block(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        block: &ast::Block,
        _expected: TypeTableIndex,
        ret: TypeTableIndex,
    ) {
        let mut scope = self.child(); //TODO: local definitions: &block.defs
                                      //ir.types.specify(expected, TypeInfo::Primitive(Primitive::Unit), errors);
        for item in &block.items {
            scope.reduce_stmt(errors, ir, item, ret);
        }
    }

    fn reduce_stmt(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        stmt: &BlockItem,
        ret: TypeTableIndex,
    ) {
        match stmt {
            BlockItem::Block(block) => {
                let block_ty = ir.types.add(TypeInfo::Unknown);
                self.reduce_block(errors, ir, block, block_ty, ret);
            }
            BlockItem::Declare(name, _index, ty, val) => {
                let ty = match ty.as_ref().map(|ty| self.resolve_type(&ty)).transpose() {
                    Ok(t) => t,
                    Err(err) => {
                        errors.emit(err, 0, 0, self.module);
                        return;
                    }
                }
                .map_or(TypeInfo::Unknown, Into::into);
                let ty = ir.types.add(ty);

                let var = self.declare_var(ir, name.clone(), ty);

                if let Some(val) = val {
                    self.reduce_expr_store_into_var(errors, ir, val, var, ty, ret);
                }
            }
            BlockItem::Expr(expr) => {
                let expr_ty = ir.types.add(TypeInfo::Unknown);
                self.reduce_expr(errors, ir, expr, expr_ty, ret);
            }
        }
    }

    fn reduce_expr_val(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        expr: &Expr,
        expected: TypeTableIndex,
        ret: TypeTableIndex,
    ) -> Ref {
        self.reduce_expr(errors, ir, expr, expected, ret)
            .get_or_load(ir, expected, errors, self.module)
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
                errors.emit(Error::ExpectedValueFoundDefinition, 0, 0, self.module);
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
            ExprResult::VarRef(var) => var,
            ExprResult::Val(_) | ExprResult::Func(_) | ExprResult::Type(_) | ExprResult::Module(_) => {
                errors.emit(Error::CantAssignTo, 0, 0, self.module);
                Ref::UNDEF
            }
            ExprResult::Stored(_) => unreachable!(),
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
        let r = match expr {
            ast::Expr::Return(ret_val) => {
                let r = self.reduce_expr_val(errors, ir, ret_val, ret, ret);
                ir.specify(expected, TypeInfo::Primitive(Primitive::Never), errors);
                ir.add_untyped(Tag::Ret, Data { un_op: r });
                Ref::val(RefVal::Undef)
            }
            ast::Expr::IntLiteral(lit) => {
                let int_ty = lit
                    .ty
                    .map_or(TypeInfo::Int, |int_ty| TypeInfo::Primitive(int_ty.into()));
                ir.specify(expected, int_ty, errors);
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
            ast::Expr::FloatLiteral(lit) => {
                let float_ty = lit.ty.map_or(TypeInfo::Float, |float_ty| {
                    TypeInfo::Primitive(float_ty.into())
                });
                ir.specify(expected, float_ty, errors);
                ir.add(Data { float: lit.val }, Tag::Float, expected)
            }
            ast::Expr::StringLiteral(string) => {
                ir.specify(expected, TypeInfo::Primitive(Primitive::String), errors);
                let extra_len = ir._extra_len(string.as_bytes());
                // add zero byte
                ir.extra_data(&[b'\0']);
                ir.add(Data { extra_len }, Tag::String, expected)
            }
            ast::Expr::BoolLiteral(b) => {
                ir.specify(expected, TypeInfo::Primitive(Primitive::Bool), errors);
                Ref::val(if *b { RefVal::True } else { RefVal::False })
            }
            ast::Expr::Unit => {
                ir.specify(expected, TypeInfo::Primitive(Primitive::Unit), errors);
                Ref::val(RefVal::Unit)
            }
            ast::Expr::Variable(name) => match self.resolve(&mut ir.types, name) {
                Ok(resolved) => match resolved {
                    Resolved::Var(ty, var) => {
                        ir.types.merge(ty, expected, errors, self.module);
                        return ExprResult::VarRef(var);
                    }
                    Resolved::Func(f) => return ExprResult::Func(f),
                    Resolved::Type(t) => return ExprResult::Type(t),
                    Resolved::Module(m) => return ExprResult::Module(m),
                },
                Err(err) => {
                    errors.emit(err, 0, 0, self.module);
                    ir.specify(expected, TypeInfo::Invalid, errors);
                    Ref::val(RefVal::Undef)
                }
            },
            ast::Expr::If(if_) => {
                let ast::If { cond, then, else_ } = &**if_;
                let b = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
                let cond = self.reduce_expr_val(errors, ir, cond, b, ret);
                let then_block = ir.create_block();
                let other_block = ir.create_block();

                let branch_extra = ir.extra_data(&then_block.0.to_le_bytes());
                ir.extra_data(&other_block.0.to_le_bytes());

                ir.add_untyped(Tag::Branch, Data { branch: (cond, branch_extra) });
                ir.begin_block(then_block);

                let val = if let Some(else_) = else_ {
                    let after_block = ir.create_block();
                    let (then_val, _) = self.reduce_block_or_expr(errors, ir, then, expected, ret);
                    ir.add_untyped(Tag::Goto, Data { int32: after_block.0, });
                    ir.begin_block(other_block);
                    let (else_val, _) = self.reduce_block_or_expr(errors, ir, else_, expected, ret);
                    ir.add_untyped(Tag::Goto, Data { int32: after_block.0, });
                    ir.begin_block(after_block);

                    let extra = ir.extra_data(&then_block.bytes());
                    ir.extra_data(&then_val.to_bytes());
                    ir.extra_data(&other_block.bytes());
                    ir.extra_data(&else_val.to_bytes());
                    ir.add(
                        Data {
                            extra_len: (extra, 2),
                        },
                        Tag::Phi,
                        expected,
                    )
                } else {
                    ir.specify(expected, TypeInfo::Primitive(Primitive::Unit), errors);
                    let then_ty = ir.types.add(TypeInfo::Unknown);
                    self.reduce_block_or_expr(errors, ir, then, then_ty, ret);
                    ir.add_untyped(Tag::Goto, Data { int32: other_block.0 });
                    ir.begin_block(other_block);

                    Ref::val(RefVal::Unit)
                };
                val
            }
            ast::Expr::While(while_) => {
                let ast::While { cond, body } = &**while_;

                ir.specify(expected, TypeInfo::Primitive(Primitive::Unit), errors);

                let cond_block = ir.create_block();
                let body_block = ir.create_block();
                let after_block = ir.create_block();

                ir.add_untyped(Tag::Goto, Data { int32: cond_block.0 });
                ir.begin_block(cond_block);
                
                let b = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
                let cond = self.reduce_expr_val(errors, ir, cond, b, ret);

                let branch_extra = ir.extra_data(&body_block.0.to_le_bytes());
                ir.extra_data(&after_block.0.to_le_bytes());
                ir.add_untyped(Tag::Branch, Data { branch: (cond, branch_extra) });
                ir.begin_block(body_block);
                let body_ty = ir.types.add(TypeInfo::Unknown);
                self.reduce_block_or_expr(errors, ir, body, body_ty, ret);
                ir.add_untyped(Tag::Goto, Data { int32: cond_block.0 });
                ir.begin_block(after_block);
                Ref::val(RefVal::Unit)
            }
            ast::Expr::FunctionCall(func_expr, args) => {
                let func_ty = ir.types.add(TypeInfo::Unknown);
                match self.reduce_expr(errors, ir, func_expr, func_ty, ret) {
                    ExprResult::Func(key) => {
                        let header = self.ctx.funcs[key.idx()].header();
                        ir.specify(expected, header.return_type.into(), errors);
                        let invalid_arg_count = if header.varargs {
                            args.len() < header.params.len()
                        } else {
                            args.len() != header.params.len()
                        };
                        if invalid_arg_count {
                            errors.emit(Error::InvalidArgCount, 0, 0, self.module);
                            Ref::val(RefVal::Undef)
                        } else {
                            let params = header.params.iter().map(|(_, ty)| Some(*ty));
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
                                let ty = ir
                                    .types
                                    .add(ty.map(|ty| ty.into()).unwrap_or(TypeInfo::Unknown));
                                let expr = self.reduce_expr_val(errors, ir, arg, ty, ret);
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
                        ir.specify(expected, TypeInfo::Resolved(ty), errors);

                        if args.len() != struct_.members.len() {
                            errors.emit(Error::InvalidArgCount, 0, 0, self.module);
                            Ref::val(RefVal::Undef)
                        } else {
                            let var = get_var(ir);
                            let member_types: Vec<TypeInfo> =
                                struct_.members.iter().map(|(_, ty)| (*ty).into()).collect();
                            for (i, (member_val, member_ty)) in
                                args.iter().zip(member_types).enumerate()
                            {
                                let member_ty = ir.types.add(member_ty);
                                let member_val =
                                    self.reduce_expr_val(errors, ir, member_val, member_ty, ret);
                                let member = ir.add(
                                    Data {
                                        member: (var, i as u32),
                                    },
                                    Tag::Member,
                                    member_ty,
                                );
                                ir.add_untyped(Tag::Store, Data { bin_op: (member, member_val) });
                            }
                            return ExprResult::Stored(var);
                        }
                    }
                    _ => {
                        if ir.types.get_type(func_ty) != TypeInfo::Invalid {
                            errors.emit(Error::FunctionOrTypeExpected, 0, 0, self.module);
                        }
                        ir.specify(expected, TypeInfo::Invalid, errors);
                        Ref::val(RefVal::Undef)
                    }
                }
            }
            ast::Expr::UnOp(un_op, val) => {
                let (expected, tag) = match un_op {
                    UnOp::Neg => (expected, Tag::Neg),
                    UnOp::Not => (ir.types.add(TypeInfo::Primitive(Primitive::Bool)), Tag::Not),
                };
                let inner = self.reduce_expr_val(errors, ir, val, expected, ret);
                let res = match un_op {
                    UnOp::Neg => match ir.types.get_type(expected) {
                        TypeInfo::Float | TypeInfo::Int | TypeInfo::Unknown => Ok(()),
                        TypeInfo::Primitive(p) => {
                            if let Some(int) = p.as_int() {
                                if !int.is_signed() {
                                    Err(Error::CantNegateType)
                                } else {
                                    Ok(())
                                }
                            } else if let Some(_) = p.as_float() {
                                Ok(())
                            } else {
                                Err(Error::CantNegateType)
                            }
                        }
                        _ => Err(Error::CantNegateType),
                    }
                    UnOp::Not => Ok(()) // type was already constrained to be a boolean
                };
                if let Err(err) = res {
                    errors.emit(err, 0, 0, self.module);
                }
                ir.add(Data { un_op: inner }, tag, expected)
            }
            ast::Expr::BinOp(op, sides) => {
                let (l, r) = &**sides;
                if let Operator::Assignment(assignment) = op {
                    ir.specify(expected, TypeInfo::Primitive(Primitive::Unit), errors);
                    let var_ty = ir.types.add_unknown();
                    let lval = self.reduce_lval_expr(errors, ir, l, var_ty, ret);
                    let r = self.reduce_expr_val(errors, ir, r, var_ty, ret);

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
                    let l = self.reduce_expr_val(errors, ir, l, inner_ty, ret);
                    let r = self.reduce_expr_val(errors, ir, r, inner_ty, ret);
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
            ast::Expr::MemberAccess(left, member) => {
                let left_ty = ir.types.add(TypeInfo::Unknown);
                enum MemberAccessType {
                    Var(Ref),
                    Module(ModuleId),
                    Invalid
                }
                let left = match self.reduce_expr(errors, ir, left, left_ty, ret) {
                    ExprResult::VarRef(r) | ExprResult::Stored(r) => MemberAccessType::Var(r),
                    ExprResult::Val(val) => {
                        let var = ir.add(Data { ty: expected }, Tag::Decl, expected);
                        ir.add_unused(Tag::Store, Data { bin_op: (var, val) }, expected);
                        MemberAccessType::Var(var)
                    }
                    ExprResult::Func(_) | ExprResult::Type(_) => {
                        errors.emit(Error::NonexistantMember, 0, 0, self.module);
                        MemberAccessType::Invalid
                    }
                    ExprResult::Module(id) => MemberAccessType::Module(id),
                };

                match left {
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
                                    ((*ty).into(), i)
                                } else {
                                    errors.emit(Error::NonexistantMember, 0, 0, self.module);
                                    (TypeInfo::Invalid, 0)
                                }
                            }
                            TypeInfo::Invalid => (TypeInfo::Invalid, 0),
                            TypeInfo::Unknown => {
                                errors.emit(Error::TypeMustBeKnownHere, 0, 0, self.module);
                                (TypeInfo::Invalid, 0)
                            }
                            _ => {
                                errors.emit(Error::NonexistantMember, 0, 0, self.module);
                                (TypeInfo::Invalid, 0)
                            }
                        };
                        ir.specify(expected, ty, errors);
                        let member = ir.add(
                            Data {
                                member: (var, idx as u32),
                            },
                            Tag::Member,
                            expected,
                        );
                        return ExprResult::VarRef(member);
                    }
                    MemberAccessType::Module(id) => {
                        let module = &self.globals[id.idx()];
                        if let Some(symbol) = module.get(member) {
                            return match *symbol {
                                Symbol::Func(f) => ExprResult::Func(f),
                                Symbol::Type(t) => ExprResult::Type(t),
                                Symbol::Module(m) => ExprResult::Module(m),
                                Symbol::Var { ty: _, var } => ExprResult::VarRef(var),
                            };
                        } else {
                            errors.emit(Error::UnknownIdent, 0, 0, self.module);
                            Ref::UNDEF
                        }
                    }
                    MemberAccessType::Invalid => {
                        Ref::UNDEF
                    }
                }
            }
            ast::Expr::Cast(target, val) => {
                ir.specify(expected, TypeInfo::Primitive(*target), errors);
                let inner_ty = ir.types.add(TypeInfo::Unknown);
                let val = self.reduce_expr_val(errors, ir, val, inner_ty, ret);
                //TODO: check table for available casts
                ir.add(
                    Data {
                        cast: (val, *target),
                    },
                    Tag::Cast,
                    expected,
                )
            }
            ast::Expr::Root => {
                return ExprResult::Module(ModuleId::ROOT)
            }
        };
        ExprResult::Val(r)
    }
}
