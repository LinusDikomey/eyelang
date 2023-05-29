use crate::{
    ast::{ExprRef, self, CallId, ExprExtra, ModuleId},
    error::Error,
    token::{FloatLiteral, IntLiteral, Operator},
    types::Primitive,
    resolve::{exhaust::Exhaustion, types::ResolvedTypeDef, trait_impls},
    dmap, span::TSpan, ir::types::{TypeRefs, TypeRef},
};

use super::{
    Ctx,
    type_info::{TypeInfo, TypeInfoOrIndex},
    Ident,
    ResolvedCall,
    scope::{ExprInfo, LocalDefId, ScopeId},
    types::{DefId, TupleCountMode, Type}, MemberAccess, pat
};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum UseHint {
    Should,
    Can,
}

#[derive(Debug)]
pub enum Res {
    Val { use_hint: UseHint, lval: bool },
    Type(TypeRef),
    Module(ModuleId),
    Invalid,
}
impl Res {
    fn should_use(&self) -> UseHint {
        match self {
            Res::Val { use_hint, lval: _ } => *use_hint,
            Res::Invalid => UseHint::Can,
            _ => UseHint::Should,
        }
    }
}

pub(super) fn val_expr(expr: ExprRef, mut info: ExprInfo, mut ctx: Ctx, unused: bool) {
    match check_expr(expr, info.reborrow(), ctx.reborrow(), false) {
        Res::Val { use_hint, lval: _ } => {
            if use_hint == UseHint::Should && unused {
                ctx.errors.emit_span(Error::UnusedExpressionValue, ctx.span(expr));
            }
        }
        Res::Invalid => {
            ctx.types.invalidate(info.expected);
        }
        _ => {
            ctx.errors.emit_span(Error::ExpectedValue, ctx.span(expr));
            ctx.types.invalidate(info.expected);
        }
        /*Res::Symbol(_) | Res::Method(_) => {
            ctx.errors.emit_span(Error::ExpectedValue, self.span(expr, ctx.ast));
            ValRes { lval: false }
        }*/
    }
}

#[must_use]
pub(super) fn check_expr(expr: ExprRef, mut info: ExprInfo, mut ctx: Ctx, hole_allowed: bool) -> Res {
    ctx.symbols.expr_types[expr.idx()] = info.expected;
    let mut use_hint = UseHint::Can;
    let mut lval = false;

    match &ctx.ast[expr] {
        ast::Expr::Block { span, items, defs } => {
            let block_scope = ctx.scopes.child_with_defs(ctx.scope, &ctx.ast[*defs], ctx.ast, ctx.symbols, ctx.errors, ctx.ir);

            for item in &ctx.ast[*items] {
                let expected = ctx.types.add_unknown();
                let res = check_expr(*item, info.with_expected(expected), ctx.with_scope(block_scope), false);
                if res.should_use() == UseHint::Should {
                    ctx.errors.emit_span(Error::UnusedExpressionValue, ctx.span(*item));
                }
            }
            if !*info.noreturn {
                ctx.specify(info.expected, TypeInfo::UNIT, span.in_mod(ctx.scope().module.id));
            }
        }
        ast::Expr::Declare { pat, annotated_ty } => {
            let ty = ctx.scopes.resolve_type_info(ctx.scope, annotated_ty, ctx.types, ctx.errors, ctx.symbols, ctx.ast, ctx.ir);
            let ty = ctx.types.add_info_or_idx(ty);

            let mut exhaustion = Exhaustion::None;
            pat::pat(*pat, ty, ctx.reborrow(), &mut exhaustion);
            ctx.add_exhaustion(exhaustion, ty, ctx.ast[*pat].span(ctx.ast));
        }
        ast::Expr::DeclareWithVal { pat, annotated_ty, val } => {
            let ty = ctx.scopes.resolve_type_info(ctx.scope, annotated_ty, ctx.types, ctx.errors, ctx.symbols, ctx.ast, ctx.ir);
            let ty = ctx.types.add_info_or_idx(ty);

            val_expr(*val, info.with_expected(ty), ctx.reborrow(), false);
            
            let mut exhaustion = Exhaustion::None;
            pat::pat(*pat, ty, ctx.reborrow(), &mut exhaustion);
            ctx.add_exhaustion(exhaustion, ty, ctx.ast[*pat].span(ctx.ast));
        }
        ast::Expr::Return { val, .. } => {
            val_expr(*val, info.with_expected(info.ret), ctx, false);
            info.mark_noreturn();
        }
        ast::Expr::ReturnUnit { .. } => {
            ctx.specify(info.expected, TypeInfo::Primitive(Primitive::Unit), ctx.span(expr));
            ctx.specify(info.ret, TypeInfo::UNIT, ctx.span(expr));
            info.mark_noreturn();
        }
        ast::Expr::IntLiteral(span) => {
            let lit = IntLiteral::parse(&ctx.scopes[ctx.scope].module.src()[span.range()]);
            let ty = lit.ty.map_or(TypeInfo::Int, |ty| TypeInfo::Primitive(ty.into()));
            ctx.specify(info.expected, ty, span.in_mod(ctx.scope().module.id));
            use_hint = UseHint::Should;
        }
        ast::Expr::FloatLiteral(span) => {
            let lit = FloatLiteral::parse(&ctx.scope().module.src()[span.range()]);
            let ty = lit.ty.map_or(TypeInfo::Float, |ty| TypeInfo::Primitive(ty.into()));
            ctx.specify(info.expected, ty, span.in_mod(ctx.scope().module.id));
            use_hint = UseHint::Should;
        }
        ast::Expr::StringLiteral(span) => {
            use_hint = UseHint::Should;
            ctx.specify(info.expected, ctx.symbols.builtins.str_info(), span.in_mod(ctx.scope().module.id))
        }
        ast::Expr::BoolLiteral { .. } => {
            use_hint = UseHint::Should;
            
            ctx.specify(info.expected, TypeInfo::Primitive(Primitive::Bool), ctx.span(expr));
        }
        ast::Expr::EnumLiteral { ident, args, span: _ } => {
            use_hint = UseHint::Should;

            let name = &ctx.scope().module.src()[ident.range()];
            let arg_types = ctx.types.add_multiple_unknown(args.count);
            for (i, arg) in ctx.ast[*args].iter().enumerate() {
                val_expr(*arg, info.with_expected(arg_types.nth(i as u32)), ctx.reborrow(), false);
            }
            ctx.specify_enum_variant(info.expected, name, ctx.span(expr), arg_types)
        }
        ast::Expr::Record { .. } => todo!("record literals"),
        ast::Expr::Nested(_, inner) => return check_expr(*inner, info, ctx, hole_allowed),
        ast::Expr::Unit(_) => {
            ctx.specify(info.expected, TypeInfo::UNIT, ctx.span(expr));
        }
        ast::Expr::Variable { span, id } => {
            let name = &ctx.scope().module.src()[span.range()];
            let resolved = ctx.scopes.resolve_local(ctx.scope, name, *span, ctx.errors, ctx.symbols, ctx.ast, ctx.ir);
            let (ident, res) = match resolved {
                LocalDefId::Def(DefId::Invalid) => {
                    ctx.types.invalidate(info.expected);
                    (Ident::Invalid, Res::Invalid)
                }
                LocalDefId::Def(DefId::Global(id)) => {
                    let (_, ty, _) = ctx.symbols.get_global(id);
                    let global_ty = ty.as_info(ctx.types, |_| panic!("global type shouldn't be generic"));
                    let span = ctx.span(expr);
                    ctx.types.specify_or_merge(info.expected, global_ty, ctx.errors, span, ctx.symbols);

                    (Ident::Global(id), Res::Val { use_hint: UseHint::Should, lval: true })
                }
                LocalDefId::Def(DefId::Const(const_id)) => {
                    let ty = ctx.symbols.consts[const_id.idx()].type_info(ctx.types);
                    ctx.specify(info.expected, ty, span.in_mod(ctx.scope().module.id));
                    (Ident::Const(const_id), Res::Val { use_hint: UseHint::Should, lval: false })
                }
                LocalDefId::Def(DefId::Function(func_id)) => {
                    let generics = ctx.types.add_multiple_unknown(ctx.symbols.get_func(func_id).generic_count() as _);
                    ctx.specify(info.expected, TypeInfo::FunctionItem(func_id, generics),
                        span.in_mod(ctx.scope().module.id));
                    (Ident::Function(func_id), Res::Val { use_hint: UseHint::Should, lval: false })
                }
                LocalDefId::Def(DefId::Module(module_id)) => {
                    (Ident::Module(module_id), Res::Module(module_id))
                }
                LocalDefId::Def(DefId::Type(ty)) => {
                    ctx.specify(info.expected, TypeInfo::Type, span.in_mod(ctx.scope().module.id));
                    let generics = ctx.types.add_multiple_unknown(ctx.symbols.generic_count(ty) as _);

                    let ty = ctx.types.add(TypeInfo::Resolved(ty, generics));
                    (Ident::Type(ty), Res::Type(ty))
                }
                LocalDefId::Def(def) => {
                    todo!("support other defs {def:?} or error?")
                    //ctx.specify(info.expected, TypeInfo::SymbolItem(def), span.in_mod(ctx.scope().module.id));
                    //todo!("Definition of {def:?} as expression is not yet implemented");
                    //Ident::Invalid
                    
                }
                LocalDefId::Var(var) => {
                    let ty = ctx.var(var).ty;
                    ctx.merge(info.expected, ty, span.in_mod(ctx.scope().module.id));
                    (Ident::Var(var), Res::Val { use_hint: UseHint::Should, lval: true })
                }
                LocalDefId::Type(idx) => {
                    ctx.specify(info.expected, TypeInfo::Type, span.in_mod(ctx.scope().module.id));
                    (Ident::Type(idx), Res::Type(idx))
                }
            };
            ctx.set_ident(*id, ident);
            return res;
        }
        ast::Expr::Hole(_) => if !hole_allowed {
            lval = true;

            ctx.errors.emit_span(Error::HoleLHSOnly, ctx.span(expr));
        }
        ast::Expr::Array(span, elems) => {
            use_hint = UseHint::Should;

            let elems = &ctx.ast[*elems];
            let elem_ty = ctx.types.add_unknown();
            let arr_ty = TypeInfo::Array(Some(elems.len() as u32), elem_ty);
            ctx.specify(info.expected, arr_ty, span.in_mod(ctx.scope().module.id));
            
            for elem in elems.iter() {
                val_expr(*elem, info.with_expected(elem_ty), ctx.reborrow(), false);
            }
        }
        ast::Expr::Tuple(span, elems) => {
            let elem_types = ctx.types.add_multiple_unknown(elems.count);
            let tuple_ty = TypeInfo::Tuple(elem_types, TupleCountMode::Exact);
            ctx.specify(info.expected, tuple_ty, span.in_mod(ctx.scope().module.id));

            for (elem, elem_ty) in ctx.ast[*elems].iter().zip(elem_types.iter()) {
                val_expr(*elem, info.with_expected(elem_ty), ctx.reborrow(), false);
            }
        }
        &ast::Expr::If { cond, then, .. } => {
            ctx.specify(info.expected, TypeInfo::UNIT, ctx.span(expr));

            let bool_ty = ctx.types.add(TypeInfo::Primitive(Primitive::Bool));
            val_expr(cond, info.with_expected(bool_ty), ctx.reborrow(), false);
            
            let then_ty = ctx.types.add_unknown();
            let mut then_noreturn = *info.noreturn;
            val_expr(then, info.with_expected(then_ty).with_noreturn(&mut then_noreturn), ctx, true);
        }
        &ast::Expr::IfPat { pat, value, then, .. } => {
            ctx.specify(info.expected, TypeInfo::UNIT, ctx.span(expr));

            let value_ty = ctx.types.add(TypeInfo::Unknown);
            val_expr(value, info.with_expected(value_ty), ctx.reborrow(), false); 
            let mut exhaustion = Exhaustion::None;
            pat::pat(pat, value_ty, ctx.reborrow(), &mut exhaustion);
            // TODO: warn on full/empty exhaustion
            
            let then_ty = ctx.types.add_unknown();
            let mut then_noreturn = *info.noreturn;
            val_expr(then, info.with_expected(then_ty).with_noreturn(&mut then_noreturn), ctx, true);
        }
        ast::Expr::IfElse { cond, then, else_, .. } => {
            let bool_ty = ctx.types.add(TypeInfo::Primitive(Primitive::Bool));
            val_expr(*cond, info.with_expected(bool_ty), ctx.reborrow(), false);

            let mut then_noreturn = false;
            let mut else_noreturn = false;
            // TODO: setting unused to false can be incorrect if the if-else is unused
            val_expr(*then, info.with_noreturn(&mut then_noreturn), ctx.reborrow(), false);
            val_expr(*else_, info.with_noreturn(&mut else_noreturn), ctx, false);
            if then_noreturn && else_noreturn {
                info.mark_noreturn();
            }
        }
        &ast::Expr::IfPatElse { pat, value, then, else_, .. } => {
            let value_ty = ctx.types.add(TypeInfo::Unknown);
            val_expr(value, info.with_expected(value_ty), ctx.reborrow(), false); 
            let mut exhaustion = Exhaustion::None;
            pat::pat(pat, value_ty, ctx.reborrow(), &mut exhaustion);
            // TODO: warn on full/empty exhaustion
            
            let mut then_noreturn = false;
            let mut else_noreturn = false;
            val_expr(then, info.with_noreturn(&mut then_noreturn), ctx.reborrow(), false);
            val_expr(else_, info.with_noreturn(&mut else_noreturn), ctx, false);
            if then_noreturn && else_noreturn {
                info.mark_noreturn();
            }
        }
        ast::Expr::Match { span: _, val, extra_branches, branch_count } => {
            let matched_ty = ctx.types.add_unknown();
            val_expr(*val, info.with_expected(matched_ty), ctx.reborrow(), false);
            let extra = &ctx.ast[ExprExtra { idx: *extra_branches, count: *branch_count * 2 }];
            let mut all_noreturn = true;
            let mut exhaustion = Exhaustion::None;
            for [pat, branch] in extra.array_chunks() {
                let branch_scope = ctx.scopes.child(ctx.scope, dmap::new(), dmap::new(), true);
                let mut ctx = ctx.with_scope(branch_scope);
                
                pat::pat(*pat, matched_ty, ctx.reborrow(), &mut exhaustion);

                let mut branch_noreturn = false;
                val_expr(*branch, info.with_noreturn(&mut branch_noreturn), ctx, false);
                all_noreturn &= branch_noreturn;
            }
            ctx.add_exhaustion(exhaustion, matched_ty, ctx.ast[*val].span(ctx.ast));
            if all_noreturn {
                info.mark_noreturn();
            }
        }
        ast::Expr::While { start: _, cond, body } => {
            ctx.specify(info.expected, TypeInfo::UNIT, ctx.span(expr));

            let bool_ty = ctx.types.add(TypeInfo::Primitive(Primitive::Bool));
            val_expr(*cond, info.with_expected(bool_ty), ctx.reborrow(), false);

            let body_ty = ctx.types.add_unknown();
            let mut body_noreturn = false;
            val_expr(*body, info.with_expected(body_ty).with_noreturn(&mut body_noreturn), ctx, true);
        }
        &ast::Expr::WhilePat { start: _, pat, val, body } => {
            ctx.specify(info.expected, TypeInfo::UNIT, ctx.span(expr));

            let val_ty = ctx.types.add(TypeInfo::Unknown);
            val_expr(val, info.with_expected(val_ty), ctx.reborrow(), false);
            let mut exhaustion = Exhaustion::None;
            pat::pat(pat, val_ty, ctx.reborrow(), &mut exhaustion);

            // TODO: we probably want to emit a warning if the pattern is fully exhausted.
            
            let body_ty = ctx.types.add_unknown();
            let mut body_noreturn = false;
            val_expr(body, info.with_expected(body_ty).with_noreturn(&mut body_noreturn), ctx, true);
        }
        ast::Expr::FunctionCall(call_id) => {
            return call(*call_id, expr, info, ctx);
        }
        ast::Expr::UnOp(_, op, val) => {
            use_hint = UseHint::Should;
            match op {
                ast::UnOp::Neg => {
                    // TODO: type check negation properly (number TypeInfo or traits)
                    val_expr(*val, info, ctx, false);
                }
                ast::UnOp::Not => {
                    ctx.specify(info.expected, TypeInfo::Primitive(Primitive::Bool), ctx.span(expr));
                    val_expr(*val, info, ctx, false);
                }
                ast::UnOp::Ref => {
                    let pointee_ty = ctx.types.add_unknown();
                    let ptr_ty = TypeInfo::Pointer(pointee_ty);
                    ctx.specify(info.expected, ptr_ty, ctx.span(*val));
                    val_expr(*val, info.with_expected(pointee_ty), ctx, false);
                }
                ast::UnOp::Deref => {
                    lval = true;

                    let ptr_ty = ctx.types.add(TypeInfo::Pointer(info.expected));
                    val_expr(*val, info.with_expected(ptr_ty), ctx, false);
                }
            }
        }
        &ast::Expr::BinOp(op, l, r) => {
            if let Operator::Assignment(_assign) = op {
                ctx.specify(info.expected, TypeInfo::UNIT, ctx.span(expr));
                let var_ty = ctx.types.add_unknown();
                val_expr(r, info.with_expected(var_ty), ctx.reborrow(), false);

                // TODO: handle lvals properly
                let lval = check_expr(l, info.with_expected(var_ty), ctx.reborrow(), true);
                match lval {
                    Res::Val { use_hint: _, lval: false } | Res::Module(_) | Res::Type(_) => {
                        ctx.errors.emit_span(Error::CantAssignTo, ctx.span(l));
                    }
                    Res::Val { use_hint: _, lval: true } | Res::Invalid => {}
                }
                // TODO: type checking for all assign variants like AddAssign (same with BinOp)
            } else {
                use_hint = UseHint::Should;

                let inner_ty = if op.is_boolean() {
                    ctx.types.add(TypeInfo::Primitive(Primitive::Bool))
                } else if op.is_logical() {
                    ctx.types.add(TypeInfo::Unknown)
                } else {
                    info.expected
                };
                val_expr(l, info.with_expected(inner_ty), ctx.reborrow(), false);
                val_expr(r, info.with_expected(inner_ty), ctx, false);
                if op == Operator::Range || op == Operator::RangeExclusive {
                    todo!("range operators only implemented in patterns for now")
                }
            }
        }
        &ast::Expr::MemberAccess { left, name: name_span, id } => {
            let name = &ctx.ast.src(ctx.scope().module.id).0[name_span.range()];
            use_hint = UseHint::Should;
            lval = true;
            let left_ty = ctx.types.add_unknown();
            let (member_access, ty) = match check_expr(left, info.with_expected(left_ty), ctx.reborrow(), false) {
                Res::Val { use_hint: _, lval: _ } => {
                    val_member_access(ctx.reborrow(), expr, left, left_ty, name)
                }
                Res::Type(ty) => type_member_access(ctx.reborrow(), expr, ty, name, name_span),
                Res::Module(module_id) => {
                    let def = ctx.scopes.resolve(
                        ScopeId::module(module_id),
                        name,
                        name_span.in_mod(ctx.scope().module.id),
                        ctx.errors,
                        ctx.symbols,
                        ctx.ast,
                        ctx.ir
                    );
                    match def {
                        DefId::Type(id) => {
                            ctx.symbols.member_accesses[id.idx()] = MemberAccess::Symbol(def);
                            ctx.specify(info.expected, TypeInfo::Type, ctx.span(expr));
                            let generics = ctx.types.add_multiple_unknown(ctx.symbols.generic_count(id) as _);

                            let ty = ctx.types.add(TypeInfo::Resolved(id, generics));
                            return Res::Type(ty);
                        }
                        DefId::Function(id) => {
                            let generic_count = ctx.symbols.get_func(id).generic_count() as _;
                            let generics = ctx.types.add_multiple_unknown(generic_count);
                            (
                                MemberAccess::Symbol(def),
                                TypeInfo::FunctionItem(id, generics).into()
                            )
                        }
                        DefId::Module(module_id) => {
                            ctx.symbols.member_accesses[id.idx()] = MemberAccess::Symbol(def);
                            return Res::Module(module_id);
                        }
                        DefId::Global(global_id) => (
                            MemberAccess::Symbol(def),
                            ctx.symbols.get_global(global_id).1.as_info(ctx.types, |_| unreachable!("generic global?"))
                        ),
                        DefId::Invalid => (MemberAccess::Invalid, TypeInfo::Invalid.into()),
                        _ => (MemberAccess::Symbol(def), TypeInfo::Unknown.into())
                    }
                }
                Res::Invalid => (MemberAccess::Invalid, TypeInfo::Invalid.into())
            };
            ctx.symbols.member_accesses[id.idx()] = member_access;
            ctx.types.specify_or_merge(info.expected, ty, ctx.errors, ctx.span(expr), ctx.symbols);
        }
        &ast::Expr::Index { expr, idx, .. } => {
            lval = true;
            
            let arr_ty = ctx.types.add(TypeInfo::Array(None, info.expected));
            val_expr(expr, info.with_expected(arr_ty), ctx.reborrow(), false);

            let idx_ty = ctx.types.add(TypeInfo::Int);
            val_expr(idx, info.with_expected(idx_ty), ctx, false);
        }
        &ast::Expr::TupleIdx { expr, idx, .. } => {
            lval = true;

            let elem_types = ctx.types.add_multiple_info_or_index(
                (0..idx).map(|_| TypeInfoOrIndex::Type(TypeInfo::Unknown))
                .chain(std::iter::once(TypeInfoOrIndex::Idx(info.expected)))
            );

            let tuple_ty = ctx.types.add(TypeInfo::Tuple(elem_types, TupleCountMode::AtLeast));
            val_expr(expr, info.with_expected(tuple_ty), ctx, false);
        }
        ast::Expr::Cast(span, ty, val) => {
            // TODO: check casts properly, maybe defer check to end of function
            let val_ty = ctx.types.add_unknown();
            val_expr(*val, info.with_expected(val_ty), ctx.reborrow(), false);
            let cast_info = ctx.scopes.resolve_type_info(ctx.scope, ty, ctx.types, ctx.errors, ctx.symbols, ctx.ast, ctx.ir);
            ctx.types.specify_or_merge(
                info.expected, cast_info,
                ctx.errors, span.in_mod(ctx.scope().module.id), &ctx.symbols
            );
        }
        ast::Expr::Root(_) => {
            ctx.types.invalidate(info.expected);
            return Res::Module(ctx.scope().module.root)
        }
        ast::Expr::Asm { .. } => todo!("inline asm is unsupported right now"),
    };
    Res::Val { use_hint, lval }
}

fn val_member_access(ctx: Ctx, expr: ExprRef, left: ExprRef, left_ty: TypeRef, name: &str)
-> (MemberAccess, TypeInfoOrIndex)
{
    // auto deref
    let mut deref_ty = ctx.types.get(left_ty);
    loop {
        deref_ty = match deref_ty {
            TypeInfo::Pointer(inner) => ctx.types.get(inner),
            TypeInfo::Resolved(id, generics) => match ctx.symbols.get_type(id) {
                ResolvedTypeDef::Struct(s) => {
                    let member = s.members
                        .iter()
                        .enumerate()
                        .find(|(_, (member_name, _))| member_name == name);
                    if let Some((i, (_, ty))) = member {
                        let ty = ty.as_info(ctx.types, |i| generics.nth(i as u32).into());
                        break (MemberAccess::StructMember(i as _), ty);
                    } else if let Some(&id) = s.methods.get(name) {
                        let func_generic_count = ctx.symbols.get_func(id).generic_count() as usize;
                        let generics = if generics.len() == func_generic_count {
                            generics
                        } else {
                            debug_assert!(func_generic_count > generics.len());
                            ctx.types.add_multiple_info_or_index(generics
                                .iter()
                                .map(TypeInfoOrIndex::Idx)
                                .chain(
                                    std::iter::repeat(TypeInfo::Unknown.into())
                                        .take(func_generic_count - generics.len())
                                )
                            )
                        };
                        let ty = TypeInfo::MethodItem { function: id, generics, this_ty: left_ty };
                        break (MemberAccess::Method(id), ty.into());
                    } else {
                        ctx.errors.emit_span(Error::NonexistantMember, ctx.span(expr));
                        break (MemberAccess::Invalid, TypeInfo::Invalid.into());
                    }
                }
                ResolvedTypeDef::Enum(_) => {
                    ctx.errors.emit_span(Error::NonexistantMember, ctx.span(expr));
                    break (MemberAccess::Invalid, TypeInfo::Invalid.into());
                }
            }
            TypeInfo::Unknown => {
                ctx.errors.emit_span(Error::TypeMustBeKnownHere, ctx.span(left));
                break (MemberAccess::Invalid, TypeInfo::Invalid.into());
            }
            TypeInfo::Invalid => {
                break (MemberAccess::Invalid, TypeInfo::Invalid.into());
            }
            TypeInfo::Generic(_) => todo!("generic member checking (traits?)"),
            TypeInfo::FunctionItem(_, _) | TypeInfo::MethodItem { .. }
            | TypeInfo::Type
            | TypeInfo::Int | TypeInfo::Float | TypeInfo::Primitive(_)
            | TypeInfo::Array(_, _) | TypeInfo::Tuple(_, _) | TypeInfo::Enum(_) => {
                ctx.errors.emit_span(Error::NonexistantMember, ctx.span(expr));
                break (MemberAccess::Invalid, TypeInfo::Invalid.into());
            }
        }
    }
}

fn type_member_access(ctx: Ctx, expr: ExprRef, ty: TypeRef, name: &str, name_span: TSpan)
-> (MemberAccess, TypeInfoOrIndex)
{
    const U64: TypeInfoOrIndex = TypeInfoOrIndex::Type(TypeInfo::Primitive(Primitive::U64));
    let generic_ty = match name {
        "size"   => return (MemberAccess::LocalSize  (ty), U64),
        "align"  => return (MemberAccess::LocalAlign (ty), U64),
        "stride" => return (MemberAccess::LocalStride(ty), U64),
        _ => match ctx.types.get(ty) {
            TypeInfo::Resolved(id, generics) => {
                match ctx.symbols.get_type(id) {
                    ResolvedTypeDef::Struct(def) => if let Some(&method) = def.methods.get(name) {
                        let func_generic_count = ctx.symbols.get_func(method).generic_count();
                        let generics = if func_generic_count as u32 > generics.count {
                            ctx.types.add_multiple_info_or_index(generics
                                .iter()
                                .map(TypeInfoOrIndex::Idx)
                                .chain(
                                    std::iter::repeat(TypeInfoOrIndex::Type(TypeInfo::Unknown))
                                        .take(func_generic_count as usize - generics.count as usize)
                                )
                            )
                        } else {
                            debug_assert_eq!(func_generic_count as u32, generics.count);
                            generics
                        };
                        return (
                            MemberAccess::Symbol(DefId::Function(method)),
                            TypeInfo::FunctionItem(method, generics).into()
                        );
                    }
                    ResolvedTypeDef::Enum(def) => if let Some(variant) = def.variants.get(name) {
                        return (
                            MemberAccess::EnumItem(id, variant.1),
                            TypeInfo::Resolved(id, generics).into(),
                        )
                    }
                }
                Some(trait_impls::GenericType::Id(id))
            }
            TypeInfo::Primitive(p) => Some(trait_impls::GenericType::Primitive(p)),
            _ => None
        }
    };

    // qualifies for trait resolval
    if let Some(generic_ty) = generic_ty {
        match ctx.symbols.trait_impls.from_type(&ctx.symbols, generic_ty, name) {
            trait_impls::TraitMethodResult::Found { func, impl_generic_count } => {
                // TODO: generics
                return (
                    MemberAccess::Symbol(DefId::Function(func)),
                    TypeInfo::FunctionItem(func, TypeRefs::EMPTY).into(),
                );
            }
            trait_impls::TraitMethodResult::None => {}
            trait_impls::TraitMethodResult::Multiple => todo!("handle multiple trait candidates")
        }
    }

    ctx.errors.emit_span(
        Error::NonexistantMember,
        name_span.in_mod(ctx.scope().module.id)
        );
    (MemberAccess::Invalid, TypeInfo::Invalid.into())
}

fn call(id: CallId, call_expr: ExprRef, mut info: ExprInfo, mut ctx: Ctx) -> Res {
    
    let call = &ctx.ast[id];
    let called_ty = ctx.types.add_unknown();

    match check_expr(call.called_expr, info.with_expected(called_ty), ctx.reborrow(), false) {
        Res::Val { .. } => {}
        Res::Type(called_type) => {
            match ctx.types.get(called_type) {
                TypeInfo::Resolved(type_id, generics) => {
                    let resolved_call = call_type_id(ctx.reborrow(), type_id, generics, call, call_expr, info);
                    ctx.symbols.place_call(id, resolved_call);
                    return Res::Val { use_hint: UseHint::Can, lval: false };
                }
                _ => {
                    ctx.errors.emit_span(
                        Error::FunctionOrTypeExpected,
                        ctx.ast[call.called_expr].span_in(&ctx.ast, ctx.scope().module.id)
                    );
                    return Res::Invalid
                }
            }
        }
        Res::Module(_) => {
            ctx.errors.emit_span(
                Error::FunctionOrTypeExpected,
                ctx.ast[call.called_expr].span_in(&ctx.ast, ctx.scope().module.id)
            );
            return Res::Invalid
        }
        Res::Invalid => return Res::Invalid
    }
    
    let (res, call) = match ctx.types.get(called_ty) {
        TypeInfo::FunctionItem(func_id, generics) => {
            let resolved_call = call_func(func_id, generics, ctx.reborrow(), None, call, call_expr, info);
            (Res::Val { use_hint: UseHint::Can, lval: false }, resolved_call)
        }
        TypeInfo::MethodItem { function: id, generics, this_ty } => {
            let this = Some((this_ty, ctx.ast[call.called_expr].span(ctx.ast)));
            let call = call_func(id, generics, ctx.reborrow(), this, call, call_expr, info);
            (Res::Val { use_hint: UseHint::Can, lval: false }, call)
        }
        _ => {
            if ctx.types.invalidate(called_ty) {
                ctx.errors.emit_span(
                    Error::FunctionOrStructTypeExpected,
                    ctx.ast[call.called_expr].span_in(&ctx.ast, ctx.scope().module.id)
                );
            }
            (Res::Invalid, ResolvedCall::Invalid)
        }
    };
    ctx.symbols.place_call(id, call);
    res
}

fn call_func(
    func_id: ast::FunctionId,
    generics: TypeRefs,
    mut ctx: Ctx,
    this: Option<(TypeRef, TSpan)>,
    call: &ast::Call,
    call_expr: ExprRef,
    mut info: ExprInfo
)
-> ResolvedCall {
    let sig = ctx.symbols.get_func(func_id);

    let on_generic = |i| TypeInfoOrIndex::Idx(generics.nth(i as u32));

    let arg_count = call.args.count + this.is_some() as u32;

    match sig.params.len().cmp(&(arg_count as usize)) {
        std::cmp::Ordering::Less if sig.varargs => {}
        std::cmp::Ordering::Equal => {}
        _ => {
            ctx.errors.emit_span(Error::InvalidArgCount {
                expected: sig.params.len() as _,
                varargs: sig.varargs,
                found: arg_count,
            }, ctx.span(call_expr));
        }
    }

    let ret = sig.return_type.as_info(ctx.types, on_generic);
    if sig.return_type == Type::Prim(Primitive::Never) {
        info.mark_noreturn();
    }
    
    let call_span = ctx.span(call_expr);
    ctx.types.specify_or_merge(info.expected, ret, ctx.errors, call_span, &ctx.symbols);
    
    let params = sig.params
        .iter()
        .map(|(_, ty)| {
            let ty = ty.as_info(ctx.types, on_generic);
            ctx.types.add_info_or_idx(ty)
        })
        .collect::<Vec<_>>();

    let mut params = params.into_iter();

    if let Some((this, this_span)) = this {
        let this_param = params.next().unwrap_or_else(|| ctx.types.add_unknown());
        ctx.types.merge_dereffed(this, this_param, ctx.errors, this_span.in_mod(ctx.scope().module.id), ctx.symbols);
    }

    for arg in &ctx.ast[call.args] {
        let param_ty = params.next().unwrap_or_else(|| ctx.types.add_unknown());
        val_expr(*arg, info.with_expected(param_ty), ctx.reborrow(), false);
    }
    ResolvedCall::Function { func_id, generics }
}

fn call_type_id(
    mut ctx: Ctx, id: ast::TypeId, generics: TypeRefs, call: &ast::Call, call_expr: ExprRef, mut info: ExprInfo
) -> ResolvedCall {
    match ctx.symbols.get_type(id) {
        ResolvedTypeDef::Struct(def) => {
            if call.args.count as usize != def.members.len() {
                ctx.errors.emit_span(
                    Error::InvalidArgCount {
                        expected: def.members.len() as _,
                        varargs: false,
                        found: call.args.count,
                    },
                    ctx.span(call_expr)
                );
            }
            
            let arg_types = ctx.types.add_multiple_unknown(def.members.len() as _);
            for (i, (_, ty)) in def.members.iter().enumerate() {
                let param_ty = ty.as_info(ctx.types, |i| generics.nth(i as u32).into());
                ctx.types.replace_idx(arg_types.nth(i as u32), param_ty);
                
            }
            for (arg, ty) in ctx.ast[call.args].iter().zip(arg_types.iter()) {
                val_expr(*arg, info.with_expected(ty), ctx.reborrow(), false);
            }

            ctx.specify(info.expected, TypeInfo::Resolved(id, generics), ctx.span(call_expr));
            
            ResolvedCall::Struct { type_id: id, generics }
        }
        ResolvedTypeDef::Enum(_) => {
            ctx.errors.emit_span(
                Error::FunctionOrStructTypeExpected,
                ctx.ast[call.called_expr].span_in(&ctx.ast, ctx.scope().module.id),
            );
            ResolvedCall::Invalid
        }
    } 
}

