mod cast;
mod exhaust;
pub mod expr;

use dmap::DHashMap;
use id::ModuleId;
use span::TSpan;
use types::{Primitive, Type};

use crate::{
    Compiler,
    parser::{ast::{Ast, ExprId, Expr, UnOp}, token::{IntLiteral, Operator}},
    compiler::{LocalScope, LocalItem, Def, VarId, Signature},
    type_table::{TypeInfo, LocalTypeId, TypeTable},
    hir::{HIRBuilder, Node, Pattern, HIR, CastId, LValue}, error::{Error, CompileError},
};

use self::exhaust::Exhaustion;

pub struct Ctx<'a> {
    pub compiler: &'a mut Compiler,
    pub ast: &'a Ast,
    pub module: ModuleId,
    pub hir: HIRBuilder,
    /// Exhaustion value, type, pattern expr
    pub deferred_exhaustions: Vec<(Exhaustion, LocalTypeId, ExprId)>,
    /// from, to, cast_expr
    pub deferred_casts: Vec<(LocalTypeId, LocalTypeId, ExprId, CastId)>,
}
impl<'a> Ctx<'a> {
    fn span(&self, expr: ExprId) -> span::Span {
        self.ast[expr].span_in(self.ast, self.module)
    }

    fn specify(&mut self, ty: LocalTypeId, info: impl Into<TypeInfo>, span: impl FnOnce(&Ast) -> TSpan) {
        self.hir.types.specify(
            ty,
            info.into(),
            &mut self.compiler.errors,
            || span(self.ast).in_mod(self.module),
        )
    }

    fn unify(&mut self, a: LocalTypeId, b: LocalTypeId, span: impl FnOnce(&Ast) -> TSpan) {
        self.hir.types.unify(a, b, &mut self.compiler.errors, || span(self.ast).in_mod(self.module))
    }

    fn invalidate(&mut self, ty: LocalTypeId) {
        self.hir.types.invalidate(ty);
    }

    pub(crate) fn finish(self, root: Node) -> (HIR, TypeTable) {
        // TODO: finalize types?
        let (mut hir, types) = self.hir.finish(root);
        for (exhaustion, ty, pat) in self.deferred_exhaustions {
            if let Some(false) = exhaustion.is_exhausted(types[ty], &types, self.compiler) {
                let error = Error::Inexhaustive.at_span(self.ast[pat].span_in(&self.ast, self.module));
                self.compiler.errors.emit_err(error)
            }
        }
        for (from_ty, to_ty, cast_expr, cast_id) in self.deferred_casts {
            let res = cast::check(from_ty, to_ty, &types,
                || self.ast[cast_expr].span_in(self.ast, self.module));
            match res {
                Result::Ok(cast_ty) => hir[cast_id].cast_ty = cast_ty,
                Result::Err(Some(err)) => {
                    // cast_ty of this cast should be set to invalid by default, we are just
                    // leaving it that way
                    self.compiler.errors.emit_err(err);
                }
                Result::Err(None) => {}
            }
        }
        (hir, types)
    }
}

pub fn check_lval(
    ctx: &mut Ctx,
    expr: ExprId,
    scope: &mut LocalScope,
) -> (LValue, LocalTypeId) {
    match &ctx.ast[expr] {
        &Expr::Ident { span } => {
            match scope.resolve(&ctx.ast.src()[span.range()], span, ctx.compiler) {
                LocalItem::Invalid | LocalItem::Def(Def::Invalid) => (
                    LValue::Invalid,
                    ctx.hir.types.add(TypeInfo::Invalid),
                ),
                LocalItem::Var(id) => {
                    let var_ty = ctx.hir.get_var(id);
                    (LValue::Variable(id), var_ty)
                }
                LocalItem::Def(Def::Global(module, id)) => {
                    let global_ty = &ctx.compiler.get_checked_global(module, id).0;
                    let ty = ctx.hir.types.info_from_resolved(global_ty);
                    let ty = ctx.hir.types.add(ty);
                    (LValue::Global(module, id), ty)
                }
                LocalItem::Def(_) => {
                    ctx.compiler.errors.emit_err(Error::CantAssignTo.at_span(ctx.span(expr)));
                    (
                        LValue::Invalid,
                        ctx.hir.types.add(TypeInfo::Invalid),
                    )
                }
            }
        }
        Expr::UnOp(_, UnOp::Deref, _) => todo!("assign to derefs"),
        Expr::MemberAccess { .. } => todo!("struct member assignment"),
        _ => {
            ctx.compiler.errors.emit_err(Error::CantAssignTo.at_span(ctx.span(expr)));
            (
                LValue::Invalid,
                ctx.hir.types.add(TypeInfo::Invalid),
            )
        }
    }
}

pub fn check_pat(
    ctx: &mut Ctx,
    variables: &mut DHashMap<String, VarId>,
    exhaustion: &mut Exhaustion,
    pat: ExprId,
    expected: LocalTypeId,
) -> Pattern {
    match &ctx.ast[pat] {
        Expr::Ident { span, .. } => {
            let var = ctx.hir.add_var(expected);
            let name = ctx.ast.src()[span.range()].to_owned();
            variables.insert(name, var);
            exhaustion.exhaust_full();
            Pattern::Variable(var)
        }
        Expr::Hole(_) => {
            exhaustion.exhaust_full();
            Pattern::Ignore
        }
        &Expr::BinOp(op @ (Operator::Range | Operator::RangeExclusive), l, r) => {
            enum Kind {
                Int(exhaust::SignedInt),
                Float,
                Invalid,
            }
            let mut range_side = |expr_ref: ExprId| {
                let expr = &ctx.ast[expr_ref];
                match *expr {
                    Expr::IntLiteral(l) => {
                        let lit = IntLiteral::parse(&ctx.ast.src()[l.range()]);
                        ctx.specify(expected, TypeInfo::Integer, |ast| ast[expr_ref].span(ast));
                        Kind::Int(exhaust::SignedInt(lit.val, false))
                    }
                    Expr::FloatLiteral(_) => {
                        ctx.specify(expected, TypeInfo::Float, |ast| ast[expr_ref].span(ast));
                        Kind::Float
                    }
                    Expr::UnOp(_, UnOp::Neg, inner) => match ctx.ast[inner] {
                        Expr::IntLiteral(l) => {
                            let lit = IntLiteral::parse(&ctx.ast.src()[l.range()]);
                            ctx.specify(expected, TypeInfo::Integer, |ast| ast[expr_ref].span(ast));
                            Kind::Int(exhaust::SignedInt(lit.val, true))
                        }
                        Expr::FloatLiteral(_) => {
                            ctx.specify(expected, TypeInfo::Float, |ast| ast[expr_ref].span(ast));
                            Kind::Float
                        }
                        _ => {
                            ctx.compiler.errors.emit_span(Error::NotAPatternRangeValue, ctx.span(expr_ref));
                            ctx.invalidate(expected);
                            Kind::Invalid
                        }
                    }
                    _ => {
                        ctx.compiler.errors.emit_span(Error::NotAPatternRangeValue, ctx.span(expr_ref));
                        ctx.invalidate(expected);
                        Kind::Invalid
                    }
                }
            };
            if let (Kind::Int(l), Kind::Int(r)) = (range_side(l), range_side(r)) {
                exhaustion.exhaust_int_range(l, r);
                let inclusive = op == Operator::Range;
                Pattern::Range { min_max: (l.0, r.0), min_max_signs: (l.1, r.1), inclusive }
            } else {
                ctx.compiler.errors.emit_err(
                    Error::NotAPattern { coming_soon: false }.at_span(ctx.span(pat))
                );
                Pattern::Invalid
            }
        }
        /*
        &Expr::Tuple(span, members) => {
            let member_types = ctx.hir.types.add_multiple_unknown(members.count);
            ctx.specify(expected, TypeInfo::Tuple(member_types, TupleCountMode::Exact), span.in_mod(ctx.scope().module.id));
            let do_exhaust_checks = match exhaustion {
                Exhaustion::Full | Exhaustion::Invalid => true,
                Exhaustion::None => {
                    *exhaustion = Exhaustion::Tuple(vec![Exhaustion::None; members.count as usize]);
                    true
                }
                Exhaustion::Tuple(_) => true,
                _ => {
                    *exhaustion = Exhaustion::Invalid;
                    false
                }
            };
            for (i, (&item_pat, ty)) in ctx.ast[members].iter().zip(member_types.iter()).enumerate() {
                if do_exhaust_checks {
                    let Exhaustion::Tuple(members) = exhaustion else { unreachable!() };
                    pat(item_pat, ty, ctx.reborrow(), &mut members[i]);
                } else {
                    pat(item_pat, ty, ctx.reborrow(), &mut Exhaustion::Full);
                };
            }
        }
        */
        _ => {
            ctx.compiler.errors.emit_err(
                Error::NotAPattern { coming_soon: false }.at_span(ctx.span(pat))
            );
            Pattern::Invalid
        }
    }
}

pub fn verify_main_signature(
    signature: &Signature,
    main_module: ModuleId,
) -> Result<(), Option<CompileError>> {
    if signature.args.len() != 0 || signature.varargs {
        return Err(Some(Error::MainArgs.at_span(signature.span.in_mod(main_module))));
    }
    if !signature.generics.is_empty() {
        return Err(Some(Error::MainGenerics.at_span(signature.span.in_mod(main_module))));
    }
    match &signature.return_type {
        Type::Invalid => return Err(None),
        Type::Primitive(p) if p.is_int() | matches!(p, Primitive::Unit) => Ok(()),
        ty => return Err(Some(
            Error::InvalidMainReturnType(ty.to_string())
                .at_span(signature.span.in_mod(main_module))
        )),
    }
}
