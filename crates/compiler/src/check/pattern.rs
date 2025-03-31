use dmap::DHashMap;

use crate::{
    check::exhaust,
    compiler::{VarId, builtins},
    error::Error,
    hir::Pattern,
    parser::{
        ast::{Expr, ExprId, UnOp},
        token::{IntLiteral, Operator},
    },
    types::{LocalTypeId, LocalTypeIds, TypeInfo},
};

use super::{Ctx, exhaust::Exhaustion};

pub fn check(
    ctx: &mut Ctx,
    variables: &mut DHashMap<Box<str>, VarId>,
    exhaustion: &mut Exhaustion,
    pat: ExprId,
    expected: LocalTypeId,
) -> Pattern {
    match &ctx.ast[pat] {
        &Expr::Nested(_, inner) => check(ctx, variables, exhaustion, inner, expected),
        Expr::IntLiteral(span) => {
            let lit = IntLiteral::parse(&ctx.ast.src()[span.range()]);
            let ty = lit
                .ty
                .map_or(TypeInfo::Integer, |ty| TypeInfo::Primitive(ty.into()));
            ctx.specify(expected, ty, |ast| ast[pat].span(ast));
            exhaustion.exhaust_int(exhaust::SignedInt(lit.val, false));
            Pattern::Int(false, lit.val, expected)
        }
        &Expr::StringLiteral(span) => {
            let str = super::get_string_literal(ctx.ast.src(), span);
            let str_type = builtins::get_str(ctx.compiler);
            ctx.specify(
                expected,
                TypeInfo::TypeDef(str_type, LocalTypeIds::EMPTY),
                |_| span,
            );
            Pattern::String(str)
        }
        &Expr::UnOp(_, UnOp::Neg, inner) => {
            match ctx.ast[inner] {
                Expr::IntLiteral(span) => {
                    let lit = IntLiteral::parse(&ctx.ast.src()[span.range()]);
                    let ty = lit
                        .ty
                        .map_or(TypeInfo::Integer, |ty| TypeInfo::Primitive(ty.into()));
                    // TODO: constrain negation with traits when they are available
                    ctx.specify(expected, ty, |ast| ast[pat].span(ast));
                    exhaustion.exhaust_int(exhaust::SignedInt(lit.val, true));
                    Pattern::Int(true, lit.val, expected)
                }
                Expr::FloatLiteral(_) => todo!("negative float patterns"),
                _ => {
                    ctx.compiler
                        .errors
                        .emit_err(Error::NotAPattern { coming_soon: false }.at_span(ctx.span(pat)));
                    Pattern::Invalid
                }
            }
        }
        Expr::Ident { span, .. } => {
            let var = ctx.hir.add_var(expected);
            let name = ctx.ast.src()[span.range()].into();
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
                            ctx.compiler
                                .errors
                                .emit_span(Error::NotAPatternRangeValue, ctx.span(expr_ref));
                            ctx.invalidate(expected);
                            Kind::Invalid
                        }
                    },
                    _ => {
                        ctx.compiler
                            .errors
                            .emit_span(Error::NotAPatternRangeValue, ctx.span(expr_ref));
                        ctx.invalidate(expected);
                        Kind::Invalid
                    }
                }
            };
            if let (Kind::Int(l), Kind::Int(r)) = (range_side(l), range_side(r)) {
                exhaustion.exhaust_int_range(l, r);
                let inclusive = op == Operator::Range;
                Pattern::Range {
                    min_max: (l.0, r.0),
                    ty: expected,
                    min_max_signs: (l.1, r.1),
                    inclusive,
                }
            } else {
                ctx.compiler
                    .errors
                    .emit_err(Error::NotAPattern { coming_soon: false }.at_span(ctx.span(pat)));
                Pattern::Invalid
            }
        }
        &Expr::EnumLiteral { span, ident, args } => {
            let name = &ctx.ast[ident];
            let res = ctx
                .hir
                .types
                .specify_enum_literal(expected, name, args.count, ctx.compiler);
            match res {
                Ok((ordinal, arg_types)) => {
                    debug_assert_eq!(arg_types.count, args.count + 1);
                    let arg_patterns = ctx.hir.add_invalid_patterns(args.count);
                    for ((arg_ty, arg), r) in
                        arg_types.iter().skip(1).zip(args).zip(arg_patterns.iter())
                    {
                        let mut arg_exhaustion = Exhaustion::None;
                        let pat = check(ctx, variables, &mut arg_exhaustion, arg, arg_ty);
                        ctx.hir.modify_pattern(r, pat);
                        // TODO: enum argument exhaustion
                    }
                    Pattern::EnumVariant {
                        ordinal,
                        types: arg_types.idx,
                        args: arg_patterns,
                    }
                }
                Err(err) => {
                    ctx.invalidate(expected);
                    if let Some(err) = err {
                        ctx.compiler
                            .errors
                            .emit_err(err.at_span(span.in_mod(ctx.module)));
                    }
                    for arg in args {
                        let mut arg_exhaustion = Exhaustion::None;
                        let arg_ty = ctx.hir.types.add_unknown();
                        check(ctx, variables, &mut arg_exhaustion, arg, arg_ty);
                    }
                    Pattern::Invalid
                }
            }
        }
        &Expr::Tuple(span, members) => {
            let member_types = ctx.hir.types.add_multiple_unknown(members.count);
            // PERF: could add .specify_tuple to avoid adding more types than necessary
            ctx.specify(expected, TypeInfo::Tuple(member_types), |_| span);
            let do_exhaust_checks = match exhaustion {
                Exhaustion::Full | Exhaustion::Invalid => false,
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
            let member_patterns = ctx.hir.add_invalid_patterns(members.count);
            for (i, ((item_pat, ty), pat_id)) in members
                .into_iter()
                .zip(member_types.iter())
                .zip(member_patterns.iter())
                .enumerate()
            {
                let pat = if do_exhaust_checks {
                    let Exhaustion::Tuple(member_exhaustion) = exhaustion else {
                        unreachable!()
                    };
                    check(ctx, variables, &mut member_exhaustion[i], item_pat, ty)
                } else {
                    check(ctx, variables, &mut Exhaustion::Full, item_pat, ty)
                };
                ctx.hir.modify_pattern(pat_id, pat);
            }
            debug_assert_eq!(members.count, member_patterns.count);
            debug_assert_eq!(members.count, member_types.count);
            Pattern::Tuple {
                member_count: members.count,
                patterns: member_patterns.index,
                types: member_types.idx,
            }
        }
        _ => {
            ctx.compiler
                .errors
                .emit_err(Error::NotAPattern { coming_soon: false }.at_span(ctx.span(pat)));
            *exhaustion = Exhaustion::Invalid;
            Pattern::Invalid
        }
    }
}
