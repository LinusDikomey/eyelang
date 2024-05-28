use dmap::DHashMap;
use types::Primitive;

use crate::{
    check::exhaust,
    compiler::{builtins, VarId},
    error::Error,
    hir::Pattern,
    parser::{
        ast::{Expr, ExprId, UnOp},
        token::{IntLiteral, Operator},
    },
    type_table::{LocalTypeId, LocalTypeIds, TypeInfo},
};

use super::{exhaust::Exhaustion, Ctx};

pub fn check(
    ctx: &mut Ctx,
    variables: &mut DHashMap<String, VarId>,
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
        &Expr::BoolLiteral { start: _, val } => {
            ctx.specify(expected, TypeInfo::Primitive(Primitive::Bool), |ast| {
                ast[pat].span(ast)
            });
            exhaustion.exhaust_bool(val);
            Pattern::Bool(val)
        }
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
                .specify_enum_literal(expected, &name, args.count, ctx.compiler);
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
            ctx.compiler
                .errors
                .emit_err(Error::NotAPattern { coming_soon: false }.at_span(ctx.span(pat)));
            Pattern::Invalid
        }
    }
}
