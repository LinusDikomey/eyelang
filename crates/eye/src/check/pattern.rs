use dmap::DHashMap;

use crate::{compiler::VarId, parser::{ast::{ExprId, Expr, UnOp}, token::{Operator, IntLiteral}}, type_table::{LocalTypeId, TypeInfo}, hir::Pattern, check::exhaust, error::Error};

use super::{Ctx, exhaust::Exhaustion};


pub fn check(
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

