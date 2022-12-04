use crate::{ast::{ExprRef, Expr, UnOp}, token::{IntLiteral, Operator}, span::TSpan, error::Error, types::Primitive};

use super::{Ctx, type_info::{TypeInfo, TypeTableIndex}, exhaust::{Exhaustion, self}, Ident, types::TupleCountMode};

pub(super) fn pat(pat_expr: ExprRef, expected: TypeTableIndex, mut ctx: Ctx, exhaustion: &mut Exhaustion) {
    ctx.symbols.expr_types[pat_expr.idx()] = expected;

    let expr = &ctx.ast[pat_expr];  
    let int_lit = |exhaustion: &mut Exhaustion, mut ctx: Ctx, lit: IntLiteral, lit_span: TSpan, neg| {
        exhaustion.exhaust_int(exhaust::SignedInt(lit.val, neg));
        let int_ty = lit.ty
            .map_or(TypeInfo::Int, |int_ty| TypeInfo::Primitive(int_ty.into()));
        ctx.specify(expected, int_ty, lit_span.in_mod(ctx.scopes[ctx.scope].module.id));
    };
    match expr {
        &Expr::IntLiteral(lit_span) => {
            let lit = IntLiteral::parse(&ctx.scopes[ctx.scope].module.src()[lit_span.range()]);
            int_lit(exhaustion, ctx, lit, lit_span, false);
        }
        &Expr::UnOp(_, UnOp::Neg, val) => {
            let val = &ctx.ast[val];
            match val {
                Expr::IntLiteral(lit_span) => {
                    let lit = IntLiteral::parse(&ctx.ast.src(ctx.scope().module.id).0[lit_span.range()]);
                    int_lit(exhaustion, ctx, lit, *lit_span, true)
                }
                Expr::FloatLiteral(_) => {
                    ctx.errors.emit_span(Error::NotAPattern { coming_soon: true }, ctx.span(pat_expr));
                    ctx.types.invalidate(expected);
                }
                _ => {
                    ctx.errors.emit_span(Error::NotAPattern { coming_soon: false }, ctx.span(pat_expr));
                    ctx.types.invalidate(expected);
                }
            }
        }
        Expr::BoolLiteral { start: _, val } => {
            exhaustion.exhaust_bool(*val);
            ctx.specify(expected, TypeInfo::Primitive(Primitive::Bool), expr.span_in(ctx.ast, ctx.scopes[ctx.scope].module.id));
        }
        Expr::EnumLiteral { ident, args, .. } => {
            let name = &ctx.ast.src(ctx.scopes[ctx.scope].module.id).0[ident.range()];

            let arg_types = ctx.types.add_multiple_unknown(args.count);

            for (arg, ty) in ctx.ast[*args].iter().zip(arg_types.iter()) {
                let mut variant_exhaustion = Exhaustion::None; // TODO: enum variant data exhaustion
                pat(*arg, ty, ctx.reborrow(), &mut variant_exhaustion);
            }

            ctx.specify_enum_variant(expected, name, ident.in_mod(ctx.scopes[ctx.scope].module.id), arg_types);
            exhaustion.exhaust_enum_variant(name.to_owned());
        }
        Expr::StringLiteral(_) => {
            ctx.specify(expected, ctx.symbols.builtins.str_info(), ctx.span(pat_expr));
            // TODO: exhaust for duplicate match arms
        }
        Expr::Nested(_, inner) => pat(*inner, expected, ctx, exhaustion),
        Expr::Unit(span) => ctx.specify(expected, TypeInfo::UNIT, span.in_mod(ctx.scopes[ctx.scope].module.id)),
        Expr::Variable { span, id } => {
            let var_id = ctx.new_var(super::Var { ty: expected });
            ctx.set_ident(*id, Ident::Var(var_id));
            exhaustion.exhaust_full();
            let name = ctx.scopes[ctx.scope].module.src()[span.range()].to_owned();
            ctx.scopes[ctx.scope].define_var(name, var_id);
        }
        Expr::Hole(_) => exhaustion.exhaust_full(),
        &Expr::BinOp(Operator::Range | Operator::RangeExclusive, l, r) => {
            enum Kind {
                Int(exhaust::SignedInt),
                Float,
                Invalid,
            }
            let mut range_side = |expr_ref| {
                let expr = &ctx.ast[expr_ref];
                match expr {
                    &Expr::IntLiteral(l) => {
                        let lit = IntLiteral::parse(ctx.src(l));
                        ctx.specify(expected, TypeInfo::Int, ctx.span(expr_ref));
                        Kind::Int(exhaust::SignedInt(lit.val, false))
                    }
                    &Expr::FloatLiteral(_) => {
                        ctx.specify(expected, TypeInfo::Float, ctx.span(expr_ref));
                        Kind::Float
                    }
                    &Expr::UnOp(_, UnOp::Neg, inner) if let Expr::IntLiteral(l) = ctx.ast[inner] => {
                        let lit = IntLiteral::parse(ctx.src(l));
                        ctx.specify(expected, TypeInfo::Int, ctx.span(expr_ref));
                        Kind::Int(exhaust::SignedInt(lit.val, true))
                    }
                    &Expr::UnOp(_, UnOp::Neg, inner) if let Expr::FloatLiteral(_) = ctx.ast[inner] => {
                        ctx.specify(expected, TypeInfo::Float, ctx.span(expr_ref));
                        Kind::Float
                    }
                    _ => {
                        ctx.errors.emit_span(Error::NotAPatternRangeValue, ctx.span(pat_expr));
                        ctx.types.invalidate(expected);
                        Kind::Invalid
                    }
                }
            };
            let l = range_side(l);
            let r = range_side(r);
            match (l, r) {
                (Kind::Int(l), Kind::Int(r)) => _ = exhaustion.exhaust_int_range(l, r),
                _ => ()
            }
        }
        &Expr::Tuple(span, members) => {
            let member_types = ctx.types.add_multiple_unknown(members.count);
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
            for (i, (&item_pat, ty)) in ctx.ast[members].into_iter().zip(member_types.iter()).enumerate() {
                if do_exhaust_checks {
                    let Exhaustion::Tuple(members) = exhaustion else { unreachable!() };
                    pat(item_pat, ty, ctx.reborrow(), &mut members[i]);
                } else {
                    pat(item_pat, ty, ctx.reborrow(), &mut Exhaustion::Full);
                };
            }
        }


        Expr::FloatLiteral(_)
        | Expr::Record { .. } // very useful to match on records
        | Expr::Array(_, _)
        | Expr::MemberAccess { .. } // maybe when variables are allowed. Also qualified enum variants!
        | Expr::FunctionCall { .. } => {
            ctx.errors.emit_span(
                Error::NotAPattern { coming_soon: true },
                expr.span_in(&ctx.ast, ctx.scopes[ctx.scope].module.id)
            );
        }

        Expr::Block { .. }
        | Expr::Declare { .. }
        | Expr::DeclareWithVal { .. }
        | Expr::Return { .. }
        | Expr::ReturnUnit { .. }
        | Expr::If { .. }
        | Expr::IfElse { .. } 
        | Expr::Match { .. } 
        | Expr::While { .. } 
        | Expr::UnOp(_, _, _) 
        | Expr::BinOp(_, _, _) 
        | Expr::Index { .. } 
        | Expr::TupleIdx { .. } 
        | Expr::Cast(_, _, _)
        | Expr::Root(_) 
        | Expr::Asm { .. } 
        => {
            ctx.errors.emit_span(
                Error::NotAPattern { coming_soon: false },
                expr.span_in(&ctx.ast, ctx.scopes[ctx.scope].module.id)
            );
        }
        
    }
}