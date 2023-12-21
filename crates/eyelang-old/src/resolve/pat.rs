use crate::{ast::{ExprRef, Expr, UnOp, ExprExtra}, token::{IntLiteral, Operator}, span::{TSpan, Span}, error::Error, types::Primitive, dmap, ir::types::TypeRef};

use super::{Ctx, type_info::TypeInfo, exhaust::{Exhaustion, self}, Ident, types::TupleCountMode};

pub(super) fn pat(pat_expr: ExprRef, expected: TypeRef, mut ctx: Ctx, exhaustion: &mut Exhaustion) {
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
            ctx.specify(
                expected,
                TypeInfo::Primitive(Primitive::Bool),
                expr.span_in(ctx.ast, ctx.scopes[ctx.scope].module.id)
            );
        }
        Expr::EnumLiteral { ident, args, .. } => {
            enum_variant_pat(
                exhaustion,
                expected,
                &ctx.ast.src(ctx.scopes[ctx.scope].module.id).0[ident.range()],
                expr.span_in(ctx.ast, ctx.scope().module.id),
                ctx.reborrow(),
                *args
            );
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
                match *expr {
                    Expr::IntLiteral(l) => {
                        let lit = IntLiteral::parse(ctx.src(l));
                        ctx.specify(expected, TypeInfo::Int, ctx.span(expr_ref));
                        Kind::Int(exhaust::SignedInt(lit.val, false))
                    }
                    Expr::FloatLiteral(_) => {
                        ctx.specify(expected, TypeInfo::Float, ctx.span(expr_ref));
                        Kind::Float
                    }
                    Expr::UnOp(_, UnOp::Neg, inner) if let Expr::IntLiteral(l) = ctx.ast[inner] => {
                        let lit = IntLiteral::parse(ctx.src(l));
                        ctx.specify(expected, TypeInfo::Int, ctx.span(expr_ref));
                        Kind::Int(exhaust::SignedInt(lit.val, true))
                    }
                    Expr::UnOp(_, UnOp::Neg, inner) if let Expr::FloatLiteral(_) = ctx.ast[inner] => {
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
            if let (Kind::Int(l), Kind::Int(r)) = (range_side(l), range_side(r)) {
                exhaustion.exhaust_int_range(l, r);
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
            for (i, (&item_pat, ty)) in ctx.ast[members].iter().zip(member_types.iter()).enumerate() {
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
        | Expr::Function { .. }
        | Expr::Array(_, _)
        | Expr::MemberAccess { .. } // maybe when variables are allowed. Also qualified enum variants!
        | Expr::FunctionCall { .. } => {
            ctx.errors.emit_span(
                Error::NotAPattern { coming_soon: true },
                expr.span_in(ctx.ast, ctx.scopes[ctx.scope].module.id)
            );
        }
        Expr::Block { .. }
        | Expr::Declare { .. }
        | Expr::DeclareWithVal { .. }
        | Expr::Return { .. }
        | Expr::ReturnUnit { .. }
        | Expr::If { .. }
        | Expr::IfPat { .. }
        | Expr::IfElse { .. } 
        | Expr::IfPatElse { .. }
        | Expr::Match { .. } 
        | Expr::While { .. } 
        | Expr::WhilePat { .. }
        | Expr::UnOp(_, _, _) 
        | Expr::BinOp(_, _, _) 
        | Expr::Index { .. } 
        | Expr::TupleIdx { .. } 
        | Expr::As(_, _, _)
        | Expr::Root(_) 
        | Expr::Asm { .. } 
        => {
            ctx.errors.emit_span(
                Error::NotAPattern { coming_soon: false },
                expr.span_in(ctx.ast, ctx.scopes[ctx.scope].module.id)
            );
        }
        
    }
}

fn enum_variant_pat(exhaustion: &mut Exhaustion, expected: TypeRef, variant: &str, span: Span, mut ctx: Ctx, args: ExprExtra) {
    let arg_types = ctx.types.add_multiple_unknown(args.count);
    match exhaustion {
        Exhaustion::None => {
            let mut variants = dmap::with_capacity(1);
            let args = ctx.ast[args].iter().zip(arg_types.iter()).map(|(arg, arg_ty)| {
                let mut variant_exhaustion = Exhaustion::None;
                pat(*arg, arg_ty, ctx.reborrow(), &mut variant_exhaustion);
                variant_exhaustion
            }).collect();
            variants.insert(variant.to_owned(), args);
            *exhaustion = Exhaustion::Enum(variants);
        }
        Exhaustion::Enum(variants) => if let Some(arg_exhaustions) = variants.get_mut(variant) {
            for ((&arg, arg_ty), arg_exhaustion) in ctx.ast[args].iter().zip(arg_types.iter()).zip(arg_exhaustions) {
                pat(arg, arg_ty, ctx.reborrow(), arg_exhaustion)
            }
        } else {
            let args = ctx.ast[args].iter().zip(arg_types.iter()).map(|(&arg, arg_ty)| {
                let mut variant_exhaustion = Exhaustion::None;
                pat(arg, arg_ty, ctx.reborrow(), &mut variant_exhaustion);
                variant_exhaustion
            }).collect();
            variants.insert(variant.to_owned(), args);
        }
        Exhaustion::Full => {
            for (&arg, arg_ty) in ctx.ast[args].iter().zip(arg_types.iter()) {
                pat(arg, arg_ty, ctx.reborrow(), &mut Exhaustion::Full);
            }
        }
        _ => *exhaustion = Exhaustion::Invalid
    }
    ctx.specify_enum_variant(expected, variant, span, arg_types);
}
