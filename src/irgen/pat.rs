use crate::{
    ir::{Ref, TypeTableIndex, exhaust::{Exhaustion, self}, TypeInfo, builder::BinOp, RefVal},
    ast::{ExprRef, Expr, UnOp},
    token::{IntLiteral, Operator, FloatLiteral},
    error::Error,
    types::Primitive,
    span::TSpan
};

use super::{Scope, GenCtx, IrBuilder, int_literal, Symbol};

/// builds code to check if `pat` matches on `val` and gives back a boolean `Ref`
pub fn reduce_pat(
    scope: &mut Scope, ctx: &mut GenCtx, ir: &mut IrBuilder, val: Ref, pat: ExprRef,
    expected: TypeTableIndex, bool_ty: TypeTableIndex, exhaustion: &mut Exhaustion,
) -> Ref {
    let pat_expr = &ctx.ast[pat];
    let mut int_lit = |exhaustion: &mut Exhaustion, ctx: &mut GenCtx, lit: IntLiteral, lit_span: TSpan, neg| {
        exhaustion.exhaust_int(exhaust::SignedInt(lit.val, neg));
        let int_ty = lit.ty
            .map_or(TypeInfo::Int, |int_ty| TypeInfo::Primitive(int_ty.into()));

        let mut lit_val = int_literal(lit, lit_span, ir, expected, ctx);
        if neg {
            lit_val = ir.build_neg(lit_val, expected);
        }
        ir.specify(expected, int_ty, &mut ctx.errors, lit_span, &ctx.ctx);
        ir.build_bin_op(BinOp::Eq, val, lit_val, bool_ty)
    };
    
    match pat_expr {
        Expr::IntLiteral(lit_span) => {
            let lit = IntLiteral::parse(ctx.src(*lit_span));
            int_lit(exhaustion, ctx, lit, *lit_span, false)
        }
        Expr::UnOp(_, UnOp::Neg, val) => {
            let val = &ctx.ast[*val];
            match val {
                Expr::IntLiteral(lit_span) => {
                    let lit = IntLiteral::parse(ctx.src(*lit_span));
                    int_lit(exhaustion, ctx, lit, *lit_span, true)
                }
                Expr::FloatLiteral(_) => todo!(),
                _ => {
                    ctx.errors.emit_span(Error::NotAPattern, ctx.span(pat_expr));
                    ir.invalidate(expected);
                    Ref::UNDEF
                }
            }
        }
        Expr::FloatLiteral(_) => todo!(),
        Expr::BoolLiteral { start: _, val: bool_val } => {
            exhaustion.exhaust_bool(*bool_val);
            let bool_val = Ref::val(if *bool_val { RefVal::True } else { RefVal::False });
            ir.specify(expected, TypeInfo::Primitive(Primitive::Bool),
                &mut ctx.errors, pat_expr.span(ctx.ast), &ctx.ctx);
            ir.build_bin_op(BinOp::Eq, val, bool_val, bool_ty)
        }
        Expr::EnumLiteral { dot: _, ident } => {
            let variant_name = &ctx.ast.src(ctx.module).0[ident.range()];
            let variant = ir.build_enum_lit(variant_name, expected);
            exhaustion.exhaust_enum_variant(variant_name.to_owned());
            ir.specify_enum_variant(expected, variant_name, *ident, &ctx.ctx, &mut ctx.errors);
            ir.build_bin_op(BinOp::Eq, val, variant, bool_ty)
        }
        Expr::Unit(span) => {
            ir.specify(expected, TypeInfo::UNIT, &mut ctx.errors, *span, &ctx.ctx);
            *exhaustion = Exhaustion::Full;
            Ref::val(RefVal::True)
        }
        Expr::Nested(_, expr) => reduce_pat(scope, ctx, ir, val, *expr, expected, bool_ty, exhaustion),    
        Expr::Variable(span) => {
            let name = ctx.src(*span);
            let var = ir.build_decl(expected);
            ir.build_store(var, val);
            scope.add_symbol(name.to_owned(), Symbol::Var { ty: expected, var }, &mut ctx.globals);
            *exhaustion = Exhaustion::Full;
            Ref::val(RefVal::True)
        }
        &Expr::BinOp(Operator::Range | Operator::RangeExclusive, l, r) => {
            // TODO: float literals, negated literals
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
                        (
                            Kind::Int(exhaust::SignedInt(lit.val, false)),
                            int_literal(lit, l, ir, expected, ctx),
                        )
                    }
                    &Expr::FloatLiteral(l) => {
                        let lit = FloatLiteral::parse(ctx.src(l));
                        ir.specify(expected, TypeInfo::Float, &mut ctx.errors, expr.span(ctx.ast), &ctx.ctx);
                        (
                            Kind::Float,
                            ir.build_float(lit.val, expected)
                        )
                    }
                    &Expr::UnOp(_, UnOp::Neg, inner) if let Expr::IntLiteral(l) = ctx.ast[inner] => {
                        let lit = IntLiteral::parse(ctx.src(l));
                        let unsigned_val = int_literal(lit, l, ir, expected, ctx);
                        (
                            Kind::Int(exhaust::SignedInt(lit.val, true)),
                            ir.build_neg(unsigned_val, expected),
                        )
                    }
                    &Expr::UnOp(_, UnOp::Neg, inner) if let Expr::FloatLiteral(l) = ctx.ast[inner] => {
                        let lit = FloatLiteral::parse(ctx.src(l));
                        ir.specify(expected, TypeInfo::Float, &mut ctx.errors, expr.span(ctx.ast), &ctx.ctx);
                        (
                            Kind::Float,
                            ir.build_float(-lit.val, expected)
                        )
                    }
                    _ => {
                        ctx.errors.emit_span(Error::NotAPatternRangeValue, ctx.span(expr));
                        ir.invalidate(expected);
                        (
                            Kind::Invalid,
                            Ref::UNDEF
                        )
                    }
                }
            };
            let (l, l_ref) = range_side(l);
            let (r, r_ref) = range_side(r);
            match (l, r) {
                (Kind::Int(l), Kind::Int(r)) => _ = exhaustion.exhaust_int_range(l, r),
                _ => ()
            }

            let left_check = ir.build_bin_op(BinOp::GE, val, l_ref, bool_ty);
            let right_check = ir.build_bin_op(BinOp::LE, val, r_ref, bool_ty);

            ir.build_bin_op(BinOp::And, left_check, right_check, bool_ty)
        }
        Expr::StringLiteral(_) // TODO definitely very important
        | Expr::Block { .. }
        | Expr::Declare { .. }
        | Expr::DeclareWithVal { .. }
        | Expr::Return { .. }
        | Expr::Array(_, _) 
        | Expr::Tuple(_, _) 
        | Expr::If { .. } 
        | Expr::IfElse { .. } 
        | Expr::Match { .. } 
        | Expr::While { .. } 
        | Expr::FunctionCall { .. } 
        | Expr::UnOp(_, _, _) 
        | Expr::BinOp(_, _, _) 
        | Expr::MemberAccess { .. } // maybe when variables are allowed. Also qualified enum variants!
        | Expr::Index { .. } 
        | Expr::TupleIdx { .. } 
        | Expr::Cast(_, _, _)
        | Expr::Root(_) 
        | Expr::Asm { .. } 
        => {
            ctx.errors.emit_span(Error::NotAPattern, ctx.span(pat_expr));
            ir.invalidate(expected);
            Ref::UNDEF
        }
    }
}
