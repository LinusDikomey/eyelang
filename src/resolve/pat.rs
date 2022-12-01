use crate::{ast::{ExprRef, Expr, UnOp}, token::{IntLiteral, Operator, FloatLiteral}, span::TSpan, error::Error, types::Primitive};

use super::{Ctx, type_info::{TypeInfo, TypeTableIndex}, exhaust::{Exhaustion, self}, Ident};

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
        Expr::EnumLiteral { ident, .. } => {
            let name = &ctx.ast.src(ctx.scopes[ctx.scope].module.id).0[ident.range()];
            ctx.specify_enum_variant(expected, name, ident.in_mod(ctx.scopes[ctx.scope].module.id));
            exhaustion.exhaust_enum_variant(name.to_owned());
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
        /*
        Expr::BinOp(Operator::Range | Operator::RangeExclusive, l, r) => {
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
                        let lit = FloatLiteral::parse(&ctx.scope().module.src()[l.range()]);
                        ctx.specify(expected, TypeInfo::Float, ctx.span(pat_expr));
                    }
                    _ => {
                        ctx.errors.emit_span(Error::NotAPatternRangeValue, ctx.span(pat_expr));
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
        }
        */
        
        Expr::Tuple(_, _)
        | Expr::FloatLiteral(_)
        | Expr::Record { .. } // very useful to match on records
        | Expr::StringLiteral(_) // definitely very important
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