use crate::{ast::{ExprRef, Expr}, token::IntLiteral, span::TSpan, error::Error, types::Primitive};

use super::{Ctx, type_info::{TypeInfo, TypeTableIndex}, exhaust::{Exhaustion, self}, Ident, scope::{ScopeId, Scopes}};

pub(super) fn pat(scopes: &mut Scopes, scope: ScopeId, pat_expr: ExprRef, expected: TypeTableIndex, mut ctx: Ctx, exhaustion: &mut Exhaustion) {
    ctx.symbols.expr_types[pat_expr.idx()] = expected;

    let expr = &ctx.ast[pat_expr];  
    let int_lit = |exhaustion: &mut Exhaustion, mut ctx: Ctx, lit: IntLiteral, lit_span: TSpan, neg| {
        exhaustion.exhaust_int(exhaust::SignedInt(lit.val, neg));
        let int_ty = lit.ty
            .map_or(TypeInfo::Int, |int_ty| TypeInfo::Primitive(int_ty.into()));
        ctx.specify(expected, int_ty, lit_span.in_mod(scopes[scope].module.id));
    };
    match expr {
        &Expr::IntLiteral(lit_span) => {
            let lit = IntLiteral::parse(&scopes[scope].module.src()[lit_span.range()]);
            int_lit(exhaustion, ctx, lit, lit_span, false);
        }
        Expr::BoolLiteral { start: _, val } => {
            exhaustion.exhaust_bool(*val);
            ctx.specify(expected, TypeInfo::Primitive(Primitive::Bool), expr.span_in(ctx.ast, scopes[scope].module.id));
        }
        Expr::EnumLiteral { ident, .. } => {
            let name = &ctx.ast.src(scopes[scope].module.id).0[ident.range()];
            ctx.specify_enum_variant(expected, name, ident.in_mod(scopes[scope].module.id));
            exhaustion.exhaust_enum_variant(name.to_owned());
        }
        Expr::Nested(_, inner) => pat(scopes, scope, *inner, expected, ctx, exhaustion),
        Expr::Unit(span) => ctx.specify(expected, TypeInfo::UNIT, span.in_mod(scopes[scope].module.id)),
        Expr::Variable { span, id } => {
            let var_id = ctx.new_var(super::Var { ty: expected });
            ctx.set_ident(*id, Ident::Var(var_id));
            exhaustion.exhaust_full();
            let name = scopes[scope].module.src()[span.range()].to_owned();
            scopes[scope].define_var(name, var_id);
        }
        Expr::Hole(_) => exhaustion.exhaust_full(),
        Expr::Tuple(_, _) => todo!(),

        Expr::FloatLiteral(_)
        | Expr::Record { .. } // very useful to match on records
        | Expr::StringLiteral(_) // definitely very important
        | Expr::Array(_, _)
        | Expr::MemberAccess { .. } // maybe when variables are allowed. Also qualified enum variants!
        | Expr::FunctionCall { .. } => {
            ctx.errors.emit_span(
                Error::NotAPattern { coming_soon: true },
                expr.span_in(&ctx.ast, scopes[scope].module.id)
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
                expr.span_in(&ctx.ast, scopes[scope].module.id)
            );
        }
        
    }
}