use crate::{ast::{ExprRef, Expr}, token::IntLiteral, span::TSpan, error::Error};

use super::{Ctx, LocalScope, type_info::{TypeInfo, TypeTableIndex}, exhaust::{Exhaustion, self}};

impl<'a> LocalScope<'a> {
    pub(super) fn pat(&mut self, pat_expr: ExprRef, expected: TypeTableIndex, mut ctx: Ctx, exhaustion: &mut Exhaustion) {
        let expr = &ctx.ast[pat_expr];  
        let mut int_lit = |exhaustion: &mut Exhaustion, mut ctx: Ctx, lit: IntLiteral, lit_span: TSpan, neg| {
            exhaustion.exhaust_int(exhaust::SignedInt(lit.val, neg));
            let int_ty = lit.ty
                .map_or(TypeInfo::Int, |int_ty| TypeInfo::Primitive(int_ty.into()));
        };
        match expr {
            &Expr::IntLiteral(lit_span) => {
                let lit = IntLiteral::parse(&self.scope.module.src()[lit_span.range()]);
                int_lit(exhaustion, ctx, lit, lit_span, false);
            }
            Expr::FloatLiteral(_) => todo!(),
            Expr::BoolLiteral { start, val } => todo!(),
            Expr::EnumLiteral { dot, ident } => todo!(),
            Expr::Nested(_, _) => todo!(),
            Expr::Unit(_) => todo!(),
            Expr::Variable { span, .. } => {
                exhaustion.exhaust_full();
                let name = self.scope.module.src()[span.range()].to_owned();
                let id = ctx.new_var(expected);
                self.define_var(name, id);
                let Expr::Variable { resolved, .. } = &mut ctx.ast[pat_expr] else { unreachable!() };
                *resolved = id;
            }
            Expr::Hole(_) => todo!(),
            Expr::Tuple(_, _) => todo!(),

            Expr::Record { .. } // very useful to match on records
            | Expr::StringLiteral(_) // TODO definitely very important
            | Expr::Block { .. }
            | Expr::Declare { .. }
            | Expr::DeclareWithVal { .. }
            | Expr::Return { .. }
            | Expr::Array(_, _)
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
                ctx.errors.emit_span(Error::NotAPattern, expr.span_in(&ctx.ast, self.scope.module.id));
            }
            
        }
    }
}