use crate::ast::{ExprRef, self};

use super::{ExprInfo, Ctx, scope_defs, LocalScope, type_info::TypeInfo};

impl<'a> LocalScope<'a> {
    pub(super) fn expr(&mut self, expr: ExprRef, mut info: ExprInfo, mut ctx: Ctx) {
        match &ctx.ast[expr] {
            ast::Expr::Block { span: _, items, defs } => {
                let defs = scope_defs(&ctx.ast[*defs], ctx.symbols);
                let mut block_scope = self.child(defs);
                for item in items.iter() {
                    let expected = ctx.types.add_unknown();
                    block_scope.expr(item, info.with_expected(expected), ctx.reborrow());
                }
            }
            ast::Expr::Declare { pat, annotated_ty } => {
                
            }
            ast::Expr::DeclareWithVal { pat, annotated_ty, val } => todo!(),
            ast::Expr::Return { start, val } => todo!(),
            ast::Expr::IntLiteral(span) => {
                ctx.specify(info.expected, TypeInfo::Int, span.in_mod(self.scope.module.id));
            }
            ast::Expr::FloatLiteral(_) => todo!(),
            ast::Expr::StringLiteral(_) => todo!(),
            ast::Expr::BoolLiteral { start, val } => todo!(),
            ast::Expr::EnumLiteral { dot, ident } => todo!(),
            ast::Expr::Record { span, names, values } => todo!(),
            ast::Expr::Nested(_, _) => todo!(),
            ast::Expr::Unit(_) => todo!(),
            ast::Expr::Variable { .. } => todo!(),
            ast::Expr::Hole(_) => todo!(),
            ast::Expr::Array(_, _) => todo!(),
            ast::Expr::Tuple(_, _) => todo!(),
            ast::Expr::If { start, cond, then } => todo!(),
            ast::Expr::IfElse { start, cond, then, else_ } => todo!(),
            ast::Expr::Match { start, end, val, extra_branches, branch_count } => todo!(),
            ast::Expr::While { start, cond, body } => todo!(),
            ast::Expr::FunctionCall { func, args, end } => todo!(),
            ast::Expr::UnOp(_, _, _) => todo!(),
            ast::Expr::BinOp(_, _, _) => todo!(),
            ast::Expr::MemberAccess { left, name } => todo!(),
            ast::Expr::Index { expr, idx, end } => todo!(),
            ast::Expr::TupleIdx { expr, idx, end } => todo!(),
            ast::Expr::Cast(_, _, _) => todo!(),
            ast::Expr::Root(_) => todo!(),
            ast::Expr::Asm { span, asm_str_span, args } => todo!(),
        }
    }
}