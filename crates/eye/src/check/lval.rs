use crate::{hir::LValue, type_table::{LocalTypeId, TypeInfo}, parser::ast::{Expr, ExprId, UnOp}, compiler::{LocalScope, LocalItem, Def}, error::Error};

use super::Ctx;


pub fn check(
    ctx: &mut Ctx,
    expr: ExprId,
    scope: &mut LocalScope,
) -> (LValue, LocalTypeId) {
    match &ctx.ast[expr] {
        &Expr::Ident { span } => {
            match scope.resolve(&ctx.ast.src()[span.range()], span, ctx.compiler) {
                LocalItem::Invalid | LocalItem::Def(Def::Invalid) => (
                    LValue::Invalid,
                    ctx.hir.types.add(TypeInfo::Invalid),
                ),
                LocalItem::Var(id) => {
                    let var_ty = ctx.hir.get_var(id);
                    (LValue::Variable(id), var_ty)
                }
                LocalItem::Def(Def::Global(module, id)) => {
                    let global_ty = &ctx.compiler.get_checked_global(module, id).0;
                    let ty = ctx.hir.types.info_from_resolved(global_ty);
                    let ty = ctx.hir.types.add(ty);
                    (LValue::Global(module, id), ty)
                }
                LocalItem::Def(_) => {
                    ctx.compiler.errors.emit_err(Error::CantAssignTo.at_span(ctx.span(expr)));
                    (
                        LValue::Invalid,
                        ctx.hir.types.add(TypeInfo::Invalid),
                    )
                }
            }
        }
        Expr::UnOp(_, UnOp::Deref, _) => todo!("assign to derefs"),
        Expr::MemberAccess { .. } => todo!("struct member assignment"),
        _ => {
            ctx.compiler.errors.emit_err(Error::CantAssignTo.at_span(ctx.span(expr)));
            (
                LValue::Invalid,
                ctx.hir.types.add(TypeInfo::Invalid),
            )
        }
    }
}
