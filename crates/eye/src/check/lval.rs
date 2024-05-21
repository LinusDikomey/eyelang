use crate::{
    compiler::{Def, LocalItem, LocalScope},
    error::Error,
    hir::LValue,
    parser::ast::{Expr, ExprId, UnOp},
    type_table::{LocalTypeId, LocalTypeIds, TypeInfo},
};

use super::{expr, Ctx};

pub fn check(
    ctx: &mut Ctx,
    expr: ExprId,
    scope: &mut LocalScope,
    return_ty: LocalTypeId,
) -> (LValue, LocalTypeId) {
    match &ctx.ast[expr] {
        &Expr::Ident { span } => {
            match scope.resolve(&ctx.ast.src()[span.range()], span, ctx.compiler) {
                LocalItem::Invalid | LocalItem::Def(Def::Invalid) => {
                    (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid))
                }
                LocalItem::Var(id) => {
                    let var_ty = ctx.hir.get_var(id);
                    (LValue::Variable(id), var_ty)
                }
                LocalItem::Def(Def::Global(module, id)) => {
                    // PERF: cloning type
                    let global_ty = ctx.compiler.get_checked_global(module, id).0.clone();
                    let ty = ctx.type_from_resolved(&global_ty, LocalTypeIds::EMPTY);
                    let ty = ctx.hir.types.add_info_or_idx(ty);
                    (LValue::Global(module, id), ty)
                }
                LocalItem::Def(_) => {
                    ctx.compiler
                        .errors
                        .emit_err(Error::CantAssignTo.at_span(ctx.span(expr)));
                    (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid))
                }
            }
        }
        &Expr::UnOp(_, UnOp::Deref, inner) => {
            let pointee = ctx.hir.types.add_unknown();
            let pointer = ctx.hir.types.add(TypeInfo::Pointer(pointee));
            let node = expr::check(ctx, inner, scope, pointer, return_ty);
            (LValue::Deref(ctx.hir.add(node)), pointee)
        }
        Expr::MemberAccess { .. } => todo!("struct member assignment"),
        _ => {
            ctx.compiler
                .errors
                .emit_err(Error::CantAssignTo.at_span(ctx.span(expr)));
            (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid))
        }
    }
}
