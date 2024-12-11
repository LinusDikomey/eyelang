use std::rc::Rc;

use span::TSpan;

use crate::{
    compiler::{Def, LocalItem, LocalScope, ResolvedTypeDef},
    error::Error,
    hir::{LValue, Node},
    parser::ast::{Ast, Expr, ExprId, UnOp},
    types::{LocalTypeId, LocalTypeIds, TypeInfo},
};

use super::{expr, Ctx};

pub fn check(
    ctx: &mut Ctx,
    expr: ExprId,
    scope: &mut LocalScope,
    return_ty: LocalTypeId,
    noreturn: &mut bool,
) -> (LValue, LocalTypeId) {
    match ctx.ast[expr] {
        Expr::Ident { span } => {
            match scope.resolve(&ctx.ast.src()[span.range()], span, ctx.compiler) {
                LocalItem::Invalid | LocalItem::Def(Def::Invalid) => {
                    (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid))
                }
                LocalItem::Var(id) => {
                    let var_ty = ctx.hir.get_var(id);
                    (LValue::Variable(id), var_ty)
                }
                LocalItem::Capture(id) => todo!("lvalue capture: {id:?}"),
                LocalItem::Def(def) => def_lvalue(ctx, expr, def),
            }
        }
        Expr::UnOp(_, UnOp::Deref, inner) => {
            let pointee = ctx.hir.types.add_unknown();
            let pointer = ctx.hir.types.add(TypeInfo::Pointer(pointee));
            let node = expr::check(ctx, inner, scope, pointer, return_ty, noreturn);
            (LValue::Deref(ctx.hir.add(node)), pointee)
        }
        Expr::MemberAccess {
            left,
            name: name_span,
        } => {
            let left_ty = ctx.hir.types.add_unknown();
            let left_val = expr::check(ctx, left, scope, left_ty, return_ty, noreturn);
            let name = &ctx.ast.src()[name_span.range()];
            if let TypeInfo::ModuleItem(id) = ctx.hir.types[left_ty] {
                let def = ctx
                    .compiler
                    .resolve_in_module(id, name, name_span.in_mod(ctx.module));
                return def_lvalue(ctx, expr, def);
            }
            let Some((dereffed_left_ty, pointer_count)) =
                auto_deref(ctx, left_ty, |ast| ast[left].span(ast))
            else {
                return (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid));
            };

            match dereffed_left_ty {
                TypeInfo::TypeDef(id, generics) => {
                    let ty = ctx.compiler.get_resolved_type_def(id);
                    // TODO differentiate between nonexistant member and 'can't assign to
                    // member' in the case of methods, enum variants etc.
                    let def = Rc::clone(&ty.def);
                    match &*def {
                        ResolvedTypeDef::Struct(struct_) => {
                            let (indexed_field, elem_types) =
                                struct_.get_indexed_field(ctx, generics, name);
                            let Some((index, field_ty)) = indexed_field else {
                                ctx.compiler.errors.emit_err(
                                    Error::NonexistantMember(None)
                                        .at_span(name_span.in_mod(ctx.module)),
                                );
                                return (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid));
                            };

                            let left_lval =
                                dereffed_to_lvalue(ctx, left_val, left_ty, pointer_count, |ast| {
                                    ast[left].span(ast)
                                });
                            (
                                LValue::Member {
                                    tuple: ctx.hir.add_lvalue(left_lval),
                                    index,
                                    elem_types,
                                },
                                field_ty,
                            )
                        }
                        ResolvedTypeDef::Enum(_) => {
                            ctx.compiler.errors.emit_err(
                                Error::NonexistantMember(None)
                                    .at_span(name_span.in_mod(ctx.module)),
                            );
                            (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid))
                        }
                    }
                }
                _ => {
                    // TODO(error): better error why the type doesn't have named members
                    ctx.compiler.errors.emit_err(
                        Error::NonexistantMember(None).at_span(name_span.in_mod(ctx.module)),
                    );
                    (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid))
                }
            }
        }
        Expr::TupleIdx { left, idx, .. } => {
            let left_ty = ctx.hir.types.add_unknown();
            let left_val = expr::check(ctx, left, scope, left_ty, return_ty, noreturn);
            let Some((dereffed_ty, pointer_count)) =
                auto_deref(ctx, left_ty, |ast| ast[left].span(ast))
            else {
                return (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid));
            };
            match dereffed_ty {
                TypeInfo::Tuple(elem_types) => {
                    let Some(elem_ty) = elem_types.nth(idx) else {
                        ctx.compiler
                            .errors
                            .emit_err(Error::NonexistantMember(None).at_span(ctx.span(expr)));
                        return (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid));
                    };
                    let lval = dereffed_to_lvalue(ctx, left_val, left_ty, pointer_count, |ast| {
                        ast[left].span(ast)
                    });
                    (
                        LValue::Member {
                            tuple: ctx.hir.add_lvalue(lval),
                            index: idx,
                            elem_types,
                        },
                        elem_ty,
                    )
                }
                _ => {
                    // TODO(error): use span of the idx, not of the whole expr
                    // TODO(error): better error why the type doesn't have tuple members
                    ctx.compiler
                        .errors
                        .emit_err(Error::NonexistantMember(None).at_span(ctx.span(expr)));
                    (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid))
                }
            }
        }
        Expr::Index { expr, idx, .. } => {
            let element_type = ctx.hir.types.add_unknown();
            let (array, array_ty) = check(ctx, expr, scope, return_ty, noreturn);
            ctx.specify(
                array_ty,
                TypeInfo::Array {
                    element: element_type,
                    count: None,
                },
                |ast| ast[expr].span(ast),
            );
            let index_ty = ctx.hir.types.add(TypeInfo::Integer);
            let index = expr::check(ctx, idx, scope, index_ty, return_ty, noreturn);
            (
                LValue::ArrayIndex {
                    array: ctx.hir.add_lvalue(array),
                    index: ctx.hir.add(index),
                    elem_ty: element_type,
                },
                element_type,
            )
        }
        _ => {
            ctx.compiler
                .errors
                .emit_err(Error::CantAssignTo.at_span(ctx.span(expr)));
            (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid))
        }
    }
}

fn auto_deref(
    ctx: &mut Ctx<'_>,
    ty: LocalTypeId,
    span: impl Fn(&Ast) -> TSpan,
) -> Option<(TypeInfo, u32)> {
    let mut pointer_count = 0;
    let mut current_ty = ty;
    loop {
        match ctx.hir.types[current_ty] {
            TypeInfo::Pointer(pointee) => {
                current_ty = pointee;
                pointer_count += 1;
            }
            TypeInfo::Unknown => {
                ctx.compiler.errors.emit_err(
                    Error::TypeMustBeKnownHere { needed_bound: None }
                        .at_span(span(ctx.ast).in_mod(ctx.module)),
                );
                return None;
            }
            TypeInfo::UnknownSatisfying(bounds) => {
                let needed_bound = bounds.iter().next().map(|bound| {
                    let id = ctx.hir.types.get_bound(bound).trait_id;
                    ctx.compiler.get_trait_name(id.0, id.1).to_owned()
                });
                ctx.compiler.errors.emit_err(
                    Error::TypeMustBeKnownHere { needed_bound }
                        .at_span(span(ctx.ast).in_mod(ctx.module)),
                );
                return None;
            }
            TypeInfo::Invalid => return None,
            ty => return Some((ty, pointer_count)),
        }
    }
}
fn dereffed_to_lvalue(
    ctx: &mut Ctx,
    node: Node,
    ty: LocalTypeId,
    mut pointer_count: u32,
    span: impl Fn(&Ast) -> TSpan,
) -> LValue {
    if pointer_count == 0 {
        if let Some(lval) = LValue::try_from_node(&node, &mut ctx.hir) {
            lval
        } else {
            ctx.compiler
                .errors
                .emit_err(Error::CantAssignTo.at_span(span(ctx.ast).in_mod(ctx.module)));
            LValue::Invalid
        }
    } else {
        let mut current_val = node;
        let mut current_ty = ty;
        // perform additional derefs and keep the last one as an LValue
        while pointer_count > 1 {
            let TypeInfo::Pointer(pointee) = ctx.hir.types[current_ty] else {
                unreachable!()
            };
            current_val = Node::Deref {
                value: ctx.hir.add(current_val),
                deref_ty: pointee,
            };
            current_ty = pointee;
            pointer_count -= 1;
        }
        LValue::Deref(ctx.hir.add(current_val))
    }
}

fn def_lvalue(ctx: &mut Ctx, expr: ExprId, def: Def) -> (LValue, LocalTypeId) {
    match def {
        Def::Global(module, id) => {
            // PERF: cloning type
            let global_ty = ctx.compiler.get_checked_global(module, id).0.clone();
            let ty = ctx.type_from_resolved(&global_ty, LocalTypeIds::EMPTY);
            let ty = ctx.hir.types.add_info_or_idx(ty);
            (LValue::Global(module, id), ty)
        }
        Def::Invalid => (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid)),
        _ => {
            ctx.compiler
                .errors
                .emit_err(Error::CantAssignTo.at_span(ctx.span(expr)));
            (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid))
        }
    }
}
