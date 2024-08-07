use std::rc::Rc;

use crate::{
    compiler::{Def, LocalItem, LocalScope, ResolvedTypeDef},
    error::Error,
    hir::{LValue, Node},
    parser::ast::{Expr, ExprId, UnOp},
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
                LocalItem::Def(def) => def_lvalue(ctx, expr, def),
            }
        }
        Expr::Hole(_) => (LValue::Ignore, ctx.hir.types.add_unknown()),
        &Expr::UnOp(_, UnOp::Deref, inner) => {
            let pointee = ctx.hir.types.add_unknown();
            let pointer = ctx.hir.types.add(TypeInfo::Pointer(pointee));
            let node = expr::check(ctx, inner, scope, pointer, return_ty, noreturn);
            (LValue::Deref(ctx.hir.add(node)), pointee)
        }
        &Expr::MemberAccess {
            left,
            name: name_span,
        } => {
            let name = &ctx.ast.src()[name_span.range()];
            let left_ty = ctx.hir.types.add_unknown();
            let left_node = expr::check(ctx, left, scope, left_ty, return_ty, noreturn);
            match ctx.hir.types[left_ty] {
                TypeInfo::ModuleItem(id) => {
                    let def =
                        ctx.compiler
                            .resolve_in_module(id, name, name_span.in_mod(ctx.module));
                    return def_lvalue(ctx, expr, def);
                }
                _ => {}
            }
            let mut pointer_count = 0;
            let mut current_ty = left_ty;
            loop {
                match ctx.hir.types[current_ty] {
                    TypeInfo::Unknown => {
                        ctx.compiler.errors.emit_err(
                            Error::TypeMustBeKnownHere { needed_bound: None }
                                .at_span(ctx.span(left)),
                        );
                        return (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid));
                    }
                    TypeInfo::UnknownSatisfying(bounds) => {
                        let needed_bound = bounds.iter().next().map(|bound| {
                            let id = ctx.hir.types.get_bound(bound).trait_id;
                            ctx.compiler.get_trait_name(id.0, id.1).to_owned()
                        });
                        ctx.compiler.errors.emit_err(
                            Error::TypeMustBeKnownHere { needed_bound }.at_span(ctx.span(left)),
                        );
                        return (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid));
                    }
                    TypeInfo::Invalid => {
                        return (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid));
                    }
                    TypeInfo::Pointer(pointee) => {
                        current_ty = pointee;
                        pointer_count += 1;
                    }
                    TypeInfo::TypeDef(id, generics) => {
                        let ty = ctx.compiler.get_resolved_type_def(id);
                        // TODO differentiate between nonexistant member and 'can't assign to
                        // member' in the case of methods, enum variants etc.
                        let def = Rc::clone(&ty.def);
                        match &*def {
                            ResolvedTypeDef::Struct(struct_) => {
                                let (indexed_field, elem_types) =
                                    struct_.get_indexed_field(ctx, generics, name);
                                if let Some((index, field_ty)) = indexed_field {
                                    let ptr =
                                        ctx.auto_ref_deref(pointer_count, 1, left_node, left_ty);
                                    let ptr = ctx.hir.add(ptr);
                                    return (
                                        LValue::Member {
                                            ptr,
                                            index,
                                            elem_types,
                                        },
                                        field_ty,
                                    );
                                } else {
                                    ctx.compiler.errors.emit_err(
                                        Error::NonexistantMember(None)
                                            .at_span(name_span.in_mod(ctx.module)),
                                    );
                                    return (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid));
                                }
                            }
                            ResolvedTypeDef::Enum(_) => {
                                ctx.compiler.errors.emit_err(
                                    Error::NonexistantMember(None)
                                        .at_span(name_span.in_mod(ctx.module)),
                                );
                                return (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid));
                            }
                        }
                    }
                    _ => {
                        ctx.compiler.errors.emit_err(
                            Error::NonexistantMember(None).at_span(name_span.in_mod(ctx.module)),
                        );
                        return (LValue::Invalid, ctx.hir.types.add(TypeInfo::Invalid));
                    }
                }
            }
        }
        Expr::TupleIdx { .. } => todo!("lvalue tuple indexing"),
        &Expr::Index { expr, idx, .. } => {
            let element_type = ctx.hir.types.add_unknown();
            let array_ty = ctx.hir.types.add(TypeInfo::Array {
                element: element_type,
                count: None,
            });
            let array = expr::check(ctx, expr, scope, array_ty, return_ty, noreturn);
            let array_ptr = Node::AddressOf {
                inner: ctx.hir.add(array),
                value_ty: array_ty,
            };
            let index_ty = ctx.hir.types.add(TypeInfo::Integer);
            let index = expr::check(ctx, idx, scope, index_ty, return_ty, noreturn);
            (
                LValue::ArrayIndex {
                    array_ptr: ctx.hir.add(array_ptr),
                    index: ctx.hir.add(index),
                    element_type,
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
