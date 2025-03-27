use std::rc::Rc;

use id::ConstValueId;
use span::TSpan;
use types::{Primitive, Type};

use crate::{
    compiler::{LocalScope, ResolvedStructDef, ResolvedTypeContent, Signature},
    error::Error,
    hir::{Node, NodeId, NodeIds},
    parser::ast::{Call, ExprIds, ExprId},
    types::{Bound, LocalTypeId, LocalTypeIds, TypeInfo},
};

use super::{Ctx, expr};

pub fn check_call(
    ctx: &mut Ctx,
    call: &Call,
    expr: ExprId,
    scope: &mut LocalScope,
    expected: LocalTypeId,
    return_ty: LocalTypeId,
    noreturn: &mut bool,
) -> Node {
    let called_ty = ctx.hir.types.add_unknown();
    let called_node = expr::check(ctx, call.called_expr, scope, called_ty, return_ty, noreturn);
    let call_span = TSpan::new(call.open_paren_start, call.end);
    let mut call_with_function =
        |ctx: &mut Ctx, function: NodeId, signature: &Signature, generics| {
            let call_node = match check_call_args(
                ctx,
                scope,
                return_ty,
                noreturn,
                call_span,
                call.args,
                &call.named_args,
                generics,
                &signature.params,
                &signature.named_params,
                signature.varargs,
                false,
            ) {
                Ok((args, arg_types)) => {
                    if *noreturn {
                        return Node::Invalid;
                    }
                    let call_noreturn =
                        matches!(signature.return_type, Type::Primitive(Primitive::Never));
                    if call_noreturn {
                        *noreturn = true;
                    }

                    Node::Call {
                        function,
                        args,
                        return_ty: expected,
                        arg_types,
                        noreturn: call_noreturn,
                    }
                }
                Err(err) => {
                    ctx.compiler.errors.emit_err(err);
                    ctx.invalidate(expected);
                    Node::Invalid
                }
            };
            // TODO: check that the type is never type recursively, handling empty enums as never
            if signature.return_type == Type::Primitive(Primitive::Never) {
                *noreturn = true;
            }
            call_node
        };
    match ctx.hir.types[called_ty] {
        TypeInfo::Invalid => {
            ctx.invalidate(expected);
            Node::Invalid
        }
        TypeInfo::TypeItem { ty: item_ty } => match ctx.hir.types[item_ty] {
            TypeInfo::TypeDef(id, generics) => {
                debug_assert_eq!(
                    generics.count,
                    ctx.compiler.get_resolved_type_generic_count(id) as u32
                );
                let resolved = Rc::clone(ctx.compiler.get_resolved_type_def(id));
                match &resolved.def {
                    ResolvedTypeContent::Struct(struct_def) => {
                        ctx.unify(expected, item_ty, |ast| ast[expr].span(ast));
                        check_struct_initializer(
                            ctx, struct_def, generics, call, scope, return_ty, noreturn,
                        )
                        .unwrap_or_else(|_| {
                            ctx.invalidate(expected);
                            Node::Invalid
                        })
                    }
                    ResolvedTypeContent::Enum(_) => {
                        ctx.compiler
                            .errors
                            .emit_err(Error::FunctionOrStructTypeExpected.at_span(ctx.span(expr)));
                        Node::Invalid
                    }
                }
            }
            TypeInfo::Invalid => Node::Invalid,
            _ => {
                ctx.invalidate(expected);
                ctx.compiler
                    .errors
                    .emit_err(Error::FunctionOrStructTypeExpected.at_span(ctx.span(expr)));
                Node::Invalid
            }
        },
        TypeInfo::FunctionItem {
            module,
            function,
            generics,
        } => {
            let signature = Rc::clone(ctx.compiler.get_signature(module, function));
            ctx.specify_resolved(expected, &signature.return_type, generics, |ast| {
                ast[expr].span(ast)
            });
            let function = ctx.hir.add(Node::FunctionItem(module, function, generics));
            call_with_function(ctx, function, &signature, generics)
        }
        TypeInfo::Function {
            params,
            return_type,
        } => {
            // check the partially inferred type. If we know it is uninhabited, the function is noreturn
            let call_noreturn = ctx.hir.types.is_uninhabited(ctx.hir.types[return_type]);
            ctx.unify(expected, return_type, |_| call_span);
            match check_call_args_inner(
                ctx,
                scope,
                return_ty,
                noreturn,
                call_span,
                call.args,
                &[],
                params.count,
                &[],
                params,
                false,
            ) {
                Ok((args, arg_types)) => {
                    if *noreturn {
                        return Node::Invalid;
                    }
                    if call_noreturn {
                        *noreturn = true;
                    }
                    let function = ctx.hir.add(called_node);

                    Node::Call {
                        function,
                        args,
                        return_ty: expected,
                        arg_types,
                        noreturn: call_noreturn,
                    }
                }
                Err(err) => {
                    ctx.compiler.errors.emit_err(err);
                    ctx.invalidate(expected);
                    Node::Invalid
                }
            }
        }
        TypeInfo::MethodItem {
            module,
            function,
            generics,
        } => {
            let signature = Rc::clone(ctx.compiler.get_signature(module, function));
            // it was already checked that the first argument fits the self parameter correctly
            let signature_params = &signature.params[1..];

            ctx.specify_resolved(expected, &signature.return_type, generics, |ast| {
                ast[expr].span(ast)
            });
            match check_call_args(
                ctx,
                scope,
                return_ty,
                noreturn,
                call_span,
                call.args,
                &call.named_args,
                generics,
                signature_params,
                &signature.named_params,
                signature.varargs,
                true,
            ) {
                Ok((args, arg_types)) => {
                    if *noreturn {
                        return Node::Invalid;
                    }
                    ctx.hir
                        .modify_node(args.iter().next().unwrap(), called_node);
                    let self_type = ctx
                        .hir
                        .types
                        .from_generic_resolved(&signature.params[0].1, generics);
                    ctx.hir
                        .types
                        .replace(arg_types.iter().next().unwrap(), self_type);
                    let call_noreturn =
                        matches!(signature.return_type, Type::Primitive(Primitive::Never));
                    if call_noreturn {
                        *noreturn = true;
                    }

                    Node::Call {
                        function: ctx.hir.add(Node::FunctionItem(module, function, generics)),
                        args,
                        return_ty: expected,
                        arg_types,
                        noreturn: call_noreturn,
                    }
                }
                Err(err) => {
                    ctx.compiler.errors.emit_err(err);
                    ctx.invalidate(expected);
                    Node::Invalid
                }
            }
        }
        TypeInfo::EnumVariantItem {
            enum_type,
            generics,
            ordinal: variant,
            arg_types,
        } => {
            ctx.specify(expected, TypeInfo::TypeDef(enum_type, generics), |ast| {
                ast[expr].span(ast)
            });
            if call.args.count + 1 != arg_types.count {
                ctx.compiler.errors.emit_err(
                    Error::InvalidArgCount {
                        expected: arg_types.count - 1,
                        varargs: false,
                        found: arg_types.count,
                    }
                    .at_span(ctx.span(expr)),
                );
                ctx.invalidate(expected);
                return Node::Invalid;
            }
            let elems = ctx.hir.add_invalid_nodes(arg_types.count);
            let mut elem_iter = elems.iter();
            let mut arg_type_iter = arg_types.iter();
            ctx.hir.modify_node(
                elem_iter.next().unwrap(),
                Node::IntLiteral {
                    val: variant as _,
                    ty: arg_type_iter.next().unwrap(),
                },
            );
            for ((r, arg), ty) in elem_iter.zip(call.args).zip(arg_types.iter()) {
                let node = expr::check(ctx, arg, scope, ty, return_ty, noreturn);
                ctx.hir.modify_node(r, node);
            }
            Node::EnumLiteral {
                elems,
                elem_types: arg_types,
                enum_ty: called_ty,
            }
        }
        TypeInfo::TraitMethodItem {
            module: trait_module,
            trait_id,
            method_index,
        } => {
            let Some(checked_trait) = ctx.compiler.get_checked_trait(trait_module, trait_id) else {
                return Node::Invalid;
            };
            let checked_trait = Rc::clone(checked_trait);
            let signature = &checked_trait.functions[method_index as usize];
            let span = ctx.ast[expr].span(ctx.ast);
            let generics = signature.generics.instantiate(&mut ctx.hir.types, span);
            debug_assert!(
                signature.generics.count() > checked_trait.generics.count(),
                "the method should at least have the trait's and the self type's generics {} >= {}",
                signature.generics.count(),
                checked_trait.generics.count() + 1,
            );
            // generics NOT including the self type
            let trait_generics = LocalTypeIds {
                idx: generics.idx + 1,
                count: checked_trait.generics.count().into(),
            };
            let self_ty = generics.iter().next().unwrap();
            assert!(
                matches!(ctx.hir.types[self_ty], TypeInfo::Unknown),
                "TODO: handle existing self bounds"
            );
            let self_bounds = ctx.hir.types.add_bounds([Bound {
                trait_id: (trait_module, trait_id),
                generics: trait_generics,
                span,
            }]);
            ctx.hir
                .types
                .replace(self_ty, TypeInfo::UnknownSatisfying(self_bounds));
            ctx.specify_resolved(expected, &signature.return_type, generics, |_| span);
            match check_call_args(
                ctx,
                scope,
                return_ty,
                noreturn,
                call_span,
                call.args,
                &call.named_args,
                generics,
                &signature.params,
                &signature.named_params,
                signature.varargs,
                false,
            ) {
                Ok((args, _)) => {
                    let call_noreturn =
                        matches!(signature.return_type, Type::Primitive(Primitive::Never));
                    if call_noreturn {
                        *noreturn = true;
                    }
                    Node::TraitCall {
                        trait_id: (trait_module, trait_id),
                        trait_generics,
                        method_index,
                        self_ty,
                        args,
                        return_ty: expected,
                        noreturn: call_noreturn,
                    }
                }
                Err(err) => {
                    ctx.compiler.errors.emit_err(err);
                    ctx.invalidate(expected);
                    ctx.invalidate(self_ty);
                    Node::Invalid
                }
            }
        }
        TypeInfo::UnknownSatisfying(bounds) => {
            let needed_bound = bounds.iter().next().map(|bound| {
                let trait_id = ctx.hir.types.get_bound(bound).trait_id;
                ctx.compiler
                    .get_trait_name(trait_id.0, trait_id.1)
                    .to_owned()
            });
            ctx.compiler.errors.emit_err(
                Error::TypeMustBeKnownHere { needed_bound }.at_span(ctx.span(call.called_expr)),
            );
            ctx.invalidate(expected);
            Node::Invalid
        }
        TypeInfo::Unknown => {
            ctx.compiler.errors.emit_err(
                Error::TypeMustBeKnownHere { needed_bound: None }
                    .at_span(ctx.span(call.called_expr)),
            );
            ctx.invalidate(expected);
            Node::Invalid
        }
        _ => {
            ctx.compiler
                .errors
                .emit_err(Error::FunctionOrTypeExpected.at_span(ctx.span(call.called_expr)));
            Node::Invalid
        }
    }
}

fn call_arg_types(
    arg_count: u32,
    ctx: &mut Ctx,
    params: &[(Box<str>, Type)],
    named_params: &[(Box<str>, Type, Option<ConstValueId>)],
    generics: LocalTypeIds,
    varargs: bool,
    extra_arg_slot: bool,
) -> Result<LocalTypeIds, Error> {
    // TODO: this function probably breaks with varargs and named args, properly define what combinations are allowed and how
    let invalid_arg_count = if varargs {
        arg_count < params.len() as u32
    } else {
        arg_count != params.len() as u32
    };
    if invalid_arg_count {
        let expected = params.len() as _;
        return Err(Error::InvalidArgCount {
            expected,
            varargs,
            found: arg_count,
        });
    }
    let arg_types = ctx
        .hir
        .types
        .add_multiple_unknown(extra_arg_slot as u32 + arg_count + named_params.len() as u32);
    for (ty, idx) in params
        .iter()
        .map(|(_, ty)| ty)
        .chain(named_params.iter().map(|(_, ty, _)| ty))
        .zip(arg_types.iter().skip(extra_arg_slot as usize))
    {
        let ty = ctx.type_from_resolved(ty, generics);
        ctx.hir.types.replace(idx, ty);
    }
    Ok(arg_types)
}

fn check_call_args(
    ctx: &mut Ctx,
    scope: &mut LocalScope,
    return_ty: LocalTypeId,
    noreturn: &mut bool,
    span: TSpan,
    args: ExprIds,
    named_args: &[(TSpan, ExprId)],
    generics: LocalTypeIds,
    params: &[(Box<str>, Type)],
    named_params: &[(Box<str>, Type, Option<ConstValueId>)],
    varargs: bool,
    extra_arg_slot: bool,
) -> Result<(NodeIds, LocalTypeIds), crate::error::CompileError> {
    let arg_types = call_arg_types(
        args.count,
        ctx,
        params,
        named_params,
        generics,
        varargs,
        extra_arg_slot,
    )
    .map_err(|err| err.at_span(span.in_mod(ctx.module)))?;
    check_call_args_inner(
        ctx,
        scope,
        return_ty,
        noreturn,
        span,
        args,
        named_args,
        params.len() as u32,
        named_params,
        arg_types,
        extra_arg_slot,
    )
}

fn check_call_args_inner(
    ctx: &mut Ctx,
    scope: &mut LocalScope,
    return_ty: LocalTypeId,
    noreturn: &mut bool,
    span: TSpan,
    args: ExprIds,
    named_args: &[(TSpan, ExprId)],
    param_count: u32,
    named_params: &[(Box<str>, Type, Option<ConstValueId>)],
    arg_types: LocalTypeIds,
    extra_arg_slot: bool,
) -> Result<(NodeIds, LocalTypeIds), crate::error::CompileError> {
    let all_arg_nodes = ctx.hir.add_invalid_nodes(arg_types.count);
    let arg_nodes = if extra_arg_slot {
        all_arg_nodes.skip(1)
    } else {
        all_arg_nodes
    };

    let param_arg_types = arg_types.skip(extra_arg_slot as u32);

    // iterating over the signature, all extra arguments in case of vararg
    // arguments will stay unknown which is intended
    for ((arg, node_idx), ty) in args
        .into_iter()
        .zip(
            arg_nodes.iter().take(param_count as usize).chain(
                arg_nodes
                    .iter()
                    .skip(param_count as usize + named_args.len()),
            ),
        )
        .zip(
            param_arg_types.iter().take(param_count as usize).chain(
                param_arg_types
                    .iter()
                    .skip(param_count as usize + named_args.len()),
            ),
        )
    {
        let node = expr::check(ctx, arg, scope, ty, return_ty, noreturn);
        if *noreturn {
            return Ok((all_arg_nodes, param_arg_types));
        }
        ctx.hir.modify_node(node_idx, node);
    }

    for (name_span, value) in named_args {
        let name = &ctx.ast[*name_span];
        let Some(i) = named_params
            .iter()
            .position(|(arg_name, _, _)| &**arg_name == name)
        else {
            ctx.compiler
                .errors
                .emit_err(Error::NonexistantNamedArg.at_span(name_span.in_mod(ctx.module)));
            // still check the expr with an unknown expected type
            let ty = ctx.hir.types.add_unknown();
            expr::check(ctx, *value, scope, ty, return_ty, noreturn);
            if *noreturn {
                return Ok((all_arg_nodes, arg_types));
            }
            continue;
        };
        let node_idx = arg_nodes.iter().nth(param_count as usize + i).unwrap();
        let ty = param_arg_types.nth(param_count + i as u32).unwrap();
        let node = expr::check(ctx, *value, scope, ty, return_ty, noreturn);
        if *noreturn {
            return Ok((all_arg_nodes, arg_types));
        }
        ctx.hir.modify_node(node_idx, node);
    }

    let mut missing_named_args = Vec::new();
    for ((name, _, default_val), (node_id, ty)) in named_params.iter().zip(
        arg_nodes
            .iter()
            .zip(param_arg_types.iter())
            .skip(param_count as usize),
    ) {
        if matches!(ctx.hir[node_id], Node::Invalid) {
            let Some(default_val) = *default_val else {
                missing_named_args.push(name.clone());
                continue;
            };
            ctx.hir.modify_node(
                node_id,
                Node::Const {
                    id: default_val,
                    ty,
                },
            );
        }
    }
    if !missing_named_args.is_empty() {
        return Err(Error::MissingNamedArgs {
            names: missing_named_args.into_boxed_slice(),
        }
        .at_span(span.in_mod(ctx.module)));
    }
    debug_assert_eq!(all_arg_nodes.count, arg_types.count);
    Ok((all_arg_nodes, arg_types))
}

fn check_struct_initializer(
    ctx: &mut Ctx,
    struct_def: &ResolvedStructDef,
    generics: LocalTypeIds,
    call: &Call,
    scope: &mut LocalScope,
    return_ty: LocalTypeId,
    noreturn: &mut bool,
) -> Result<Node, ()> {
    let span = TSpan::new(call.open_paren_start, call.end);
    match check_call_args(
        ctx,
        scope,
        return_ty,
        noreturn,
        span,
        call.args,
        &call.named_args,
        generics,
        &struct_def.fields,
        &struct_def.named_fields,
        false,
        false,
    ) {
        Ok((elems, elem_types)) => Ok(Node::TupleLiteral { elems, elem_types }),
        Err(err) => {
            ctx.compiler.errors.emit_err(err);
            Err(())
        }
    }
}
