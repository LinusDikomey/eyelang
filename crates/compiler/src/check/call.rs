use crate::types::{BaseType, BuiltinType, TypeFull};
use crate::{InvalidTypeError, Type};
use crate::{
    compiler::{LocalScope, ResolvedStructDef, ResolvedTypeContent, builtins},
    eval::ConstValueId,
    hir::{Node, NodeIds},
    typing::{Bound, LocalTypeId, LocalTypeIds, TypeInfo, TypeInfoOrIdx},
};
use error::{Error, span::TSpan};
use parser::ast::{Ast, Call, ExprId, ExprIds};

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
    let mut base_type_called = |ctx: &mut Ctx, base: BaseType, instance: LocalTypeIds| {
        let resolved = ctx.compiler.get_base_type_def(base);
        match &resolved.def {
            ResolvedTypeContent::Struct(struct_def) => {
                ctx.specify(expected, TypeInfo::Instance(base, instance), |ast| {
                    ast[expr].span(ast)
                });
                check_struct_initializer(
                    ctx, struct_def, instance, call, scope, return_ty, noreturn,
                )
                .unwrap_or_else(|_| {
                    ctx.invalidate(expected);
                    Node::Invalid
                })
            }
            ResolvedTypeContent::Builtin(_) | ResolvedTypeContent::Enum(_) => {
                ctx.emit(Error::FunctionOrStructTypeExpected.at_span(ctx.span(expr)));
                Node::Invalid
            }
        }
    };

    let mut s = String::new();
    ctx.hir.types.type_to_string_inner(
        ctx.compiler,
        ctx.generics,
        ctx.hir.types[called_ty],
        &mut s,
    );

    match ctx.hir.types[called_ty] {
        TypeInfo::Known(Type::Invalid) => {
            ctx.invalidate(expected);
            return Node::Invalid;
        }
        TypeInfo::BaseTypeItem(base) => {
            debug_assert!(
                !matches!(
                    ctx.compiler.get_base_type_def(base).def,
                    ResolvedTypeContent::Builtin(BuiltinType::Tuple | BuiltinType::Function)
                ),
                "tuple/function base type should not be possible to obtain"
            );
            let generic_count = ctx.compiler.get_base_type_generic_count(base);
            let base_generics = ctx.hir.types.add_multiple_unknown(generic_count.into());
            return base_type_called(ctx, base, base_generics);
        }
        TypeInfo::TypeItem(ty) => {
            match ctx.hir.types[ty] {
                TypeInfo::Instance(BaseType::Invalid, _) => {
                    ctx.invalidate(expected);
                    return Node::Invalid;
                }
                TypeInfo::Unknown(bounds) => {
                    ctx.emit_unknown(bounds, ctx.span(call.called_expr));
                    ctx.invalidate(expected);
                    return Node::Invalid;
                }
                TypeInfo::Instance(base, instance_generics) => {
                    return base_type_called(ctx, base, instance_generics);
                }
                TypeInfo::Known(ty) => {
                    if let TypeFull::Instance(base, generics) = ctx.compiler.types.lookup(ty) {
                        let generics = ctx
                            .hir
                            .types
                            .add_multiple(generics.iter().map(|&ty| TypeInfo::Known(ty)));
                        return base_type_called(ctx, base, generics);
                    }
                }
                _ => {}
            };
        }
        TypeInfo::FunctionItem {
            module,
            function,
            generics,
        } => {
            let signature = ctx.compiler.get_signature(module, function);
            let function = ctx.hir.add(Node::FunctionItem(module, function, generics));
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
                Ok((args, arg_types)) => {
                    if *noreturn {
                        return Node::Invalid;
                    }
                    // TODO: figure out noreturn checking, maybe after typecheck is done?
                    let return_info = ctx.hir.types.from_type_instance(
                        &ctx.compiler.types,
                        signature.return_type,
                        generics,
                    );
                    let return_var = ctx.hir.types.add_info_or_idx(return_info);
                    let call_noreturn = ctx
                        .hir
                        .types
                        .is_uninhabited(ctx.compiler, ctx.hir.types[return_var]);
                    match call_noreturn {
                        Ok(true) => *noreturn = true,
                        Ok(false) => {
                            ctx.unify(expected, return_var, |ast: &Ast| ast[expr].span(ast));
                        }
                        Err(InvalidTypeError) => {
                            ctx.invalidate(expected);
                        }
                    }

                    return Node::Call {
                        function,
                        args,
                        return_ty: return_var,
                        arg_types,
                        noreturn: *noreturn,
                    };
                }
                Err(err) => {
                    ctx.emit(err);
                    ctx.invalidate(expected);
                    return Node::Invalid;
                }
            }
        }
        TypeInfo::Instance(BaseType::Function, generics) => {
            return function_type_call(
                ctx,
                generics,
                call,
                called_node,
                call_span,
                scope,
                expected,
                return_ty,
                noreturn,
            );
        }
        TypeInfo::Known(ty) => {
            if let TypeFull::Instance(BaseType::Function, generics) = ctx.compiler.types.lookup(ty)
            {
                let generics = ctx
                    .hir
                    .types
                    .add_multiple(generics.iter().copied().map(TypeInfo::Known));
                return function_type_call(
                    ctx,
                    generics,
                    call,
                    called_node,
                    call_span,
                    scope,
                    expected,
                    return_ty,
                    noreturn,
                );
            }
        }
        TypeInfo::MethodItem {
            module,
            function,
            generics,
        } => {
            let signature = ctx.compiler.get_signature(module, function);
            // it was already checked that the first argument fits the self parameter correctly
            let signature_params = &signature.params[1..];

            ctx.specify_resolved(expected, signature.return_type, generics, |ast| {
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
                    let self_type = ctx.hir.types.from_type_instance(
                        &ctx.compiler.types,
                        signature.params[0].1,
                        generics,
                    );
                    ctx.hir
                        .types
                        .replace(arg_types.iter().next().unwrap(), self_type);
                    // TODO: figure out noreturn checking
                    /*
                    let call_noreturn = matches!(
                        ctx.compiler.uninhabited(&signature.return_type, generics),
                        Ok(true)
                    );
                    if call_noreturn {
                        *noreturn = true;
                    }
                    */

                    return Node::Call {
                        function: ctx.hir.add(Node::FunctionItem(module, function, generics)),
                        args,
                        return_ty: expected,
                        arg_types,
                        noreturn: false, // TODO
                    };
                }
                Err(err) => {
                    ctx.emit(err);
                    ctx.invalidate(expected);
                    return Node::Invalid;
                }
            }
        }
        TypeInfo::EnumVariantItem {
            enum_type,
            generics,
            ordinal: variant,
            arg_types,
        } => {
            ctx.specify(expected, TypeInfo::Instance(enum_type, generics), |ast| {
                ast[expr].span(ast)
            });
            if call.args.count + 1 != arg_types.count {
                ctx.emit(
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
            return Node::EnumLiteral {
                elems,
                elem_types: arg_types,
                enum_ty: called_ty,
            };
        }
        TypeInfo::TraitMethodItem {
            module: trait_module,
            trait_id,
            method_index,
        } => {
            let Some(checked_trait) = ctx.compiler.get_checked_trait(trait_module, trait_id) else {
                return Node::Invalid;
            };
            let signature = &checked_trait.functions[method_index as usize];
            let span = ctx.ast[expr].span(ctx.ast);
            let generics =
                signature
                    .generics
                    .instantiate(&mut ctx.hir.types, &ctx.compiler.types, span);
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
                matches!(ctx.hir.types[self_ty], TypeInfo::Unknown(bounds) if bounds.is_empty()),
                "TODO: handle existing self bounds"
            );
            let self_bounds = ctx.hir.types.add_bounds([Bound {
                trait_id: (trait_module, trait_id),
                generics: trait_generics,
                span,
            }]);
            ctx.hir
                .types
                .replace(self_ty, TypeInfo::Unknown(self_bounds));
            ctx.specify_resolved(expected, signature.return_type, generics, |_| span);
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
                    /*
                    let call_noreturn = matches!(
                        ctx.compiler
                            .uninhabited(&signature.return_type, generics),
                        Ok(true)
                    );
                    if call_noreturn {
                        *noreturn = true;
                    }
                    */
                    return Node::TraitCall {
                        trait_id: (trait_module, trait_id),
                        trait_generics,
                        method_index,
                        self_ty,
                        args,
                        return_ty: expected,
                        noreturn: false, // call_noreturn, // TODO
                    };
                }
                Err(err) => {
                    ctx.emit(err);
                    ctx.invalidate(expected);
                    ctx.invalidate(self_ty);
                    return Node::Invalid;
                }
            }
        }
        _ => {}
    }

    // TODO: auto ref/deref on called value
    let arg_types = ctx.hir.types.add_multiple_unknown(call.args.len() as _);
    let fn_instance = ctx.hir.types.add_multiple_info_or_idx([
        TypeInfoOrIdx::TypeInfo(TypeInfo::Instance(BaseType::Tuple, arg_types)),
        expected.into(),
    ]);
    assert_eq!(
        call.named_args.len(),
        0,
        "TODO: support named args in trait calls or error properly"
    );

    let fn_trait = builtins::get_fn_trait(ctx.compiler);
    let fn_bound = Bound {
        trait_id: fn_trait,
        generics: fn_instance,
        span: call_span,
    };
    ctx.specify_bound(called_ty, fn_bound, ctx.span(call.called_expr));

    let arg_nodes = ctx.hir.add_invalid_nodes(arg_types.count);
    for ((arg, ty), node_id) in call
        .args
        .into_iter()
        .zip(arg_types.iter())
        .zip(arg_nodes.iter())
    {
        let node = expr::check(ctx, arg, scope, ty, return_ty, noreturn);
        ctx.hir.modify_node(node_id, node);
        if *noreturn {
            return Node::Invalid;
        }
    }
    let fn_args = ctx.hir.add_nodes([
        called_node,
        Node::TupleLiteral {
            elems: arg_nodes,
            elem_types: arg_types,
        },
    ]);
    Node::TraitCall {
        trait_id: fn_trait,
        trait_generics: fn_instance,
        method_index: 0,
        self_ty: called_ty,
        args: fn_args,
        return_ty: expected,
        noreturn: false,
    }
}

fn function_type_call(
    ctx: &mut Ctx,
    function_generics: LocalTypeIds,
    call: &Call,
    called_node: Node,
    call_span: TSpan,
    scope: &mut LocalScope,
    expected: LocalTypeId,
    return_ty: LocalTypeId,
    noreturn: &mut bool,
) -> Node {
    let return_type = function_generics.nth(0).unwrap();
    let params = function_generics.skip(1);
    // TODO: call noreturn checking
    let call_noreturn = false;
    // let call_noreturn = matches!(
    //     ctx.compiler.uninhabited(
    //         &ctx.hir
    //             .types
    //             .to_generic_resolved(ctx.hir.types[return_type])
    //             .unwrap_or(TypeOld::Invalid),
    //         &[], // TODO: this will probably cause issues, need to be able to not pass in generics?
    //     ),
    //     Ok(true)
    // );
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
                noreturn: false, // TODO: call_noreturn,
            }
        }
        Err(err) => {
            ctx.emit(err);
            ctx.invalidate(expected);
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
    let arg_type_vars = ctx
        .hir
        .types
        .add_multiple_unknown(extra_arg_slot as u32 + arg_count + named_params.len() as u32);
    for (&ty, var) in params
        .iter()
        .map(|(_, ty)| ty)
        .chain(named_params.iter().map(|(_, ty, _)| ty))
        .zip(arg_type_vars.iter().skip(extra_arg_slot as usize))
    {
        let ty = ctx.from_type_instance(ty, generics);
        ctx.hir.types.replace(var, ty);
    }
    Ok(arg_type_vars)
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
) -> Result<(NodeIds, LocalTypeIds), error::CompileError> {
    let arg_types = call_arg_types(
        args.count,
        ctx,
        params,
        named_params,
        generics,
        varargs,
        extra_arg_slot,
    )
    .map_err(|err| err.at_span(span))?;
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
) -> Result<(NodeIds, LocalTypeIds), error::CompileError> {
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

    for &(name_span, value) in named_args {
        let name = &ctx.ast[name_span];
        let Some(i) = named_params
            .iter()
            .position(|(arg_name, _, _)| &**arg_name == name)
        else {
            ctx.emit(Error::NonexistantNamedArg.at_span(name_span));
            // still check the expr with an unknown expected type
            let ty = ctx.hir.types.add_unknown();
            expr::check(ctx, value, scope, ty, return_ty, noreturn);
            if *noreturn {
                return Ok((all_arg_nodes, arg_types));
            }
            continue;
        };
        let node_idx = arg_nodes.iter().nth(param_count as usize + i).unwrap();
        let ty = param_arg_types.nth(param_count + i as u32).unwrap();
        let node = expr::check(ctx, value, scope, ty, return_ty, noreturn);
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
        .at_span(span));
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
            ctx.emit(err);
            Err(())
        }
    }
}
