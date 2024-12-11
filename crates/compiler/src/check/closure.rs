use std::{cell::RefCell, rc::Rc};

use id::ConstValueId;
use indexmap::IndexMap;
use span::TSpan;
use types::Type;

use crate::{
    compiler::{CheckedFunction, LocalScope, LocalScopeParent, Signature},
    error::Error,
    hir::{HIRBuilder, Node},
    parser::ast::FunctionId,
    types::{LocalTypeId, TypeInfo, TypeInfoOrIdx, TypeTable},
};

use super::Ctx;

pub fn closure(
    ctx: &mut Ctx<'_>,
    id: FunctionId,
    expected: LocalTypeId,
    closed_over: &mut LocalScope,
    closure_span: TSpan,
) -> Node {
    let function = &ctx.ast[id];
    let body = function
        .body
        .expect("TODO: handle/error on extern closures");
    let generics =
        ctx.compiler
            .resolve_generics(&function.generics, ctx.module, function.scope, ctx.ast);
    let mut types = TypeTable::new();

    let name = crate::compiler::function_name(ctx.ast, function, ctx.module, id);

    let param_types = types
        .add_multiple_unknown(1 + (function.params.len() + function.named_params.len()) as u32);
    for ((_, param), r) in function.params.iter().zip(param_types.iter().skip(1)) {
        let info = types.info_from_unresolved(param, ctx.compiler, ctx.module, function.scope);
        let i = TypeInfoOrIdx::TypeInfo(info);
        types.replace(r, i);
    }

    for ((_, ty, _), r) in function
        .named_params
        .iter()
        .zip(param_types.iter().skip(1 + function.params.len()))
    {
        let info = types.info_from_unresolved(ty, ctx.compiler, ctx.module, function.scope);
        types.replace(r, TypeInfoOrIdx::TypeInfo(info));
    }

    let return_type = types.info_from_unresolved(
        &function.return_type,
        ctx.compiler,
        ctx.module,
        function.scope,
    );
    let return_type = types.add(return_type);
    let varargs = function.varargs;
    let params = function
        .params
        .iter()
        .map(|(name_span, _)| name_span)
        .chain(
            function
                .named_params
                .iter()
                .map(|(name_span, _, _)| name_span),
        )
        .map(|name_span| ctx.ast.src()[name_span.range()].to_owned().into_boxed_str())
        .zip(param_types.iter().skip(1));
    // TODO: replace with proper type?
    let captures_ty = param_types.nth(0).unwrap();
    let mut hir = HIRBuilder::new(types);
    let _captures_arg = hir.add_var(captures_ty);
    let mut captures = RefCell::new(IndexMap::new());
    let (hir, types) = super::check(
        ctx.compiler,
        ctx.ast,
        ctx.module,
        &generics,
        function.scope,
        hir,
        params,
        body,
        return_type,
        LocalScopeParent::ClosedOver {
            scope: &mut *closed_over,
            captures: &mut captures,
        },
    );

    let captures = captures.into_inner();
    let capture_count = captures.len() as _;
    let capture_nodes = ctx.hir.add_invalid_nodes(capture_count);
    let capture_infos = ctx.hir.types.add_multiple_unknown(capture_count);
    let capture_types: Box<[Type]> = captures
        .into_iter()
        .zip(capture_nodes.iter())
        .zip(capture_infos.iter())
        .map(|(((var, _), node), ty)| {
            ctx.hir.modify_node(node, Node::Variable(var));
            let idx = ctx.hir.get_var(var);
            ctx.hir.types.replace(ty, TypeInfoOrIdx::Idx(idx));
            ctx.hir
                .types
                .to_generic_resolved(ctx.hir.types[idx])
                .unwrap_or_else(|()| {
                    // TODO: span of the variable accesss (could put into captures)
                    // only if we really need to fully know the captured type here
                    ctx.compiler.errors.emit_err(
                        Error::TypeMustBeKnownHere { needed_bound: None }
                            .at_span(TSpan::EMPTY.in_mod(ctx.module)),
                    );
                    Type::Invalid
                })
        })
        .collect();

    let other_params = param_types
        .iter()
        .skip(1)
        .take(function.params.len())
        .zip(&function.params)
        .map(|(id, (span, _))| {
            let name = ctx.ast.src()[span.range()].to_owned().into_boxed_str();
            let ty = types.to_generic_resolved(types[id]).unwrap_or_else(|()| {
                let mut ty = String::new();
                types.type_to_string(ctx.compiler, types[id], &mut ty);
                ctx.compiler
                    .errors
                    .emit_err(Error::CantInferFromBody { ty }.at_span(span.in_mod(ctx.module)));
                Type::Invalid
            });
            (name, ty)
        });
    let params = if capture_types.is_empty() {
        other_params.collect()
    } else {
        let captures_parameter = Type::Tuple(capture_types);
        std::iter::once((String::new().into_boxed_str(), captures_parameter))
            .chain(other_params)
            .collect()
    };
    let named_params = param_types
        .iter()
        .skip(1 + function.params.len())
        .zip(&function.named_params)
        .map(|(id, (name_span, _, default_val))| {
            let name = ctx.ast.src()[name_span.range()].to_owned().into_boxed_str();
            let ty = types.to_generic_resolved(types[id]).unwrap_or_else(|()| {
                let mut ty = String::new();
                types.type_to_string(ctx.compiler, types[id], &mut ty);
                ctx.compiler.errors.emit_err(
                    Error::CantInferFromBody { ty }.at_span(name_span.in_mod(ctx.module)),
                );
                Type::Invalid
            });
            // TODO: const value
            if default_val.is_some() {
                todo!("handle default values in closures")
            }
            let a: Option<ConstValueId> = None;
            (name, ty, a)
        })
        .collect();
    let signature_return_type = types
        .to_generic_resolved(types[return_type])
        .unwrap_or_else(|()| {
            let mut ty = String::new();
            types.type_to_string(ctx.compiler, types[return_type], &mut ty);
            ctx.compiler.errors.emit_err(
                Error::CantInferFromBody { ty }
                    .at_span(function.return_type.span().in_mod(ctx.module)),
            );
            Type::Invalid
        });
    let generic_instance = generics.instantiate(&mut ctx.hir.types, closure_span);
    let symbols = &mut ctx.compiler.get_parsed_module(ctx.module).symbols;
    symbols.functions[id.0 as usize].put(Rc::new(CheckedFunction {
        name,
        types,
        params: param_types,
        varargs,
        return_type,
        generic_count: generics.count(),
        body: Some(hir),
    }));
    symbols.function_signatures[id.0 as usize].put(Rc::new(Signature {
        params,
        named_params,
        varargs,
        return_type: signature_return_type,
        generics,
        span: function.signature_span,
    }));
    if capture_nodes.is_empty() {
        ctx.specify(
            expected,
            TypeInfo::FunctionItem {
                module: ctx.module,
                function: id,
                generics: generic_instance,
            },
            |_| closure_span,
        );
        Node::Unit
    } else {
        ctx.specify(
            expected,
            TypeInfo::MethodItem {
                module: ctx.module,
                function: id,
                generics: generic_instance,
            },
            |_| closure_span,
        );
        Node::TupleLiteral {
            elems: capture_nodes,
            elem_types: capture_infos,
        }
    }
}
