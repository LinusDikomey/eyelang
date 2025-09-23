#![allow(unused)] // TODO NOCHECKIN: remove this unused
use std::{cell::RefCell, rc::Rc};

use crate::{
    eval::ConstValueId,
    types::{BaseType, TypeOld},
};
use error::{Error, span::TSpan};
use indexmap::IndexMap;

use crate::{
    compiler::{CheckedFunction, LocalScope, LocalScopeParent, Signature},
    hir::{HIRBuilder, Node},
    typing::{TypeInfo, TypeInfoOrIdx, TypeTable},
};
use parser::ast::FunctionId;

use super::Ctx;

pub fn closure(
    ctx: &mut Ctx<'_>,
    id: FunctionId,
    closed_over: &mut LocalScope,
    closure_span: TSpan,
) -> (Node, TypeInfo) {
    todo!("reimplement closures")
    /*
    let function = &ctx.ast[id];
    let body = function
        .body
        .expect("TODO: handle/error on extern closures");
    let generics = ctx.compiler.resolve_generics(
        &function.generics.types,
        ctx.module,
        function.scope,
        ctx.ast,
    );

    let name = crate::compiler::function_name(ctx.ast, function, ctx.module, id);

    let param_types = ctx
        .hir
        .types
        .add_multiple_unknown(1 + (function.params.len() + function.named_params.len()) as u32);

    for (param_ty, r) in function
        .params
        .iter()
        .map(|(_, ty)| ty)
        .chain(function.named_params.iter().map(|(_, ty, _)| ty))
        .zip(param_types.iter())
    {
        let info =
            ctx.hir
                .types
                .info_from_unresolved(param_ty, ctx.compiler, ctx.module, function.scope);
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

    let param_names = function
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

    let mut hir = HIRBuilder::new(ctx.hir.types);

    let captures_ty = param_types.nth(0).unwrap();
    let captures_param = hir.add_var(captures_ty);

    let mut captures = RefCell::new(IndexMap::new());

    let (mut hir, mut types) = super::check(
        ctx.compiler,
        ctx.ast,
        ctx.module,
        &generics,
        function.scope,
        hir,
        param_names,
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
    // let outside_capture_infos = ctx.hir.types.add_multiple_unknown(capture_count);
    // let capture_types: Box<[TypeOld]> = captures
    //     .into_iter()
    //     .zip(capture_nodes.iter())
    //     .zip(outside_capture_infos.iter())
    //     .map(|(((var, _), node), outside_id)| {
    //         ctx.hir.modify_node(node, Node::Variable(var));
    //         let idx = ctx.hir.get_var(var);
    //         ctx.hir.types.replace(outside_id, TypeInfoOrIdx::Idx(idx));
    //         // TODO: probably don't want a type with outer generics here or have to handle it
    //         // properly by allowing the closure to inherit outer generics
    //         ctx.hir
    //             .types
    //             .to_generic_resolved(ctx.hir.types[idx])
    //             .unwrap_or_else(|()| {
    //                 // TODO: span of the variable accesss (could put into captures)
    //                 // only if we really need to fully know the captured type here
    //                 ctx.emit(
    //                     Error::TypeMustBeKnownHere { needed_bound: None }.at_span(TSpan::EMPTY),
    //                 );
    //                 TypeOld::Invalid
    //             })
    //     })
    //     .collect();
    // let inside_capture_infos = types.multiple_from_generic_resolved_internal(&capture_types, None);
    types.replace(
        captures_ty,
        TypeInfo::Instance(BaseType::Tuple, inside_capture_infos),
    );
    let mut s = String::new();
    types.type_to_string(ctx.compiler, types[captures_ty], &mut s);

    let other_params = param_types
        .iter()
        .skip(1)
        .take(function.params.len())
        .zip(&function.params)
        .map(|(id, &(span, _))| {
            let name = ctx.ast.src()[span.range()].to_owned().into_boxed_str();
            let ty = types.to_generic_resolved(types[id]).unwrap_or_else(|()| {
                let mut ty = String::new();
                types.type_to_string(ctx.compiler, types[id], &mut ty);
                ctx.emit(Error::CantInferFromBody { ty }.at_span(span));
                TypeOld::Invalid
            });
            (name, ty)
        });

    let (params, param_types) = if capture_types.is_empty() {
        (other_params.collect(), param_types.skip(1))
    } else {
        hir.params.insert(0, captures_param);
        let captures_parameter = TypeOld::Tuple(capture_types.clone());
        let params_including_captures =
            std::iter::once((String::new().into_boxed_str(), captures_parameter))
                .chain(other_params)
                .collect();
        (params_including_captures, param_types)
    };

    let named_params = param_types
        .iter()
        .skip(1 + function.params.len())
        .zip(&function.named_params)
        .map(|(id, &(name_span, _, default_val))| {
            let name = ctx.ast.src()[name_span.range()].to_owned().into_boxed_str();
            let ty = types.to_generic_resolved(types[id]).unwrap_or_else(|()| {
                let mut ty = String::new();
                types.type_to_string(ctx.compiler, types[id], &mut ty);
                ctx.emit(Error::CantInferFromBody { ty }.at_span(name_span));
                TypeOld::Invalid
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
            ctx.emit(Error::CantInferFromBody { ty }.at_span(function.return_type.span()));
            TypeOld::Invalid
        });
    let generic_instance = generics.instantiate(&mut ctx.hir.types, closure_span);
    let symbols = &mut ctx.compiler.get_parsed_module(ctx.module).symbols;
    symbols.functions[id.idx()].put(Rc::new(CheckedFunction {
        name,
        types,
        params: param_types,
        varargs,
        return_type,
        generic_count: generics.count(),
        body: Some(hir),
    }));
    symbols.function_signatures[id.idx()].put(Rc::new(Signature {
        params,
        named_params,
        varargs,
        return_type: signature_return_type,
        generics,
        span: function.signature_span,
    }));
    if capture_nodes.is_empty() {
        (
            Node::FunctionItem(ctx.module, id, generic_instance),
            TypeInfo::FunctionItem {
                module: ctx.module,
                function: id,
                generics: generic_instance,
            },
        )
    } else {
        let capture_infos = ctx
            .hir
            .types
            .multiple_from_generic_resolved_internal(&capture_types, Some(generic_instance));
        (
            Node::TupleLiteral {
                elems: capture_nodes,
                elem_types: capture_infos,
            },
            TypeInfo::MethodItem {
                module: ctx.module,
                function: id,
                generics: generic_instance,
            },
        )
    }
    */
}
