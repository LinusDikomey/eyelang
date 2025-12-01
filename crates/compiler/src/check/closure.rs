#![allow(unused)] // TODO: remove this unused after implementing closures again
use std::{cell::RefCell, rc::Rc};

use crate::{
    check::expr,
    compiler::{Generics, VarId},
    eval::ConstValueId,
    types::BaseType,
    typing::{LocalTypeId, LocalTypeIds},
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

pub struct CheckedClosure {
    pub id: FunctionId,
    pub hir: HIRBuilder,
    pub generics: Generics,
    pub root: Node,
    pub params: Box<[(Box<str>, VarId)]>,
    pub param_types: LocalTypeIds,
    pub return_type: LocalTypeId,
}

pub fn closure(
    ctx: &mut Ctx<'_>,
    id: FunctionId,
    closed_over: &mut LocalScope,
    closure_span: TSpan,
) -> (Node, TypeInfo) {
    let function = &ctx.ast[id];
    let body = function
        .body
        .expect("TODO: handle extern functions in expr position just like normal externs");
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
    let captures_ty = param_types.nth(0).unwrap();

    for (param_ty, r) in function
        .params
        .iter()
        .map(|(_, ty)| ty)
        .chain(function.named_params.iter().map(|param| &param.ty))
        .zip(param_types.iter().skip(1))
    {
        let info =
            ctx.hir
                .types
                .from_annotation(param_ty, ctx.compiler, ctx.module, function.scope);
        ctx.hir.types.replace(r, TypeInfoOrIdx::TypeInfo(info));
    }

    let return_type = ctx.hir.types.from_annotation(
        &function.return_type,
        ctx.compiler,
        ctx.module,
        function.scope,
    );
    let return_type = ctx.hir.types.add(return_type);
    let varargs = function.varargs;

    let param_names = function
        .params
        .iter()
        .map(|(name_span, _)| name_span)
        .chain(function.named_params.iter().map(|param| &param.name))
        .map(|name_span| ctx.ast.src()[name_span.range()].to_owned().into_boxed_str())
        .zip(param_types.iter().skip(1));

    let mut captures = RefCell::new(IndexMap::new());
    assert_eq!(
        function.generics.count(),
        0,
        "TODO: handle generics in closures/functions in expr position",
    );
    assert!(
        function.named_params.is_empty(),
        "TODO: handle named params in closures/functions in expr position",
    );

    let types = std::mem::take(&mut ctx.hir.types);
    let (closure_hir, root, captures_param, params) = {
        // TODO: maybe simplify by just swapping out the HirBuilder and maybe the generics later
        let mut inner_ctx = Ctx {
            compiler: ctx.compiler,
            ast: ctx.ast,
            module: ctx.module,
            generics: ctx.generics, // TODO: handle generic inner functions
            hir: HIRBuilder::new(types),
            control_flow_stack: Vec::new(),
            deferred_exhaustions: Vec::new(),
            deferred_casts: Vec::new(),
            checked_closures: Vec::new(),
        };
        let params: Box<[(Box<str>, VarId)]> = param_names
            .map(|(name, ty)| (name, inner_ctx.hir.add_var(ty)))
            .collect();
        let variables = params
            .iter()
            .map(|(name, var)| (name.clone(), *var))
            .collect();
        let mut scope = LocalScope {
            parent: LocalScopeParent::ClosedOver {
                scope: closed_over,
                captures: &captures,
                outer_vars: &ctx.hir.vars,
            },
            variables,
            module: ctx.module,
            static_scope: Some(function.scope),
        };

        let captures_param = inner_ctx.hir.add_var(captures_ty);

        let root = expr::check(
            &mut inner_ctx,
            body,
            &mut scope,
            return_type,
            return_type,
            &mut false,
        );

        ctx.control_flow_stack.extend(inner_ctx.control_flow_stack);
        ctx.deferred_exhaustions
            .extend(inner_ctx.deferred_exhaustions);
        ctx.deferred_casts.extend(inner_ctx.deferred_casts);
        ctx.checked_closures.extend(inner_ctx.checked_closures);
        ctx.hir.types = std::mem::take(&mut inner_ctx.hir.types);
        (inner_ctx.hir, root, captures_param, params)
    };

    let captures = captures.into_inner();
    let capture_count = captures.len() as _;
    let capture_nodes = ctx.hir.add_invalid_nodes(capture_count);
    // let outside_capture_infos = ctx.hir.types.add_multiple_unknown(capture_count);
    let capture_types = ctx.hir.types.add_multiple_unknown(capture_count);
    for (((var, _), node), id) in captures
        .into_iter()
        .zip(capture_nodes.iter())
        .zip(capture_types.iter())
    {
        ctx.hir.modify_node(node, Node::Variable(var));
        let var = ctx.hir.get_var(var);
        ctx.hir.types.replace(id, var);
    }
    ctx.hir.types.replace(
        captures_ty,
        TypeInfo::Instance(BaseType::Tuple, capture_types),
    );

    let params = std::iter::once(("".into(), captures_param))
        .chain(params)
        .collect();

    let checked = CheckedClosure {
        id,
        generics,
        hir: closure_hir,
        root,
        params,
        param_types,
        return_type,
    };
    debug_assert_eq!(checked.params.len(), param_types.count as usize);
    ctx.checked_closures.push(checked);

    // pass the inherited generics into the closure invocation
    // TODO: chain the closure's generic here as Unknown types
    let generics_instance = ctx
        .hir
        .types
        .add_multiple((0..ctx.generics.count()).map(|i| {
            TypeInfo::Known(
                ctx.compiler
                    .types
                    .intern(crate::types::TypeFull::Generic(i)),
            )
        }));
    let params_tuple = ctx
        .hir
        .types
        .add(TypeInfo::Instance(BaseType::Tuple, param_types.skip(1)));
    (
        Node::TupleLiteral {
            elems: capture_nodes,
            elem_types: capture_types,
        },
        TypeInfo::Closure {
            function: id,
            captures: capture_types,
            generics: generics_instance,
            params: params_tuple,
            return_type,
        },
    )
    // }
}
