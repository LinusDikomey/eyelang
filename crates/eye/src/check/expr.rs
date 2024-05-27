use std::rc::Rc;

use id::{ModuleId, TypeId};
use span::TSpan;
use types::{Primitive, Type};

use crate::{
    compiler::{builtins, Def, LocalItem, LocalScope, ResolvedStructDef, ResolvedTypeDef},
    error::Error,
    eval::ConstValue,
    hir::{self, Comparison, Node},
    parser::{
        ast::{Ast, Call, Expr, ExprExtra, ExprId, FunctionId, UnOp},
        token::{FloatLiteral, IntLiteral, Operator},
    },
    type_table::{LocalTypeId, LocalTypeIds, TypeInfo, VariantId},
};

use super::{exhaust::Exhaustion, lval, pattern, Ctx};

pub fn check(
    ctx: &mut Ctx,
    expr: ExprId,
    scope: &mut LocalScope,
    expected: LocalTypeId,
    return_ty: LocalTypeId,
) -> Node {
    let ast = ctx.ast;
    match &ast[expr] {
        &Expr::Block {
            scope: static_scope,
            items,
        } => {
            let mut scope = LocalScope {
                parent: Some(scope),
                variables: dmap::new(),
                module: scope.module,
                static_scope: Some(static_scope),
            };
            // PERF: should preallocate in nodes list and put them in directly
            let items = items
                .into_iter()
                .map(|item| {
                    let unknown = ctx.hir.types.add_unknown();
                    check(ctx, item, &mut scope, unknown, return_ty)
                })
                .collect::<Vec<_>>();
            Node::Block(ctx.hir.add_nodes(items))
        }
        &Expr::Nested(_, inner) => check(ctx, inner, scope, expected, return_ty),

        &Expr::Unit(span) => {
            ctx.specify(expected, TypeInfo::Primitive(Primitive::Unit), |_| span);
            Node::Unit
        }
        &Expr::IntLiteral(span) => {
            let lit = IntLiteral::parse(&ast.src()[span.range()]);
            let info = lit
                .ty
                .map_or(TypeInfo::Integer, |int| TypeInfo::Primitive(int.into()));
            ctx.specify(expected, info, |_| span);
            Node::IntLiteral {
                val: lit.val,
                ty: expected,
            }
        }
        &Expr::FloatLiteral(span) => {
            let lit = FloatLiteral::parse(&ast.src()[span.range()]);
            let info = lit
                .ty
                .map_or(TypeInfo::Float, |float| TypeInfo::Primitive(float.into()));
            ctx.specify(expected, info, |_| span);
            Node::FloatLiteral {
                val: lit.val,
                ty: expected,
            }
        }
        &Expr::BoolLiteral { start: _, val } => {
            ctx.specify(expected, TypeInfo::Primitive(Primitive::Bool), |ast| {
                ast[expr].span(ast)
            });
            Node::BoolLiteral(val)
        }
        &Expr::StringLiteral(span) => {
            let str = get_string_literal(ctx.ast.src(), span);
            let str_ty = builtins::get_str(ctx.compiler);
            ctx.specify(
                expected,
                TypeInfo::TypeDef(str_ty, LocalTypeIds::EMPTY),
                |_| span,
            );
            Node::StringLiteral(str)
        }
        &Expr::Array(span, elems) => {
            // PERF: reuse existing Array TypeInfo @TypeInfoReuse
            let elem_ty = ctx.hir.types.add_unknown();
            ctx.specify(
                expected,
                TypeInfo::Array {
                    element: elem_ty,
                    count: Some(elems.count),
                },
                |_| span,
            );
            let nodes = ctx.hir.add_invalid_nodes(elems.count);
            for (node, elem) in nodes.iter().zip(elems) {
                let elem_node = check(ctx, elem, scope, elem_ty, return_ty);
                ctx.hir.modify_node(node, elem_node);
            }
            Node::ArrayLiteral {
                elems: nodes,
                array_ty: expected,
            }
        }
        Expr::Tuple(span, values) => {
            // PERF: special case the specify for tuples, reusing elem types could be worth it if
            // a tuple type info was already present. @TypeInfoReuse
            let elem_types = ctx.hir.types.add_multiple_unknown(values.count);
            ctx.specify(expected, TypeInfo::Tuple(elem_types), |_| *span);
            let elems = ctx.hir.add_invalid_nodes(values.count);
            for ((value, ty), node_id) in
                values.into_iter().zip(elem_types.iter()).zip(elems.iter())
            {
                let node = check(ctx, value, scope, ty, return_ty);
                ctx.hir.modify_node(node_id, node);
            }
            Node::TupleLiteral { elems, elem_types }
        }
        &Expr::EnumLiteral { span, ident, args } => {
            check_enum_literal(ctx, scope, expected, return_ty, span, ident, args)
        }
        &Expr::Function { id } => {
            function_item(ctx, ctx.module, id, expected, |ast| ast[expr].span(ast))
        }
        &Expr::Primitive { primitive, .. } => {
            // PERF @TypeInfoReuse
            let ty = ctx.hir.types.add(TypeInfo::Primitive(primitive));
            ctx.specify(expected, TypeInfo::TypeItem { ty }, |ast| {
                ast[expr].span(ast)
            });
            Node::Invalid
        }
        &Expr::Type { id } => {
            let resolved_id = ctx
                .compiler
                .add_type_def(ctx.module, id, "TODO(type_name)".into());
            ctx.compiler
                .get_module_ast_and_symbols(ctx.module)
                .symbols
                .types[id.idx()] = Some(resolved_id);
            let ty = ctx.compiler.get_resolved_type_def(resolved_id);
            let generics = ctx.hir.types.add_multiple_unknown(ty.generic_count.into());
            let ty = ctx.hir.types.add(TypeInfo::TypeDef(resolved_id, generics));
            ctx.specify(expected, TypeInfo::TypeItem { ty }, |ast| {
                ast[expr].span(ast)
            });
            Node::Invalid
        }

        &Expr::Ident { span } => check_ident(ctx, scope, expected, span),
        Expr::Declare { .. } => todo!("check variable declarations without values"),
        Expr::DeclareWithVal {
            pat,
            annotated_ty,
            val,
        } => {
            let mut exhaustion = Exhaustion::None;
            let ty = ctx.hir.types.info_from_unresolved(
                &annotated_ty,
                ctx.compiler,
                ctx.module,
                scope.get_innermost_static_scope(),
            );
            let ty = ctx.hir.types.add(ty);
            let val = check(ctx, *val, scope, ty, return_ty);
            let pattern = pattern::check(ctx, &mut scope.variables, &mut exhaustion, *pat, ty);
            if !exhaustion.is_trivially_exhausted() {
                ctx.deferred_exhaustions.push((exhaustion, ty, *pat));
            }
            Node::DeclareWithVal {
                pattern: ctx.hir.add_pattern(pattern),
                val: ctx.hir.add(val),
            }
        }
        Expr::Hole(_) => {
            ctx.invalidate(expected);
            ctx.compiler
                .errors
                .emit_err(Error::HoleLHSOnly.at_span(ctx.span(expr)));
            Node::Invalid
        }

        &Expr::UnOp(_, op, value) => {
            match op {
                UnOp::Neg => {
                    // TODO(trait): this should constrain the value with a trait
                    let value = check(ctx, value, scope, expected, return_ty);
                    Node::Negate(ctx.hir.add(value), expected)
                }
                UnOp::Not => {
                    ctx.specify(expected, TypeInfo::Primitive(Primitive::Bool), |ast| {
                        ast[expr].span(ast)
                    });
                    let value = check(ctx, value, scope, expected, return_ty);
                    Node::Not(ctx.hir.add(value))
                }
                UnOp::Ref => {
                    // PERF: could check if the expected type is already a pointer and avoid extra
                    // unknown TypeInfo @TypeInfoReuse
                    let pointee = ctx.hir.types.add(TypeInfo::Unknown);
                    ctx.specify(expected, TypeInfo::Pointer(pointee), |ast| {
                        ast[expr].span(ast)
                    });
                    let value = check(ctx, value, scope, pointee, return_ty);
                    Node::AddressOf {
                        inner: ctx.hir.add(value),
                        value_ty: pointee,
                    }
                }
                UnOp::Deref => {
                    let ptr_ty = ctx.hir.types.add(TypeInfo::Pointer(expected));
                    let value = check(ctx, value, scope, ptr_ty, return_ty);
                    Node::Deref {
                        value: ctx.hir.add(value),
                        deref_ty: expected,
                    }
                }
            }
        }
        &Expr::BinOp(op, l, r) => {
            match op {
                Operator::Add | Operator::Sub | Operator::Mul | Operator::Div | Operator::Mod => {
                    // TODO: this will be have to bound/handled by traits
                    let l = check(ctx, l, scope, expected, return_ty);
                    let r = check(ctx, r, scope, expected, return_ty);
                    let op = match op {
                        Operator::Add => hir::Arithmetic::Add,
                        Operator::Sub => hir::Arithmetic::Sub,
                        Operator::Mul => hir::Arithmetic::Mul,
                        Operator::Div => hir::Arithmetic::Div,
                        Operator::Mod => hir::Arithmetic::Mod,
                        _ => unreachable!(),
                    };
                    Node::Arithmetic(ctx.hir.add(l), ctx.hir.add(r), op, expected)
                }
                Operator::Assignment(assign_ty) => {
                    // TODO: arithmetic assignment operations will be have to bound/handled by traits
                    ctx.specify(expected, Primitive::Unit, |ast| ast[expr].span(ast));
                    let (lval, ty) = lval::check(ctx, l, scope, return_ty);
                    let val = check(ctx, r, scope, ty, return_ty);
                    Node::Assign(ctx.hir.add_lvalue(lval), ctx.hir.add(val), assign_ty, ty)
                }
                Operator::Or | Operator::And => {
                    ctx.specify(expected, Primitive::Bool, |ast| ast[expr].span(ast));
                    let l = check(ctx, l, scope, expected, return_ty);
                    let r = check(ctx, r, scope, expected, return_ty);
                    let l = ctx.hir.add(l);
                    let r = ctx.hir.add(r);
                    let cmp = if op == Operator::Or {
                        Comparison::Or
                    } else {
                        Comparison::And
                    };
                    Node::Comparison(l, r, cmp)
                }
                Operator::Equals | Operator::NotEquals => {
                    let compared = ctx.hir.types.add_unknown();
                    let l = check(ctx, l, scope, compared, return_ty);
                    let r = check(ctx, r, scope, compared, return_ty);
                    let l = ctx.hir.add(l);
                    let r = ctx.hir.add(r);
                    let cmp = if op == Operator::Equals {
                        Comparison::Eq
                    } else {
                        Comparison::NE
                    };
                    Node::Comparison(l, r, cmp)
                }
                Operator::LT | Operator::GT | Operator::LE | Operator::GE => {
                    // FIXME: this will have to be bound by type like Ord
                    let compared = ctx.hir.types.add_unknown();
                    let l = check(ctx, l, scope, compared, return_ty);
                    let r = check(ctx, r, scope, compared, return_ty);
                    let l = ctx.hir.add(l);
                    let r = ctx.hir.add(r);
                    let cmp = match op {
                        Operator::LT => Comparison::LT,
                        Operator::GT => Comparison::GT,
                        Operator::LE => Comparison::LE,
                        Operator::GE => Comparison::GE,
                        _ => unreachable!(),
                    };
                    Node::Comparison(l, r, cmp)
                }
                Operator::Range | Operator::RangeExclusive => {
                    todo!("range types not implemented yet")
                }
            }
        }
        Expr::As(val, new_ty) => {
            let from_ty = ctx.hir.types.add_unknown();
            let val = check(ctx, *val, scope, from_ty, return_ty);
            let val = ctx.hir.add(val);
            let new_type_info = ctx.hir.types.info_from_unresolved(
                new_ty,
                ctx.compiler,
                ctx.module,
                scope.get_innermost_static_scope(),
            );
            ctx.specify(expected, new_type_info, |_| new_ty.span());
            let cast_id = ctx.hir.add_cast(hir::Cast {
                val,
                cast_ty: hir::CastType::Invalid, // will be filled in in deferred check
            });
            ctx.deferred_casts.push((from_ty, expected, expr, cast_id));
            Node::Cast(cast_id)
        }
        &Expr::Root(_) => todo!("path roots"),

        &Expr::MemberAccess {
            left,
            name: name_span,
        } => check_member_access(ctx, left, name_span, expr, scope, expected, return_ty),
        &Expr::Index { expr, idx, end: _ } => {
            let array_ty = ctx.hir.types.add(TypeInfo::Array {
                element: expected,
                count: None,
            });
            let array = check(ctx, expr, scope, array_ty, return_ty);
            let index_ty = ctx.hir.types.add(TypeInfo::Integer);
            let index = check(ctx, idx, scope, index_ty, return_ty);
            Node::ArrayIndex {
                array: ctx.hir.add(array),
                index: ctx.hir.add(index),
                elem_ty: expected,
            }
        }
        &Expr::TupleIdx { left, idx, .. } => {
            let tuple_ty = ctx.hir.types.add_unknown(); // add Size::AtLeast tuple here maybe
            let tuple_value = check(ctx, left, scope, tuple_ty, return_ty);
            let elem_types = match ctx.hir.types[tuple_ty] {
                TypeInfo::Tuple(ids) => ids,
                TypeInfo::Invalid => return Node::Invalid,
                _ => {
                    // TODO: could add TupleCountMode and stuff again to unify with tuple with
                    // Size::AtLeast. Not doing that for now since it is very rare.
                    ctx.compiler
                        .errors
                        .emit_err(Error::TypeMustBeKnownHere.at_span(ctx.span(expr)));
                    return Node::Invalid;
                }
            };
            if let Some(elem_ty) = elem_types.nth(idx) {
                ctx.unify(elem_ty, expected, |ast| ast[expr].span(ast));
                Node::Element {
                    tuple_value: ctx.hir.add(tuple_value),
                    index: idx,
                    elem_types,
                }
            } else {
                ctx.compiler
                    .errors
                    .emit_err(Error::TupleIndexOutOfRange.at_span(ctx.span(expr)));
                Node::Invalid
            }
        }

        Expr::ReturnUnit { .. } => {
            ctx.specify(return_ty, TypeInfo::Primitive(Primitive::Unit), |ast| {
                ast[expr].span(ast)
            });
            Node::Return(ctx.hir.add(Node::Unit))
        }
        &Expr::Return { val, .. } => {
            let val = check(ctx, val, scope, return_ty, return_ty);
            Node::Return(ctx.hir.add(val))
        }

        // FIXME: some code duplication going on with the 4 different If variants
        &Expr::If {
            start: _,
            cond,
            then,
        } => {
            ctx.specify(expected, TypeInfo::Primitive(Primitive::Unit), |ast| {
                ast[expr].span(ast)
            });
            let bool_ty = ctx.hir.types.add(TypeInfo::Primitive(Primitive::Bool));
            let cond = check(ctx, cond, scope, bool_ty, return_ty);
            let then = check(ctx, then, scope, expected, return_ty);
            Node::IfElse {
                cond: ctx.hir.add(cond),
                then: ctx.hir.add(then),
                else_: ctx.hir.add(Node::Unit),
                resulting_ty: expected,
            }
        }
        &Expr::IfElse {
            start: _,
            cond,
            then,
            else_,
        } => {
            let bool_ty = ctx.hir.types.add(TypeInfo::Primitive(Primitive::Bool));
            let cond = check(ctx, cond, scope, bool_ty, return_ty);
            let then = check(ctx, then, scope, expected, return_ty);
            let else_ = check(ctx, else_, scope, expected, return_ty);
            Node::IfElse {
                cond: ctx.hir.add(cond),
                then: ctx.hir.add(then),
                else_: ctx.hir.add(else_),
                resulting_ty: expected,
            }
        }
        &Expr::IfPat {
            start: _,
            pat,
            value,
            then,
        } => {
            ctx.specify(expected, TypeInfo::Primitive(Primitive::Unit), |ast| {
                ast[expr].span(ast)
            });
            let pattern_ty = ctx.hir.types.add_unknown();
            let value = check(ctx, value, scope, pattern_ty, return_ty);
            let mut body_scope = LocalScope {
                module: scope.module,
                parent: Some(scope),
                static_scope: None,
                variables: dmap::new(),
            };
            let mut exhaustion = Exhaustion::None;
            let pat = pattern::check(
                ctx,
                &mut body_scope.variables,
                &mut exhaustion,
                pat,
                pattern_ty,
            );
            if exhaustion.is_trivially_exhausted() {
                // TODO: Error::ConditionIsAlwaysTrue
                // maybe even defer this exhaustion to check for this warning in non-trivial case
            }
            let cond = Node::CheckPattern(ctx.hir.add_pattern(pat), ctx.hir.add(value));
            let then = check(ctx, then, &mut body_scope, expected, return_ty);
            Node::IfElse {
                cond: ctx.hir.add(cond),
                then: ctx.hir.add(then),
                else_: ctx.hir.add(Node::Unit),
                resulting_ty: expected,
            }
        }
        &Expr::IfPatElse {
            start: _,
            pat,
            value,
            then,
            else_,
        } => {
            let pattern_ty = ctx.hir.types.add_unknown();
            let value = check(ctx, value, scope, pattern_ty, return_ty);
            let mut body_scope = LocalScope {
                module: scope.module,
                parent: Some(scope),
                static_scope: None,
                variables: dmap::new(),
            };
            let mut exhaustion = Exhaustion::None;
            let pat = pattern::check(
                ctx,
                &mut body_scope.variables,
                &mut exhaustion,
                pat,
                pattern_ty,
            );
            if exhaustion.is_trivially_exhausted() {
                // TODO: Error::ConditionIsAlwaysTrue
                // maybe even defer this exhaustion to check for this warning in non-trivial case
            }
            let cond = Node::CheckPattern(ctx.hir.add_pattern(pat), ctx.hir.add(value));
            let then = check(ctx, then, &mut body_scope, expected, return_ty);
            let else_ = check(ctx, else_, &mut body_scope, expected, return_ty);
            Node::IfElse {
                cond: ctx.hir.add(cond),
                then: ctx.hir.add(then),
                else_: ctx.hir.add(else_),
                resulting_ty: expected,
            }
        }
        &Expr::Match {
            span: _,
            val,
            extra_branches,
            branch_count,
        } => {
            let matched_ty = ctx.hir.types.add_unknown();
            let value = check(ctx, val, scope, matched_ty, return_ty);
            let value = ctx.hir.add(value);
            let mut vars = dmap::new();
            let mut exhaustion = Exhaustion::None;
            let patterns = ctx
                .hir
                .add_patterns((0..branch_count).map(|_| hir::Pattern::Invalid));
            let branches = ctx.hir.add_invalid_nodes(branch_count);
            for i in 0..branch_count {
                vars.clear();
                let pat = ExprId(extra_branches + 2 * i);
                let pat = pattern::check(ctx, &mut vars, &mut exhaustion, pat, matched_ty);
                ctx.hir
                    .modify_pattern(hir::PatternId(patterns.index + i), pat);
                let mut scope = LocalScope {
                    parent: Some(scope),
                    variables: vars,
                    module: scope.module,
                    static_scope: None,
                };
                let branch = ExprId(extra_branches + 2 * i + 1);
                let branch = check(ctx, branch, &mut scope, expected, return_ty);
                vars = scope.variables;
                ctx.hir.modify_node(hir::NodeId(branches.index + i), branch);
            }
            Node::Match {
                value,
                branch_index: branches.index,
                pattern_index: patterns.index,
                branch_count,
            }
        }
        &Expr::While {
            start: _,
            cond,
            body,
        } => {
            let bool_ty = ctx.hir.types.add(TypeInfo::Primitive(Primitive::Bool));
            let cond = check(ctx, cond, scope, bool_ty, return_ty);
            let body_ty = ctx.hir.types.add_unknown();
            let body = check(ctx, body, scope, body_ty, return_ty);
            Node::While {
                cond: ctx.hir.add(cond),
                body: ctx.hir.add(body),
            }
        }
        &Expr::WhilePat {
            start: _,
            pat,
            val,
            body,
        } => {
            let value_ty = ctx.hir.types.add_unknown();
            let val = check(ctx, val, scope, value_ty, return_ty);
            let mut body_scope = LocalScope {
                parent: Some(scope),
                module: scope.module,
                variables: dmap::new(),
                static_scope: None,
            };
            let mut exhaustion = Exhaustion::None;
            let pat = pattern::check(
                ctx,
                &mut body_scope.variables,
                &mut exhaustion,
                pat,
                value_ty,
            );
            let cond = Node::CheckPattern(ctx.hir.add_pattern(pat), ctx.hir.add(val));
            let body_ty = ctx.hir.types.add_unknown();
            let body = check(ctx, body, &mut body_scope, body_ty, return_ty);
            Node::While {
                cond: ctx.hir.add(cond),
                body: ctx.hir.add(body),
            }
        }

        &Expr::FunctionCall(call) => check_call(ctx, &ast[call], expr, scope, expected, return_ty),

        Expr::Asm { .. } => todo!("implement inline assembly properly"),
    }
}

fn check_ident(
    ctx: &mut Ctx<'_>,
    scope: &mut LocalScope<'_>,
    expected: LocalTypeId,
    span: span::TSpan,
) -> Node {
    let name = &ctx.ast[span];
    match scope.resolve(name, span, ctx.compiler) {
        LocalItem::Var(var) => {
            let ty = ctx.hir.get_var(var);
            ctx.unify(expected, ty, |_| span);
            Node::Variable(var)
        }
        LocalItem::Def(def) => def_to_node(ctx, def, expected, span),
        LocalItem::Invalid => {
            ctx.specify(expected, TypeInfo::Invalid, |_| span);
            Node::Invalid
        }
    }
}

fn def_to_node(ctx: &mut Ctx, def: Def, expected: LocalTypeId, span: TSpan) -> Node {
    match def {
        Def::Invalid => {
            ctx.specify(expected, TypeInfo::Invalid, |_| span);
            Node::Invalid
        }
        Def::Function(module, id) => function_item(ctx, module, id, expected, |_| span),
        Def::Type(ty) => {
            let ty = ctx.hir.types.generic_info_from_resolved(ctx.compiler, &ty);
            let ty = ctx.hir.types.add(ty);
            ctx.specify(expected, TypeInfo::TypeItem { ty }, |_| span);
            Node::Invalid
        }
        Def::ConstValue(const_val) => {
            match &ctx.compiler.const_values[const_val.idx()] {
                ConstValue::Undefined => todo!("should this invalidate the type?"),
                ConstValue::Unit => {
                    ctx.specify(expected, TypeInfo::Primitive(Primitive::Unit), |_| span);
                }
                ConstValue::Int(_) => {
                    ctx.specify(expected, TypeInfo::Integer, |_| span);
                }
                ConstValue::Float(_) => ctx.specify(expected, TypeInfo::Float, |_| span),
            }
            Node::Const {
                id: const_val,
                ty: expected,
            }
        }
        Def::Module(id) => {
            ctx.specify(expected, TypeInfo::ModuleItem(id), |_| span);
            Node::Invalid
        }
        Def::Global(_, _) => todo!("globals"),
    }
}

fn check_enum_literal(
    ctx: &mut Ctx,
    scope: &mut LocalScope,
    expected: LocalTypeId,
    return_ty: LocalTypeId,
    span: TSpan,
    ident: TSpan,
    args: ExprExtra,
) -> Node {
    // Do the type checking manually instead of using `specify`.
    // This allows skipping construction of unneeded enum variant representations.

    let name = &ctx.ast[ident];

    enum OrdinalType {
        Inferred(VariantId),
        Known(u32),
    }
    let res =
        match ctx.hir.types[expected] {
            TypeInfo::Invalid => {
                for arg in args.into_iter() {
                    let ty = ctx.hir.types.add_unknown();
                    check(ctx, arg, scope, ty, return_ty);
                }
                return Node::Invalid;
            }
            TypeInfo::Enum(id) => {
                let variants = ctx.hir.types.get_enum_variants(id);
                if let Some(variant) = variants
                    .iter()
                    .copied()
                    .find(|&variant| (&*ctx.hir.types[variant].name == name))
                {
                    let arg_types = ctx.hir.types[variant].args;
                    Ok((OrdinalType::Inferred(variant), arg_types))
                } else {
                    let arg_types = ctx.hir.types.add_multiple_unknown(args.count + 1);
                    let variant = ctx
                        .hir
                        .types
                        .append_enum_variant(id, name.into(), arg_types);
                    Ok((OrdinalType::Inferred(variant), arg_types))
                }
            }
            TypeInfo::Unknown => {
                let arg_types = ctx.hir.types.add_multiple_unknown(args.count + 1);
                let enum_id = ctx.hir.types.add_enum_type();
                let variant = ctx
                    .hir
                    .types
                    .append_enum_variant(enum_id, name.into(), arg_types);
                ctx.hir.types.replace(expected, TypeInfo::Enum(enum_id));
                Ok((OrdinalType::Inferred(variant), arg_types))
            }
            TypeInfo::TypeDef(id, generics) => {
                let def = Rc::clone(&ctx.compiler.get_resolved_type_def(id).def);
                if let ResolvedTypeDef::Enum(enum_) = &*def {
                    let variant = enum_.variants.iter().zip(0..).find_map(
                        |((variant_name, arg_types), i)| {
                            (variant_name == name).then_some((i, &*arg_types))
                        },
                    );
                    if let Some((variant_index, arg_types)) = variant {
                        if arg_types.len() != args.count as usize {
                            Err(Error::InvalidArgCount {
                                expected: arg_types.len() as _,
                                varargs: false,
                                found: args.count,
                            }
                            .at_span(span.in_mod(ctx.module)))
                        } else {
                            let arg_type_ids = ctx
                                .hir
                                .types
                                .add_multiple_unknown(arg_types.len() as u32 + 1);
                            let mut arg_type_iter = arg_type_ids.iter();
                            ctx.hir.types.replace(
                                arg_type_iter.next().unwrap(),
                                int_ty_from_variant_count(enum_.variants.len() as u32),
                            );
                            for (r, ty) in arg_type_ids.iter().zip(arg_types.iter()) {
                                let ty = ctx.type_from_resolved(ty, generics);
                                ctx.hir.types.replace(r, ty);
                            }

                            Ok((OrdinalType::Known(variant_index), arg_type_ids))
                        }
                    } else {
                        Err(Error::NonexistantEnumVariant.at_span(ident.in_mod(ctx.module)))
                    }
                } else {
                    Err(Error::MismatchedType {
                        expected: ctx.type_to_string(ctx.hir.types[expected]),
                        found: "an enum variant".to_owned(),
                    }
                    .at_span(span.in_mod(ctx.module)))
                }
            }
            _ => Err(Error::MismatchedType {
                expected: ctx.type_to_string(ctx.hir.types[expected]),
                found: "an enum variant".to_owned(),
            }
            .at_span(span.in_mod(ctx.module))),
        };
    match res {
        Ok((variant_index, arg_type_ids)) => {
            debug_assert_eq!(arg_type_ids.count, args.count + 1);
            let arg_nodes = ctx.hir.add_invalid_nodes(arg_type_ids.count);
            let mut arg_node_iter = arg_nodes.iter();
            let mut arg_type_iter = arg_type_ids.iter();
            let ordinal_type = arg_type_iter.next().unwrap();
            let ordinal_node = match variant_index {
                OrdinalType::Known(ordinal) => Node::IntLiteral {
                    val: ordinal as u128,
                    ty: ordinal_type,
                },
                OrdinalType::Inferred(variant) => Node::InferredEnumOrdinal(variant),
            };
            ctx.hir
                .modify_node(arg_node_iter.next().unwrap(), ordinal_node);
            for ((arg, ty), r) in args.into_iter().zip(arg_type_iter).zip(arg_node_iter) {
                let arg_node = check(ctx, arg, scope, ty, return_ty);
                ctx.hir.modify_node(r, arg_node);
            }
            Node::TupleLiteral {
                elems: arg_nodes,
                elem_types: arg_type_ids,
            }
        }
        Err(err) => {
            ctx.invalidate(expected);
            ctx.compiler.errors.emit_err(err);
            Node::Invalid
        }
    }
}

fn function_item(
    ctx: &mut Ctx,
    function_module: ModuleId,
    function: FunctionId,
    expected: LocalTypeId,
    span: impl FnOnce(&Ast) -> TSpan,
) -> Node {
    let signature = ctx.compiler.get_signature(function_module, function);
    let generics_count = signature.generics.len();
    let generics = ctx.hir.types.add_multiple_unknown(generics_count as _);
    ctx.specify(
        expected,
        TypeInfo::FunctionItem {
            module: function_module,
            function,
            generics,
        },
        span,
    );
    // TODO: should this stay a unit node?
    Node::Unit
}

fn check_struct_def(
    ctx: &mut Ctx,
    struct_def: &ResolvedStructDef,
    generics: LocalTypeIds,
    call: &Call,
    scope: &mut LocalScope,
    return_ty: LocalTypeId,
) -> Node {
    if struct_def.fields.len() != call.args.count() {
        ctx.compiler.errors.emit_err(
            Error::InvalidArgCount {
                expected: struct_def.fields.len() as u32,
                varargs: false,
                found: call.args.count,
            }
            .at_span(TSpan::new(call.open_paren_start, call.end).in_mod(ctx.module)),
        );
    }
    let elem_nodes = ctx.hir.add_invalid_nodes(call.args.count);
    let elem_types = ctx.hir.types.add_multiple_unknown(call.args.count);
    for ((arg, (node_id, type_id)), (_field_name, field_ty)) in call
        .args
        .into_iter()
        .zip(elem_nodes.iter().zip(elem_types.iter()))
        .zip(&struct_def.fields)
    {
        let info_or_idx = ctx.type_from_resolved(field_ty, generics);
        ctx.hir.types.replace(type_id, info_or_idx);
        let node = check(ctx, arg, scope, type_id, return_ty);
        ctx.hir.modify_node(node_id, node);
    }
    Node::TupleLiteral {
        elems: elem_nodes,
        elem_types,
    }
}

fn check_member_access(
    ctx: &mut Ctx,
    left: ExprId,
    name_span: TSpan,
    expr: ExprId,
    scope: &mut LocalScope,
    expected: LocalTypeId,
    return_ty: LocalTypeId,
) -> Node {
    let left_ty = ctx.hir.types.add_unknown();
    let left_node = check(ctx, left, scope, left_ty, return_ty);
    let name = &ctx.ast.src()[name_span.range()];
    match ctx.hir.types[left_ty] {
        TypeInfo::TypeItem { ty } => {
            return match name {
                "size" => {
                    ctx.specify(expected, Primitive::U64, |ast| ast[expr].span(ast));
                    Node::TypeProperty(ty, hir::TypeProperty::Size)
                }
                "align" => {
                    ctx.specify(expected, Primitive::U64, |ast| ast[expr].span(ast));
                    Node::TypeProperty(ty, hir::TypeProperty::Align)
                }
                "stride" => {
                    ctx.specify(expected, Primitive::U64, |ast| ast[expr].span(ast));
                    Node::TypeProperty(ty, hir::TypeProperty::Stride)
                }
                _ => match ctx.hir.types[ty] {
                    TypeInfo::Invalid => Node::Invalid,
                    TypeInfo::TypeDef(id, generics) => {
                        let ty = ctx.compiler.get_resolved_type_def(id);
                        if let Some(&method) = ty.methods.get(name) {
                            let module = ty.module;
                            let signature = ctx.compiler.get_signature(module, method);
                            if signature.generics.len() != generics.count as usize {
                                todo!("handle extra generics");
                            }
                            ctx.specify(
                                expected,
                                TypeInfo::FunctionItem {
                                    module,
                                    function: method,
                                    generics,
                                },
                                |ast| ast[expr].span(ast),
                            );
                            Node::Invalid
                        } else {
                            let def = Rc::clone(&ty.def);
                            if let ResolvedTypeDef::Enum(def) = &*def {
                                if let Some((ordinal, args)) = def.get_by_name(name) {
                                    let ordinal_ty =
                                        int_ty_from_variant_count(def.variants.len() as u32);
                                    let node = if args.is_empty() {
                                        ctx.specify(
                                            expected,
                                            TypeInfo::TypeDef(id, generics),
                                            |ast| ast[expr].span(ast),
                                        );
                                        let ordinal_ty = ctx.hir.types.add(ordinal_ty);
                                        let elem_types = ctx
                                            .hir
                                            .types
                                            .add_multiple_info_or_idx([ordinal_ty.into()]);
                                        let elems = ctx.hir.add_nodes([Node::IntLiteral {
                                            val: ordinal as u128,
                                            ty: ordinal_ty,
                                        }]);
                                        Node::TupleLiteral { elems, elem_types }
                                    } else {
                                        let arg_types = ctx
                                            .hir
                                            .types
                                            .add_multiple_unknown(args.len() as u32 + 1);
                                        let mut arg_type_iter = arg_types.iter();
                                        ctx.hir
                                            .types
                                            .replace(arg_type_iter.next().unwrap(), ordinal_ty);
                                        for (r, ty) in arg_type_iter.zip(args.iter()) {
                                            let ty = ctx.type_from_resolved(ty, generics);
                                            ctx.hir.types.replace(r, ty);
                                        }
                                        ctx.specify(
                                            expected,
                                            TypeInfo::EnumVariantItem {
                                                enum_type: id,
                                                generics,
                                                ordinal: ordinal as u32,
                                                arg_types,
                                            },
                                            |ast| ast[expr].span(ast),
                                        );
                                        Node::Invalid
                                    };
                                    return node;
                                }
                            }
                            ctx.compiler.errors.emit_err(
                                Error::NonexistantMember(None)
                                    .at_span(name_span.in_mod(ctx.module)),
                            );
                            ctx.invalidate(expected);
                            Node::Invalid
                        }
                    }
                    TypeInfo::Enum { .. } => todo!("local enum variant from type item"),
                    TypeInfo::Unknown => {
                        ctx.compiler
                            .errors
                            .emit_err(Error::TypeMustBeKnownHere.at_span(ctx.span(left)));
                        ctx.invalidate(expected);
                        Node::Invalid
                    }
                    _ => {
                        ctx.compiler.errors.emit_err(
                            Error::NonexistantMember(None).at_span(name_span.in_mod(ctx.module)),
                        );
                        ctx.invalidate(expected);
                        Node::Invalid
                    }
                },
            };
        }
        TypeInfo::ModuleItem(id) => {
            let def = ctx
                .compiler
                .resolve_in_module(id, name, name_span.in_mod(ctx.module));
            return def_to_node(ctx, def, expected, name_span);
        }
        _ => {}
    }
    // now check the type while allowing auto deref for field access, methods
    let mut current_ty = left_ty;
    let mut pointer_count = 0;
    loop {
        match ctx.hir.types[current_ty] {
            TypeInfo::Pointer(pointee) => {
                pointer_count += 1;
                current_ty = pointee;
            }
            TypeInfo::TypeDef(id, generics) => {
                let resolved = ctx.compiler.get_resolved_type_def(id);
                if let Some(&method) = resolved.methods.get(name) {
                    let module = resolved.module;
                    let signature = ctx.compiler.get_signature(module, method);
                    if signature.generics.len() != generics.count as usize {
                        todo!("handle extra generics");
                    }
                    let Some(required_pointer_count) = check_is_instance_method(signature, id)
                    else {
                        ctx.compiler
                            .errors
                            .emit_err(Error::NotAnInstanceMethod.at_span(ctx.span(expr)));
                        ctx.invalidate(expected);
                        return Node::Invalid;
                    };
                    let self_value = ctx.auto_ref_deref(
                        pointer_count,
                        required_pointer_count,
                        left_node,
                        left_ty,
                    );
                    ctx.specify(
                        expected,
                        TypeInfo::MethodItem {
                            module,
                            function: method,
                            generics,
                        },
                        |ast| ast[expr].span(ast),
                    );
                    return self_value;
                }
                let def = Rc::clone(&resolved.def);
                if let ResolvedTypeDef::Struct(def) = &*def {
                    let (indexed_field, elem_types) = def.get_indexed_field(ctx, generics, name);
                    if let Some((index, field_ty)) = indexed_field {
                        // perform auto deref first
                        let mut dereffed_node = left_node;
                        let mut current_ty = left_ty;
                        for _ in 0..pointer_count {
                            let TypeInfo::Pointer(pointee) = ctx.hir.types[current_ty] else {
                                // the deref was already checked so we know the type is wrapped in
                                // `pointer_count` pointers
                                unreachable!()
                            };
                            let value = ctx.hir.add(dereffed_node);
                            dereffed_node = Node::Deref {
                                value,
                                deref_ty: pointee,
                            };
                            current_ty = pointee;
                        }
                        ctx.unify(expected, field_ty, |ast| ast[expr].span(ast));
                        return Node::Element {
                            tuple_value: ctx.hir.add(dereffed_node),
                            index,
                            elem_types,
                        };
                    }
                }
                ctx.compiler
                    .errors
                    .emit_err(Error::NonexistantMember(None).at_span(name_span.in_mod(ctx.module)));
                ctx.invalidate(expected);
                return Node::Invalid;
            }
            TypeInfo::Unknown => {
                ctx.compiler
                    .errors
                    .emit_err(Error::TypeMustBeKnownHere.at_span(ctx.span(left)));
                ctx.invalidate(expected);
                return Node::Invalid;
            }
            TypeInfo::Invalid => {
                ctx.invalidate(expected);
                return Node::Invalid;
            }
            other => {
                let hint = matches!(other, TypeInfo::Enum(_))
                    .then_some(crate::error::MemberHint::InferredEnum);
                ctx.compiler
                    .errors
                    .emit_err(Error::NonexistantMember(hint).at_span(name_span.in_mod(ctx.module)));
                ctx.invalidate(expected);
                return Node::Invalid;
            }
        }
    }
}

/// checks if the provided method signature is valid as an instance medhot of the provided type.
/// Returns the number of pointer indirections of the self type in case it is valid or None
/// otherwise.
fn check_is_instance_method(signature: &crate::compiler::Signature, id: TypeId) -> Option<u32> {
    let Some((_, self_param_ty)) = signature.args.first() else {
        return None;
    };
    let mut required_pointer_count = 0;
    let mut current_ty = self_param_ty;
    loop {
        match current_ty {
            Type::DefId {
                id: _,
                generics: Some(generics),
            } if !generics.is_empty() => todo!("self types with additional generics"),
            &Type::DefId {
                id: self_id,
                generics: _,
            } if id == self_id => {
                return Some(required_pointer_count);
            }
            Type::Pointer(inner) => {
                required_pointer_count += 1;
                current_ty = &*inner;
            }
            _ => {
                return None;
            }
        }
    }
}

fn check_call(
    ctx: &mut Ctx,
    call: &Call,
    expr: ExprId,
    scope: &mut LocalScope,
    expected: LocalTypeId,
    return_ty: LocalTypeId,
) -> Node {
    let called_ty = ctx.hir.types.add_unknown();
    let called_node = check(ctx, call.called_expr, scope, called_ty, return_ty);
    match ctx.hir.types[called_ty] {
        TypeInfo::Invalid => Node::Invalid,
        TypeInfo::TypeItem { ty: item_ty } => match ctx.hir.types[item_ty] {
            TypeInfo::TypeDef(id, generics) => {
                let resolved = ctx.compiler.get_resolved_type_def(id);
                debug_assert_eq!(generics.count, resolved.generic_count.into());
                let def = Rc::clone(&resolved.def);
                match &*def {
                    ResolvedTypeDef::Struct(struct_def) => {
                        ctx.unify(expected, item_ty, |ast| ast[expr].span(ast));
                        check_struct_def(ctx, &struct_def, generics, call, scope, return_ty)
                    }
                    ResolvedTypeDef::Enum(_) => {
                        ctx.compiler
                            .errors
                            .emit_err(Error::FunctionOrStructTypeExpected.at_span(ctx.span(expr)));
                        Node::Invalid
                    }
                }
            }
            _ => {
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

            match check_call_signature(
                ctx,
                expr,
                expected,
                call.args,
                generics,
                &signature.args,
                &signature.return_type,
                signature.varargs,
            ) {
                Ok(arg_types) => {
                    let args = ctx
                        .hir
                        .add_nodes((0..call.args.count).map(|_| Node::Invalid));
                    for ((arg, ty), node_id) in call.args.zip(arg_types.iter()).zip(args.iter()) {
                        let node = check(ctx, arg, scope, ty, return_ty);
                        ctx.hir.modify_node(node_id, node);
                    }

                    Node::Call {
                        function: (module, function),
                        generics,
                        args,
                        return_ty: expected,
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
            let signature_args = &signature.args[1..];
            match check_call_signature(
                ctx,
                expr,
                expected,
                call.args,
                generics,
                signature_args,
                &signature.return_type,
                signature.varargs,
            ) {
                Ok(arg_types) => {
                    let args = ctx
                        .hir
                        .add_nodes((0..call.args.count + 1).map(|_| Node::Invalid));
                    let mut arg_iter = args.iter();
                    ctx.hir.modify_node(arg_iter.next().unwrap(), called_node);
                    for ((arg, ty), node_id) in call.args.zip(arg_types.iter()).zip(arg_iter) {
                        let node = check(ctx, arg, scope, ty, return_ty);
                        ctx.hir.modify_node(node_id, node);
                    }

                    Node::Call {
                        function: (module, function),
                        generics,
                        args,
                        return_ty: expected,
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
                let node = check(ctx, arg, scope, ty, return_ty);
                ctx.hir.modify_node(r, node);
            }
            Node::TupleLiteral {
                elems,
                elem_types: arg_types,
            }
        }
        TypeInfo::Unknown => {
            ctx.compiler
                .errors
                .emit_err(Error::TypeMustBeKnownHere.at_span(ctx.span(call.called_expr)));
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

fn check_call_signature(
    ctx: &mut Ctx,
    expr: ExprId,
    expected: LocalTypeId,
    args: ExprExtra,
    generics: LocalTypeIds,
    signature: &[(String, Type)],
    return_type: &Type,
    varargs: bool,
) -> Result<LocalTypeIds, crate::error::CompileError> {
    let invalid_arg_count = if varargs {
        args.count() < signature.len()
    } else {
        args.count() != signature.len()
    };
    if invalid_arg_count {
        let expected = signature.len() as _;
        let span = ctx.span(expr);
        return Err(Error::InvalidArgCount {
            expected,
            varargs,
            found: args.count,
        }
        .at_span(span));
    }

    let arg_types = ctx.hir.types.add_multiple_unknown(args.count);
    // iterating over the signature, all extra arguments in case of vararg
    // arguments will stay unknown which is intended
    for (i, (_, arg)) in signature.iter().enumerate() {
        let ty = ctx.type_from_resolved(arg, generics);
        ctx.hir.types.replace(arg_types.nth(i as _).unwrap(), ty);
    }

    ctx.specify_resolved(expected, return_type, generics, |ast| ast[expr].span(ast));
    Ok(arg_types)
}

fn get_string_literal(src: &str, span: TSpan) -> String {
    src[span.start as usize + 1..span.end as usize]
        .replace("\\n", "\n")
        .replace("\\t", "\t")
        .replace("\\r", "\r")
        .replace("\\0", "\0")
        .replace("\\\"", "\"")
}

pub fn int_ty_from_variant_count(count: u32) -> TypeInfo {
    match count {
        0 | 1 => TypeInfo::Primitive(Primitive::Unit),
        2..=255 => TypeInfo::Primitive(Primitive::U8),
        256..=65535 => TypeInfo::Primitive(Primitive::U16),
        _ => TypeInfo::Primitive(Primitive::U32),
    }
}
