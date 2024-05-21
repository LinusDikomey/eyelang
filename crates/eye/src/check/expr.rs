use std::rc::Rc;

use id::ModuleId;
use span::TSpan;
use types::Primitive;

use crate::{
    compiler::{builtins, Def, LocalItem, LocalScope, ResolvedStructDef, ResolvedTypeDef},
    error::Error,
    eval::ConstValue,
    hir::{self, Comparison, Node},
    parser::{
        ast::{Ast, Call, Expr, ExprId, FunctionId, UnOp},
        token::{AssignType, FloatLiteral, IntLiteral, Operator},
    },
    type_table::{LocalTypeId, LocalTypeIds, TypeInfo},
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
        Expr::EnumLiteral { .. } => todo!("check enum literals"),

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
            let resolved_id = ctx.compiler.add_type_def(ctx.module, id);
            ctx.compiler.get_module_ast_and_symbols(ctx.module).1.types[id.idx()] =
                Some(resolved_id);
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
                Operator::Assignment(AssignType::Assign) => {
                    ctx.specify(expected, Primitive::Unit, |ast| ast[expr].span(ast));
                    let (lval, ty) = lval::check(ctx, l, scope, return_ty);
                    let val = check(ctx, r, scope, ty, return_ty);
                    Node::Assign(ctx.hir.add_lvalue(lval), ctx.hir.add(val))
                }
                Operator::Assignment(_ty) => todo!("assignment-op type checking"),
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
                Node::TupleIndex {
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
        Expr::Match { .. } => todo!(),
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
            let ty = ctx.type_from_resolved(&ty, LocalTypeIds::EMPTY);
            let ty = ctx.hir.types.add_info_or_idx(ty);
            ctx.specify(expected, TypeInfo::TypeItem { ty }, |_| span);
            Node::Invalid
        }
        Def::ConstValue(const_val) => {
            match &ctx.compiler.const_values[const_val.idx()] {
                ConstValue::Undefined => todo!("should this invalidate the type?"),
                ConstValue::Unit => {
                    ctx.specify(expected, TypeInfo::Primitive(Primitive::Unit), |_| span);
                }
                ConstValue::Number(_) => {
                    ctx.specify(expected, TypeInfo::Integer, |_| span);
                }
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
        TypeInfo::TypeItem { ty: _ } => {
            todo!("size/align/stride exprs here, also enums/assoc functions")
        }
        TypeInfo::TypeDef(id, generics) => {
            let resolved = ctx.compiler.get_resolved_type_def(id);
            match &resolved.def {
                ResolvedTypeDef::Struct(def) => {
                    let def = def.clone(); // PERF: cloning def
                                           // PERF: Every time we index a struct, all fields are mapped to TypeInfo's
                                           // again. This could be improved by caching structs somehow ?? or by putting
                                           // the fields along the TypeDef (easier but would make TypeDef very large,
                                           // similar problem for enums and extra solution required).
                    let elem_types = ctx.hir.types.add_multiple_unknown(def.fields.len() as _);
                    let mut indexed_field = None;
                    let fields = def.fields.iter().zip(0..).zip(elem_types.iter());
                    for (((field_name, ty), index), r) in fields {
                        let ty = ctx.type_from_resolved(ty, generics);
                        if field_name == name {
                            indexed_field = Some((index, r));
                        }
                        ctx.hir.types.replace(r, ty);
                    }
                    if let Some((index, field_ty)) = indexed_field {
                        ctx.unify(expected, field_ty, |ast| ast[expr].span(ast));
                        Node::TupleIndex {
                            tuple_value: ctx.hir.add(left_node),
                            index,
                            elem_types,
                        }
                    } else {
                        ctx.compiler.errors.emit_err(
                            Error::NonexistantMember.at_span(name_span.in_mod(ctx.module)),
                        );
                        Node::Invalid
                    }
                }
            }
        }
        TypeInfo::ModuleItem(id) => {
            let def = ctx
                .compiler
                .resolve_in_module(id, name, name_span.in_mod(ctx.module));
            def_to_node(ctx, def, expected, name_span)
        }
        TypeInfo::Unknown => {
            ctx.compiler
                .errors
                .emit_err(Error::TypeMustBeKnownHere.at_span(ctx.span(left)));
            Node::Invalid
        }
        TypeInfo::Invalid => {
            ctx.invalidate(expected);
            Node::Invalid
        }
        _ => {
            ctx.compiler
                .errors
                .emit_err(Error::NonexistantMember.at_span(ctx.span(left)));
            Node::Invalid
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
    let _called = check(ctx, call.called_expr, scope, called_ty, return_ty);
    match ctx.hir.types[called_ty] {
        TypeInfo::Invalid => Node::Invalid,
        TypeInfo::TypeItem { ty: item_ty } => {
            match ctx.hir.types[item_ty] {
                TypeInfo::TypeDef(id, generics) => {
                    let resolved = ctx.compiler.get_resolved_type_def(id);
                    debug_assert_eq!(generics.count, resolved.generic_count.into());
                    match &resolved.def {
                        ResolvedTypeDef::Struct(struct_def) => {
                            // PERF: cloning struct def
                            let struct_def = struct_def.clone();
                            ctx.unify(expected, item_ty, |ast| ast[expr].span(ast));
                            check_struct_def(ctx, &struct_def, generics, call, scope, return_ty)
                        }
                        _ => {
                            ctx.compiler.errors.emit_err(
                                Error::FunctionOrStructTypeExpected.at_span(ctx.span(expr)),
                            );
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
            }
        }
        TypeInfo::FunctionItem {
            module,
            function,
            generics,
        } => {
            let signature = Rc::clone(ctx.compiler.get_signature(module, function));

            let invalid_arg_count = if signature.varargs {
                call.args.count() < signature.args.len()
            } else {
                call.args.count() != signature.args.len()
            };
            if invalid_arg_count {
                let expected = signature.args.len() as _;
                let varargs = signature.varargs;
                let span = ctx.span(expr);
                ctx.compiler.errors.emit_err(
                    Error::InvalidArgCount {
                        expected,
                        varargs,
                        found: call.args.count,
                    }
                    .at_span(span),
                );
                return Node::Invalid;
            }

            let arg_types = ctx.hir.types.add_multiple_unknown(call.args.count);
            // iterating over the signature, all extra arguments in case of vararg
            // arguments will stay unknown which is intended
            for (i, (_, arg)) in signature.args.iter().enumerate() {
                let ty = ctx.type_from_resolved(arg, generics);
                ctx.hir.types.replace(arg_types.nth(i as _).unwrap(), ty);
            }

            let func_return_ty = ctx.type_from_resolved(&signature.return_type, generics);
            let return_ty_info = ctx.hir.types.get_info_or_idx(func_return_ty);
            ctx.specify(expected, return_ty_info, |ast| ast[expr].span(ast));

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
        TypeInfo::MethodItem { .. } => todo!("methods"),
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

fn get_string_literal(src: &str, span: TSpan) -> String {
    src[span.start as usize + 1..span.end as usize]
        .replace("\\n", "\n")
        .replace("\\t", "\t")
        .replace("\\r", "\r")
        .replace("\\0", "\0")
        .replace("\\\"", "\"")
}
