use id::ModuleId;
use span::TSpan;
use types::Primitive;

use crate::{parser::{ast::{ExprId, Expr, FunctionId, Ast}, token::{IntLiteral, Operator, AssignType, FloatLiteral}}, compiler::{LocalScope, LocalItem, Def}, type_table::{LocalTypeId, TypeInfo}, hir::{Node, self, Comparison}, error::Error, eval::ConstValue};

use super::{Ctx, exhaust::Exhaustion, lval, pattern};


pub fn check(
    ctx: &mut Ctx,
    expr: ExprId,
    scope: &mut LocalScope,
    expected: LocalTypeId,
    return_ty: LocalTypeId,
) -> Node {
    let ast = ctx.ast;
    match &ast[expr] {
        &Expr::IntLiteral(span) => {
            let lit = IntLiteral::parse(&ast.src()[span.range()]);
            let info = lit.ty.map_or(
                TypeInfo::Integer,
                |int| TypeInfo::Primitive(int.into()),
            );
            ctx.specify(expected, info, |_| span);
            Node::IntLiteral { val: lit.val, ty: expected }
        }
        &Expr::FloatLiteral(span) => {
            let lit = FloatLiteral::parse(&ast.src()[span.range()]);
            let info = lit.ty.map_or(TypeInfo::Float, |float| TypeInfo::Primitive(float.into()));
            ctx.specify(expected, info, |_| span);
            Node::FloatLiteral { val: lit.val, ty: expected }
        }
        &Expr::Ident { span } => check_ident(ctx, scope, expected, span),
        Expr::ReturnUnit { .. } => {
            ctx.specify(return_ty, TypeInfo::Primitive(Primitive::Unit), |ast| ast[expr].span(ast));
            Node::Return(ctx.hir.add(Node::Unit))
        }
        &Expr::Return { val, .. } => {
            let val = check(ctx, val, scope, return_ty, return_ty);
            Node::Return(ctx.hir.add(val))
        }
        &Expr::Function { id } => function_item(ctx, ctx.module, id, expected, |ast| ast[expr].span(ast)),
        Expr::Type { id: _ } => todo!("type type?"),
        &Expr::Block { scope: static_scope, items } => {
            let mut scope = LocalScope {
                parent: Some(scope),
                variables: dmap::new(),
                module: scope.module,
                static_scope,
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
        Expr::DeclareWithVal { pat, annotated_ty, val } => {
            let mut exhaustion = Exhaustion::None;
            let ty = ctx.hir.types.info_from_unresolved(
                &annotated_ty,
                ctx.compiler,
                ctx.module,
                scope.static_scope,
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
        &Expr::BinOp(op, l, r) => {
            match op {
                Operator::Add
                | Operator::Sub
                | Operator::Mul
                | Operator::Div
                | Operator::Mod => {
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
                    let (lval, ty) = lval::check(ctx, l, scope);
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
                Operator::Range | Operator::RangeExclusive => todo!("range types not implemented yet"),
            }
        }
        &Expr::FunctionCall(call) => {
            let call = &ast[call];
            let function_ty = ctx.hir.types.add_unknown();
            let _called = check(ctx, call.called_expr, scope, function_ty, return_ty);
            match ctx.hir.types[function_ty] {
                TypeInfo::Invalid => Node::Invalid,
                TypeInfo::TypeDef(_, _) => todo!("struct initializers"),
                TypeInfo::FunctionItem { module, function, generics } => {
                    let signature = ctx.compiler.get_signature(module, function);
                    if (signature.varargs && call.args.count() < signature.args.len())
                        || call.args.count() != signature.args.len()
                    {
                        let expected = signature.args.len() as _;
                        let varargs = signature.varargs;
                        let span = ctx.span(expr);
                        ctx.compiler.errors.emit_err(Error::InvalidArgCount {
                            expected,
                            varargs, 
                            found: call.args.count,
                        }.at_span(span));
                        return Node::Invalid;
                    }

                    
                    let arg_types: Vec<_> = signature.args
                        .iter()
                        .map(|(_, arg)| ctx.hir.types.from_generic_resolved(arg, generics))
                        .collect();
                    let arg_types = ctx.hir.types.add_multiple_info_or_idx(arg_types);

                    let func_return_ty = ctx.hir.types.from_generic_resolved(
                        &signature.return_type,
                        generics,
                    );
                    let return_ty_info = ctx.hir.types.get_info_or_idx(func_return_ty);
                    ctx.specify(expected, return_ty_info, |ast| ast[expr].span(ast));


                    let args = ctx.hir.add_nodes((0..call.args.count).map(|_| Node::Invalid));
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
                    ctx.compiler.errors.emit_err(Error::TypeMustBeKnownHere
                        .at_span(ctx.span(call.called_expr)));
                    Node::Invalid
                }
                _ => {
                    ctx.compiler.errors.emit_err(Error::FunctionOrTypeExpected
                        .at_span(ctx.span(call.called_expr)));
                    Node::Invalid
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
                scope.static_scope,
            );
            ctx.specify(expected, new_type_info, |_| new_ty.span());
            let cast_id = ctx.hir.add_cast(hir::Cast {
                val,
                cast_ty: hir::CastType::Invalid, // will be filled in in deferred check
            });
            ctx.deferred_casts.push((from_ty, expected, expr, cast_id));
            Node::Cast(cast_id)
        }
        Expr::Tuple(span, values) => {
            // PERF: special case the specify for tuples, reusing elem types could be worth it if
            // a tuple type info was already present.
            let elem_types = ctx.hir.types.add_multiple_unknown(values.count);
            ctx.specify(expected, TypeInfo::Tuple(elem_types), |_| *span);
            let elems = ctx.hir.add_invalid_nodes(values.count);
            for ((value, ty), node_id) in values.into_iter().zip(elem_types.iter()).zip(elems.iter()) {
                let node = check(ctx, value, scope, ty, return_ty);
                ctx.hir.modify_node(node_id, node);
            }
            Node::Tuple { elems, elem_types }
        }
        &Expr::TupleIdx { expr, idx, .. } => {
            let tuple_ty = ctx.hir.types.add_unknown(); // add Size::AtLeast tuple here maybe
            let tuple_value = check(ctx, expr, scope, tuple_ty, return_ty);
            let elem_types = match ctx.hir.types[tuple_ty] {
                TypeInfo::Tuple(ids) => ids,
                _ => {
                    // TODO: could add TupleCountMode and stuff again to unify with tuple with
                    // Size::AtLeast. Not doing that for now since it is very rare.
                    ctx.compiler.errors.emit_err(Error::TypeMustBeKnownHere.at_span(ctx.span(expr)));
                    return Node::Invalid;
                }
            };
            if let Some(elem_ty) = elem_types.nth(idx) {
                ctx.unify(elem_ty, expected, |ast| ast[expr].span(ast));
                Node::TupleIdx { tuple_value: ctx.hir.add(tuple_value), index: idx, elem_ty }
            } else {
                ctx.compiler.errors.emit_err(Error::TupleIndexOutOfRange.at_span(ctx.span(expr)));
                Node::Invalid
            }

        }
        expr => todo!("typecheck {expr:?}")
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
        LocalItem::Def(def) => match def {
            Def::Invalid => {
                ctx.specify(expected, TypeInfo::Invalid, |_| span);
                Node::Invalid
            }
            Def::Function(module, id) => function_item(ctx, module, id, expected, |_| span),
            Def::Type(_) => todo!("type type?"),
            Def::ConstValue(const_val) => {
                match &ctx.compiler.const_values[const_val.idx()] {
                    ConstValue::Undefined => todo!("should this invalidate the type?"),
                    ConstValue::Unit => {
                        ctx.specify(
                            expected,
                            TypeInfo::Primitive(Primitive::Unit),
                            |_| span,
                        );
                    }
                    ConstValue::Number(_) => {
                        ctx.specify(
                            expected,
                            TypeInfo::Integer,
                            |_| span,
                        );
                    }
                }
                Node::Const { id: const_val, ty: expected }
            }
            Def::Module(_) => {
                ctx.compiler.errors.emit_err(
                    Error::ExpectedValue.at_span(span.in_mod(ctx.module)),
                );
                ctx.invalidate(expected);
                Node::Invalid
            }
            Def::Global(_, _) => todo!("globals"),
        }
        LocalItem::Invalid => {
            ctx.specify(expected, TypeInfo::Invalid, |_| span);
            Node::Invalid
        }
    }
}

fn function_item(
    ctx: &mut Ctx,
    _module: ModuleId,
    function: FunctionId,
    expected: LocalTypeId,
    span: impl FnOnce(&Ast) -> TSpan,
) -> Node {
    let signature = ctx.compiler.get_signature(ctx.module, function);
    let generics_count = signature.generics.len();
    let generics = ctx.hir.types.add_multiple_unknown(generics_count as _);
    ctx.specify(
        expected,
        TypeInfo::FunctionItem {
            module: ctx.module,
            function,
            generics,
        },
        span,
    );
    // TODO: should this stay a unit node?
    Node::Unit
}

