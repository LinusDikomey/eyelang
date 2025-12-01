use error::{Error, span::TSpan};

use crate::{
    Type,
    compiler::{
        Def, LocalItem, LocalScope, LocalScopeParent, ModuleSpan, ResolvedTypeContent, builtins,
    },
    eval::ConstValueId,
    hir::{self, Comparison, LValue, Logic, Node, NodeIds, Pattern},
    types::{BaseType, TypeFull, Types},
    typing::{
        Bound, Bounds, LocalTypeId, LocalTypeIds, OrdinalType, TypeInfo, TypeInfoOrIdx, TypeTable,
    },
};
use parser::ast::{
    Ast, Expr, ExprId, ExprIds, FloatLiteral, FunctionId, IntLiteral, ModuleId, Operator,
    Primitive, UnOp,
};

use super::{Ctx, call, closure::closure, exhaust::Exhaustion, lval, pattern};

pub fn check(
    ctx: &mut Ctx,
    expr: ExprId,
    scope: &mut LocalScope,
    expected: LocalTypeId,
    return_ty: LocalTypeId,
    noreturn: &mut bool,
) -> Node {
    let ast = ctx.ast;
    match &ast[expr] {
        Expr::Error(_) => {
            *noreturn = true;
            Node::Invalid
        }
        &Expr::Block {
            scope: static_scope,
            items,
            ..
        } => {
            let mut scope = LocalScope {
                parent: LocalScopeParent::Some(scope),
                variables: dmap::new(),
                module: scope.module,
                static_scope: Some(static_scope),
            };
            let mut item_nodes = ctx.hir.add_invalid_nodes(items.count);
            for ((item, r), i) in items.into_iter().zip(item_nodes.iter()).zip(0..) {
                let statement_ty = ctx.hir.types.add_unknown();
                let node = check(ctx, item, &mut scope, statement_ty, return_ty, noreturn);
                ctx.hir.modify_node(r, node);
                if *noreturn {
                    // just shorten the node list. We waste the remaining nodes but this is not the
                    // common case. Usually, there is no unreachable code in blocks.
                    // TODO: unreachable code warning for the rest of the lines
                    item_nodes = NodeIds {
                        index: item_nodes.index,
                        count: i + 1,
                    };
                    break;
                }
            }
            if !*noreturn {
                ctx.specify(expected, TypeInfo::UNIT, |ast| ast[expr].span(ast));
            }
            Node::Block(item_nodes)
        }
        &Expr::Nested { inner, .. } => check(ctx, inner, scope, expected, return_ty, noreturn),
        &Expr::IntLiteral { span, .. } => {
            let lit = IntLiteral::parse(&ast.src()[span.range()]);
            let info = lit.ty.map_or(TypeInfo::Integer, |int| {
                TypeInfo::Instance(Primitive::from(int).into(), LocalTypeIds::EMPTY)
            });
            ctx.specify(expected, info, |_| span);
            Node::IntLiteral {
                val: lit.val,
                ty: expected,
            }
        }
        &Expr::FloatLiteral { span, .. } => {
            let lit = FloatLiteral::parse(&ast.src()[span.range()]);
            let info = lit.ty.map_or(TypeInfo::Float, |float| {
                TypeInfo::Instance(Primitive::from(float).into(), LocalTypeIds::EMPTY)
            });
            ctx.specify(expected, info, |_| span);
            Node::FloatLiteral {
                val: lit.val,
                ty: expected,
            }
        }
        &Expr::StringLiteral { span, .. } => {
            let str = super::get_string_literal(ctx.ast.src(), span);
            let str_ty = builtins::get_str(ctx.compiler);
            ctx.specify(expected, TypeInfo::Known(str_ty), |_| span);
            Node::StringLiteral(str)
        }
        &Expr::Array { span, elements, .. } => {
            let elem_ty_and_count = ctx.hir.types.specify_base(
                expected,
                BaseType::Array,
                2,
                ctx.generics,
                ctx.compiler,
                || ModuleSpan {
                    module: ctx.module,
                    span,
                },
                |types| {
                    types.add_multiple([TypeInfo::Unknown(Bounds::EMPTY), TypeInfo::UnknownConst])
                },
            );
            let elem_ty = elem_ty_and_count.nth(0).unwrap();
            let count = elem_ty_and_count.nth(1).unwrap();
            let const_count = ctx
                .compiler
                .types
                .intern(TypeFull::Const(elements.count as u64));
            ctx.specify(count, TypeInfo::Known(const_count), |_| span);
            let nodes = ctx.hir.add_invalid_nodes(elements.count);
            for (node, elem) in nodes.iter().zip(elements) {
                let elem_node = check(ctx, elem, scope, elem_ty, return_ty, noreturn);
                // TODO: can we return early here in case of noreturn?
                ctx.hir.modify_node(node, elem_node);
            }
            Node::ArrayLiteral {
                elems: nodes,
                array_ty: expected,
            }
        }
        Expr::Tuple { span, elements, .. } => {
            let elem_types = ctx.specify_base(expected, BaseType::Tuple, elements.count, |_| *span);
            let elems = ctx.hir.add_invalid_nodes(elements.count);
            for ((value, ty), node_id) in elements
                .into_iter()
                .zip(elem_types.iter())
                .zip(elems.iter())
            {
                let node = check(ctx, value, scope, ty, return_ty, noreturn);
                // TODO: can we return early here in case of noreturn?
                ctx.hir.modify_node(node_id, node);
            }
            Node::TupleLiteral { elems, elem_types }
        }
        &Expr::EnumLiteral {
            span, ident, args, ..
        } => check_enum_literal(ctx, scope, expected, return_ty, span, ident, args, noreturn),
        &Expr::Function { id } => {
            let function_span = ctx.ast[expr].span(ctx.ast);
            let (node, info) = closure(ctx, id, scope, function_span);
            ctx.specify(expected, info, |_| function_span);
            node
        }
        &Expr::Primitive { primitive, .. } => {
            ctx.specify(expected, TypeInfo::BaseTypeItem(primitive.into()), |ast| {
                ast[expr].span(ast)
            });
            Node::Invalid
        }
        &Expr::Type { id } => {
            let generic_count = ctx.ast[id].generic_count();
            let base =
                ctx.compiler
                    .add_type_def(ctx.module, id, "<anonymous type>".into(), generic_count);
            ctx.compiler.get_parsed_module(ctx.module).symbols.types[id.idx()]
                .set(base)
                .expect("Type defined multiple times");
            let span = ctx.ast[expr].span(ast);
            ctx.specify(expected, TypeInfo::BaseTypeItem(base), |_| span);
            Node::Invalid
        }
        &Expr::Trait { id } => {
            ctx.specify(
                expected,
                TypeInfo::TraitItem {
                    module: ctx.module,
                    id,
                },
                |ast| ast[expr].span(ast),
            );
            Node::Invalid
        }

        &Expr::Ident { span, .. } => check_ident(ctx, scope, expected, span),
        Expr::Declare { .. } => todo!("check variable declarations without values"),
        Expr::DeclareWithVal {
            pat,
            annotated_ty,
            val,
            ..
        } => {
            ctx.specify(expected, TypeInfo::UNIT, |ast| ast[expr].span(ast));
            let mut exhaustion = Exhaustion::None;
            let ty = ctx.hir.types.from_annotation(
                annotated_ty,
                ctx.compiler,
                ctx.module,
                scope.get_innermost_static_scope(),
            );
            let ty = ctx.hir.types.add(ty);
            let val = check(ctx, *val, scope, ty, return_ty, noreturn);
            let pattern = pattern::check(ctx, &mut scope.variables, &mut exhaustion, *pat, ty);
            if !exhaustion.is_trivially_exhausted() {
                ctx.deferred_exhaustions.push((exhaustion, ty, *pat));
            }
            Node::DeclareWithVal {
                pattern: ctx.hir.add_pattern(pattern),
                val: ctx.hir.add(val),
            }
        }
        Expr::Hole { .. } => {
            ctx.invalidate(expected);
            ctx.emit(Error::HoleLHSOnly.at_span(ctx.span(expr)));
            Node::Invalid
        }

        &Expr::UnOp { op, inner, .. } => {
            match op {
                UnOp::Neg => {
                    // TODO(trait): this should constrain the value with a trait
                    let value = check(ctx, inner, scope, expected, return_ty, noreturn);
                    Node::Negate(ctx.hir.add(value), expected)
                }
                UnOp::Not => {
                    ctx.specify(expected, ctx.primitives().bool_info(), |ast| {
                        ast[expr].span(ast)
                    });
                    let value = check(ctx, inner, scope, expected, return_ty, noreturn);
                    Node::Not(ctx.hir.add(value))
                }
                UnOp::Ref => {
                    let pointee = ctx
                        .specify_base(expected, BaseType::Pointer, 1, |ast| ast[expr].span(ast))
                        .nth(0)
                        .unwrap();
                    let value = check(ctx, inner, scope, pointee, return_ty, noreturn);
                    if let Some(lval) = LValue::try_from_node(&value, &mut ctx.hir) {
                        Node::AddressOf {
                            value: ctx.hir.add_lvalue(lval),
                            value_ty: pointee,
                        }
                    } else {
                        // promote the value to a variable
                        let promoted = ctx.hir.add_var(pointee);
                        Node::Promote {
                            value: ctx.hir.add(value),
                            variable: promoted,
                        }
                    }
                }
                UnOp::Deref => {
                    let ptr_ty = ctx
                        .hir
                        .types
                        .add(TypeInfo::Instance(BaseType::Pointer, expected.into()));
                    let value = check(ctx, inner, scope, ptr_ty, return_ty, noreturn);
                    Node::Deref {
                        value: ctx.hir.add(value),
                        deref_ty: expected,
                    }
                }
            }
        }
        &Expr::BinOp { op, l, r, .. } => {
            match op {
                Operator::Add | Operator::Sub | Operator::Mul | Operator::Div | Operator::Mod => {
                    // TODO: this will be have to bound/handled by traits
                    let l = check(ctx, l, scope, expected, return_ty, noreturn);
                    let r = check(ctx, r, scope, expected, return_ty, noreturn);
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
                    ctx.specify(expected, TypeInfo::UNIT, |ast| ast[expr].span(ast));
                    let (lval, ty) = lval::check(ctx, l, scope, return_ty, noreturn);
                    let val = check(ctx, r, scope, ty, return_ty, noreturn);
                    Node::Assign(ctx.hir.add_lvalue(lval), ctx.hir.add(val), assign_ty, ty)
                }
                Operator::Or | Operator::And => {
                    ctx.specify(expected, ctx.primitives().bool_info(), |ast| {
                        ast[expr].span(ast)
                    });
                    let l = check(ctx, l, scope, expected, return_ty, noreturn);
                    let r = check(ctx, r, scope, expected, return_ty, noreturn);
                    let l = ctx.hir.add(l);
                    let r = ctx.hir.add(r);
                    let logic = if op == Operator::Or {
                        Logic::Or
                    } else {
                        Logic::And
                    };
                    Node::Logic { l, r, logic }
                }
                Operator::Equals | Operator::NotEquals => {
                    ctx.specify(expected, ctx.primitives().bool_info(), |ast| {
                        ast[expr].span(ast)
                    });
                    let eq_trait = builtins::get_eq_trait(ctx.compiler);
                    let span = ctx.span(expr);
                    let bounds = ctx.hir.types.add_bounds([Bound {
                        trait_id: eq_trait,
                        generics: LocalTypeIds::EMPTY,
                        span,
                    }]);
                    let compared = ctx.hir.types.add(TypeInfo::Unknown(bounds));
                    let l = check(ctx, l, scope, compared, return_ty, noreturn);
                    let r = check(ctx, r, scope, compared, return_ty, noreturn);
                    let args = ctx.hir.add_nodes([l, r]);
                    let node = Node::TraitCall {
                        trait_id: eq_trait,
                        trait_generics: LocalTypeIds::EMPTY,
                        method_index: 0,
                        self_ty: compared,
                        args,
                        return_ty: expected,
                        noreturn: false,
                    };
                    if op == Operator::Equals {
                        node
                    } else {
                        Node::Not(ctx.hir.add(node))
                    }
                }
                Operator::LT | Operator::GT | Operator::LE | Operator::GE => {
                    ctx.specify(expected, ctx.primitives().bool_info(), |ast| {
                        ast[expr].span(ast)
                    });
                    // FIXME: this will have to be bound by type like Ord
                    let compared = ctx.hir.types.add_unknown();
                    let l = check(ctx, l, scope, compared, return_ty, noreturn);
                    let r = check(ctx, r, scope, compared, return_ty, noreturn);
                    let l = ctx.hir.add(l);
                    let r = ctx.hir.add(r);
                    let cmp = match op {
                        Operator::LT => Comparison::LT,
                        Operator::GT => Comparison::GT,
                        Operator::LE => Comparison::LE,
                        Operator::GE => Comparison::GE,
                        _ => unreachable!(),
                    };
                    Node::Comparison {
                        l,
                        r,
                        cmp,
                        compared,
                    }
                }
                Operator::Range | Operator::RangeExclusive => {
                    todo!("range types not implemented yet")
                }
            }
        }
        Expr::As {
            value, ty: new_ty, ..
        } => {
            let from_ty = ctx.hir.types.add_unknown();
            let val = check(ctx, *value, scope, from_ty, return_ty, noreturn);
            let val = ctx.hir.add(val);
            let new_type_info = ctx.hir.types.from_annotation(
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
        &Expr::Root { .. } => {
            let root_module = ctx.compiler.get_root_module(ctx.module);
            ctx.specify(expected, TypeInfo::ModuleItem(root_module), |ast| {
                ast[expr].span(ast)
            });
            Node::Invalid
        }
        &Expr::MemberAccess {
            left,
            name: name_span,
            ..
        } => check_member_access(
            ctx, left, name_span, expr, scope, expected, return_ty, noreturn,
        ),
        &Expr::Index { expr, idx, .. } => {
            let elem_and_count = ctx.hir.types.add_multiple_info_or_idx([
                TypeInfoOrIdx::Idx(expected),
                TypeInfo::UnknownConst.into(),
            ]);
            let array_ty = ctx
                .hir
                .types
                .add(TypeInfo::Instance(BaseType::Array, elem_and_count));
            let array = check(ctx, expr, scope, array_ty, return_ty, noreturn);
            let index_ty = ctx.hir.types.add(TypeInfo::Integer);
            let index = check(ctx, idx, scope, index_ty, return_ty, noreturn);
            Node::ArrayIndex {
                array: ctx.hir.add(array),
                index: ctx.hir.add(index),
                elem_ty: expected,
            }
        }
        &Expr::TupleIdx { left, idx, .. } => {
            let tuple_ty = ctx.hir.types.add_unknown(); // add Size::AtLeast tuple here maybe
            let tuple_value = check(ctx, left, scope, tuple_ty, return_ty, noreturn);
            match ctx.hir.types[tuple_ty] {
                TypeInfo::Instance(BaseType::Tuple, elem_types) => {
                    return if let Some(elem_ty) = elem_types.nth(idx) {
                        ctx.unify(expected, elem_ty, |ast| ast[expr].span(ast));
                        Node::Element {
                            tuple_value: ctx.hir.add(tuple_value),
                            index: idx,
                            elem_types,
                        }
                    } else {
                        ctx.emit(Error::TupleIndexOutOfRange.at_span(ctx.span(expr)));
                        Node::Invalid
                    };
                }
                TypeInfo::Instance(BaseType::Invalid, _) => return Node::Invalid,
                TypeInfo::Known(ty) => {
                    if let TypeFull::Instance(BaseType::Tuple, elem_types) =
                        ctx.compiler.types.lookup(ty)
                    {
                        return if let Some(&elem_ty) = elem_types.get(idx as usize) {
                            ctx.specify(expected, TypeInfo::Known(elem_ty), |ast| {
                                ast[expr].span(ast)
                            });
                            let elem_types = ctx
                                .hir
                                .types
                                .add_multiple(elem_types.iter().copied().map(TypeInfo::Known));
                            Node::Element {
                                tuple_value: ctx.hir.add(tuple_value),
                                index: idx,
                                elem_types,
                            }
                        } else {
                            ctx.emit(Error::TupleIndexOutOfRange.at_span(ctx.span(expr)));
                            Node::Invalid
                        };
                    };
                }
                _ => {}
            };

            // FIXME: emit invalid type error on a known but wrong type
            // TODO: could add TupleCountMode and stuff again to unify with tuple with
            // Size::AtLeast. Not doing that for now since it is very rare.
            ctx.emit(Error::TypeMustBeKnownHere { needed_bound: None }.at_span(ctx.span(left)));
            ctx.invalidate(expected);
            Node::Invalid
        }

        Expr::ReturnUnit { .. } => {
            ctx.specify(return_ty, TypeInfo::UNIT, |ast| ast[expr].span(ast));
            Node::Return(ctx.hir.add(Node::Unit))
        }
        &Expr::Return { val, .. } => {
            let val = check(ctx, val, scope, return_ty, return_ty, noreturn);
            *noreturn = true;
            Node::Return(ctx.hir.add(val))
        }

        // FIXME: some code duplication going on with the 4 different If variants
        &Expr::If { cond, then, .. } => {
            ctx.specify(expected, TypeInfo::UNIT, |ast| ast[expr].span(ast));
            let bool_ty = ctx.hir.types.add(ctx.primitives().bool_info());
            let cond = check(ctx, cond, scope, bool_ty, return_ty, noreturn);
            let then = check(ctx, then, scope, expected, return_ty, &mut false);
            Node::IfElse {
                cond: ctx.hir.add(cond),
                then: ctx.hir.add(then),
                else_: ctx.hir.add(Node::Unit),
                resulting_ty: expected,
            }
        }
        &Expr::IfElse {
            cond, then, else_, ..
        } => {
            let bool_ty = ctx.hir.types.add(ctx.primitives().bool_info());
            let cond = check(ctx, cond, scope, bool_ty, return_ty, noreturn);
            let mut then_noreturn = false;
            let then = check(ctx, then, scope, expected, return_ty, &mut then_noreturn);
            let mut else_noreturn = false;
            let else_ = check(ctx, else_, scope, expected, return_ty, &mut else_noreturn);
            if then_noreturn && else_noreturn {
                *noreturn = true;
            }
            Node::IfElse {
                cond: ctx.hir.add(cond),
                then: ctx.hir.add(then),
                else_: ctx.hir.add(else_),
                resulting_ty: expected,
            }
        }
        &Expr::IfPat {
            pat, value, then, ..
        } => {
            ctx.specify(expected, TypeInfo::UNIT, |ast| ast[expr].span(ast));
            let pattern_ty = ctx.hir.types.add_unknown();
            let value = check(ctx, value, scope, pattern_ty, return_ty, noreturn);
            let mut body_scope = LocalScope {
                module: scope.module,
                parent: LocalScopeParent::Some(scope),
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
            let then = check(ctx, then, &mut body_scope, expected, return_ty, &mut false);
            Node::IfPatElse {
                pat: ctx.hir.add_pattern(pat),
                val: ctx.hir.add(value),
                then: ctx.hir.add(then),
                else_: ctx.hir.add(Node::Unit),
                resulting_ty: expected,
            }
        }
        &Expr::IfPatElse {
            pat,
            value,
            then,
            else_,
            ..
        } => {
            let pattern_ty = ctx.hir.types.add_unknown();
            let value = check(ctx, value, scope, pattern_ty, return_ty, noreturn);
            let mut body_scope = LocalScope {
                module: scope.module,
                parent: LocalScopeParent::Some(scope),
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
            let pat = ctx.hir.add_pattern(pat);
            let val = ctx.hir.add(value);
            let mut then_noreturn = false;
            let then = check(
                ctx,
                then,
                &mut body_scope,
                expected,
                return_ty,
                &mut then_noreturn,
            );
            let mut else_noreturn = false;
            let else_ = check(
                ctx,
                else_,
                &mut body_scope,
                expected,
                return_ty,
                &mut else_noreturn,
            );
            if then_noreturn && else_noreturn {
                *noreturn = true;
            }
            Node::IfPatElse {
                pat,
                val,
                then: ctx.hir.add(then),
                else_: ctx.hir.add(else_),
                resulting_ty: expected,
            }
        }
        &Expr::Match { val, branches, .. } => {
            let branch_count = branches.pair_count();
            let matched_ty = ctx.hir.types.add_unknown();
            let value = check(ctx, val, scope, matched_ty, return_ty, noreturn);
            let value = ctx.hir.add(value);
            let mut vars = dmap::new();
            let mut exhaustion = Exhaustion::None;
            let patterns = ctx.hir.add_invalid_patterns(branch_count);
            let branch_nodes = ctx.hir.add_invalid_nodes(branch_count);
            let mut all_branches_noreturn = true;
            for ((pat, branch), i) in branches.into_iter().zip(0..) {
                vars.clear();
                let pat = pattern::check(ctx, &mut vars, &mut exhaustion, pat, matched_ty);
                ctx.hir
                    .modify_pattern(hir::PatternId(patterns.index + i), pat);
                let mut scope = LocalScope {
                    parent: LocalScopeParent::Some(scope),
                    variables: vars,
                    module: scope.module,
                    static_scope: None,
                };
                let mut branch_noreturn = false;
                let branch = check(
                    ctx,
                    branch,
                    &mut scope,
                    expected,
                    return_ty,
                    &mut branch_noreturn,
                );
                if !branch_noreturn {
                    all_branches_noreturn = false;
                }
                vars = scope.variables;
                ctx.hir
                    .modify_node(hir::NodeId(branch_nodes.index + i), branch);
            }
            if all_branches_noreturn {
                *noreturn = true;
            }
            Node::Match {
                value,
                branch_index: branch_nodes.index,
                pattern_index: patterns.index,
                branch_count,
                resulting_ty: expected,
            }
        }
        &Expr::While { cond, body, .. } => {
            let bool_ty = ctx.hir.types.add(ctx.primitives().bool_info());
            let cond = check(ctx, cond, scope, bool_ty, return_ty, noreturn);
            let body_ty = ctx.hir.types.add_unknown();
            ctx.control_flow_stack.push(());
            let body = check(ctx, body, scope, body_ty, return_ty, &mut false);
            ctx.control_flow_stack.pop();
            Node::While {
                cond: ctx.hir.add(cond),
                body: ctx.hir.add(body),
            }
        }
        &Expr::WhilePat { pat, val, body, .. } => {
            ctx.control_flow_stack.push(());
            let value_ty = ctx.hir.types.add_unknown();
            let val = check(ctx, val, scope, value_ty, return_ty, noreturn);
            let mut body_scope = LocalScope {
                parent: LocalScopeParent::Some(scope),
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
            let pat = ctx.hir.add_pattern(pat);
            let val = ctx.hir.add(val);
            let body_ty = ctx.hir.types.add_unknown();
            ctx.control_flow_stack.push(());
            let body = check(ctx, body, &mut body_scope, body_ty, return_ty, &mut false);
            ctx.control_flow_stack.pop();
            Node::WhilePat {
                pat,
                val,
                body: ctx.hir.add(body),
            }
        }
        &Expr::For {
            pat, iter, body, ..
        } => {
            let iterator_trait = builtins::get_iterator(ctx.compiler);
            let option_ty = builtins::get_option(ctx.compiler);
            let some_variant_types = ctx.hir.types.add_multiple([
                TypeInfo::from(Primitive::U8),
                TypeInfo::Unknown(Bounds::EMPTY),
            ]);
            let item_ty = some_variant_types.nth(1).unwrap();
            let bounds = ctx.hir.types.add_bounds([Bound {
                trait_id: iterator_trait,
                generics: item_ty.into(),
                span: ctx.ast[iter].span(ctx.ast),
            }]);
            let iter_ty = ctx.hir.types.add(TypeInfo::Unknown(bounds));
            let iter = check(ctx, iter, scope, iter_ty, return_ty, noreturn);
            let iter_var_id = ctx.hir.add_var(iter_ty);
            let decl_iter_var = Node::DeclareWithVal {
                pattern: ctx.hir.add_pattern(Pattern::Variable(iter_var_id)),
                val: ctx.hir.add(iter),
            };

            let mut body_scope = LocalScope {
                parent: LocalScopeParent::Some(scope),
                module: scope.module,
                variables: dmap::new(),
                static_scope: None,
            };
            let option_item_ty = ctx
                .hir
                .types
                .add(TypeInfo::Instance(option_ty, item_ty.into()));
            let iter_var_ref = Node::AddressOf {
                value: ctx.hir.add_lvalue(LValue::Variable(iter_var_id)),
                value_ty: iter_ty,
            };
            let next_call = Node::TraitCall {
                trait_id: iterator_trait,
                trait_generics: item_ty.into(),
                method_index: 0, // TODO: don't hardcode index of next method
                self_ty: iter_ty,
                args: ctx.hir.add(iter_var_ref).into(),
                return_ty: option_item_ty,
                noreturn: false,
            };
            let mut exhaustion = Exhaustion::None;
            let pat_item_node = pattern::check(
                ctx,
                &mut body_scope.variables,
                &mut exhaustion,
                pat,
                item_ty,
            );
            if exhaustion.is_trivially_exhausted() {
                ctx.deferred_exhaustions.push((exhaustion, item_ty, pat));
            }
            // TODO: don't hardcode 0 for Some
            let pat_node = Pattern::EnumVariant {
                ordinal: OrdinalType::Known(0),
                types: some_variant_types.idx,
                args: ctx.hir.add_pattern(pat_item_node).into(),
            };
            let body_ty = ctx.hir.types.add_unknown();
            let mut body_noreturn = false;
            ctx.control_flow_stack.push(());
            let body = check(
                ctx,
                body,
                &mut body_scope,
                body_ty,
                return_ty,
                &mut body_noreturn,
            );
            ctx.control_flow_stack.pop();
            let loop_node = Node::WhilePat {
                pat: ctx.hir.add_pattern(pat_node),
                val: ctx.hir.add(next_call),
                body: ctx.hir.add(body),
            };
            Node::Block(ctx.hir.add_nodes([decl_iter_var, loop_node]))
        }
        &Expr::FunctionCall(call) => {
            call::check_call(ctx, &ast[call], expr, scope, expected, return_ty, noreturn)
        }
        Expr::Asm { .. } => todo!("implement inline assembly properly"),
        Expr::Break { .. } => {
            if ctx.control_flow_stack.is_empty() {
                ctx.emit(Error::BreakOutsideLoop.at_span(ctx.span(expr)));
                return Node::Invalid;
            }
            Node::Break(0)
        }
        Expr::Continue { .. } => {
            if ctx.control_flow_stack.is_empty() {
                ctx.emit(Error::ContinueOutsideLoop.at_span(ctx.span(expr)));
                return Node::Invalid;
            }
            Node::Continue(0)
        }
    }
}

fn check_ident(
    ctx: &mut Ctx<'_>,
    scope: &mut LocalScope<'_>,
    expected: LocalTypeId,
    span: TSpan,
) -> Node {
    let name = &ctx.ast[span];
    match scope.resolve(name, span, ctx.compiler) {
        LocalItem::Var(var) => {
            let ty = ctx.hir.get_var(var);
            ctx.unify(expected, ty, |_| span);
            Node::Variable(var)
        }
        LocalItem::Def(def) => def_to_node(ctx, def, expected, span),
        LocalItem::Capture(id, ty) => {
            ctx.unify(expected, ty, |_| span);
            Node::Capture(id)
        }
        LocalItem::Invalid => {
            ctx.specify(expected, TypeInfo::INVALID, |_| span);
            ctx.invalidate(expected);
            Node::Invalid
        }
    }
}

fn def_to_node(ctx: &mut Ctx, def: Def, expected: LocalTypeId, span: TSpan) -> Node {
    match def {
        Def::Invalid => {
            ctx.specify(expected, TypeInfo::INVALID, |_| span);
            Node::Invalid
        }
        Def::Function(module, id) => function_item(ctx, module, id, expected, span),
        Def::BaseType(id) => {
            ctx.specify(expected, TypeInfo::BaseTypeItem(id), |_| span);
            Node::Invalid
        }
        Def::Type(ty) => {
            let ty = ctx.hir.types.add(TypeInfo::Known(ty));
            ctx.specify(expected, TypeInfo::TypeItem(ty), |_| span);
            Node::Invalid
        }
        Def::Trait(module, id) => {
            ctx.specify(expected, TypeInfo::TraitItem { module, id }, |_| span);
            Node::Invalid
        }
        Def::ConstValue(const_val) => const_value_to_node(ctx, expected, const_val, span),
        Def::Module(id) => {
            ctx.specify(expected, TypeInfo::ModuleItem(id), |_| span);
            Node::Invalid
        }
        Def::Global(module, id) => {
            let (_, ty) = ctx.compiler.get_checked_global(module, id);
            // PERF: cloning type
            let ty = *ty;
            ctx.specify_resolved(expected, ty, LocalTypeIds::EMPTY, |_| span);
            Node::Global(module, id, expected)
        }
    }
}

fn const_value_to_node(
    ctx: &mut Ctx,
    expected: LocalTypeId,
    const_val: ConstValueId,
    span: TSpan,
) -> Node {
    let (_, ty) = &ctx.compiler.const_values[const_val.idx()];
    // PERF: clone of Type
    let ty = *ty;
    ctx.specify_resolved(expected, ty, LocalTypeIds::EMPTY, |_| span);
    Node::Const {
        id: const_val,
        ty: expected,
    }
}

fn check_enum_literal(
    ctx: &mut Ctx,
    scope: &mut LocalScope,
    expected: LocalTypeId,
    return_ty: LocalTypeId,
    span: TSpan,
    ident: TSpan,
    args: ExprIds,
    noreturn: &mut bool,
) -> Node {
    let name = &ctx.ast[ident];
    let res =
        ctx.hir
            .types
            .specify_enum_literal(expected, name, args.count, ctx.compiler, ctx.generics);
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
                let arg_node = check(ctx, arg, scope, ty, return_ty, noreturn);
                ctx.hir.modify_node(r, arg_node);
            }
            Node::EnumLiteral {
                elems: arg_nodes,
                elem_types: arg_type_ids,
                enum_ty: expected,
            }
        }
        Err(err) => {
            ctx.invalidate(expected);
            if let Some(err) = err {
                ctx.emit(err.at_span(span));
            }
            // the expected type was invalid, still check the arguments against an unknown type
            for arg in args.into_iter() {
                let ty = ctx.hir.types.add_unknown();
                check(ctx, arg, scope, ty, return_ty, noreturn);
            }
            Node::Invalid
        }
    }
}

fn function_item(
    ctx: &mut Ctx,
    function_module: ModuleId,
    function: FunctionId,
    expected: LocalTypeId,
    span: TSpan,
) -> Node {
    let signature = ctx.compiler.get_signature(function_module, function);
    let generics = signature
        .generics
        .instantiate(&mut ctx.hir.types, &ctx.compiler.types, span);
    ctx.specify(
        expected,
        TypeInfo::FunctionItem {
            module: function_module,
            function,
            generics,
        },
        |_| span,
    );
    Node::FunctionItem(function_module, function, generics)
}

fn check_member_access(
    ctx: &mut Ctx,
    left: ExprId,
    name_span: TSpan,
    expr: ExprId,
    scope: &mut LocalScope,
    expected: LocalTypeId,
    return_ty: LocalTypeId,
    noreturn: &mut bool,
) -> Node {
    let left_ty = ctx.hir.types.add_unknown();
    let left_node = check(ctx, left, scope, left_ty, return_ty, noreturn);
    let name = &ctx.ast.src()[name_span.range()];
    match ctx.hir.types[left_ty] {
        TypeInfo::BaseTypeItem(base) => {
            let generic_count = ctx.compiler.types.get_base(base).generic_count;
            let generics = ctx.hir.types.add_multiple_unknown(generic_count.into());
            let type_var = ctx.hir.types.add(TypeInfo::Instance(base, generics));
            return check_type_item_member_access(
                ctx,
                type_var,
                name,
                name_span,
                expected,
                left,
                |ast| ast[expr].span(ast),
            );
        }
        TypeInfo::TypeItem(var) => {
            return check_type_item_member_access(
                ctx,
                var,
                name,
                name_span,
                expected,
                left,
                |ast| ast[expr].span(ast),
            );
        }
        TypeInfo::TraitItem { module, id } => {
            let Some(checked) = ctx.compiler.get_checked_trait(module, id) else {
                // invalid definition, error was already emitted
                return Node::Invalid;
            };
            let Some(&method_index) = checked.functions_by_name.get(name) else {
                ctx.emit(Error::NonexistantMember(None).at_span(name_span));
                ctx.invalidate(expected);
                return Node::Invalid;
            };
            ctx.specify(
                expected,
                TypeInfo::TraitMethodItem {
                    module,
                    trait_id: id,
                    method_index,
                },
                |ast| ast[expr].span(ast),
            );
            return Node::Invalid;
        }
        TypeInfo::ModuleItem(id) => {
            let def = ctx.compiler.resolve_in_module(
                id,
                name,
                ModuleSpan {
                    module: ctx.module,
                    span: name_span,
                },
            );
            return def_to_node(ctx, def, expected, name_span);
        }
        _ => {}
    }
    // now check the type while allowing auto deref for field access, methods
    let mut current_ty = ctx.hir.types[left_ty];
    let mut pointer_count = 0;
    loop {
        match current_ty {
            TypeInfo::Instance(BaseType::Pointer, pointee) => {
                pointer_count += 1;
                current_ty = ctx.hir.types[pointee.nth(0).unwrap()];
            }
            TypeInfo::Instance(BaseType::Invalid, _) => {
                ctx.invalidate(expected);
                return Node::Invalid;
            }
            TypeInfo::Known(ty) => match ctx.compiler.types.lookup(ty) {
                TypeFull::Instance(BaseType::Pointer, &[pointee]) => {
                    pointer_count += 1;
                    current_ty = TypeInfo::Known(pointee);
                }
                TypeFull::Instance(base, generics) => {
                    let generics = ctx
                        .hir
                        .types
                        .add_multiple(generics.iter().map(|&ty| TypeInfo::Known(ty)));
                    return instance_member(
                        ctx,
                        name_span,
                        expr,
                        expected,
                        pointer_count,
                        left_node,
                        left_ty,
                        base,
                        generics,
                    );
                }
                TypeFull::Generic(_) | TypeFull::Const(_) => {
                    ctx.emit(Error::NonexistantMember(None).at_span(name_span));
                    ctx.invalidate(expected);
                    return Node::Invalid;
                }
            },
            TypeInfo::Instance(base, generics) => {
                return instance_member(
                    ctx,
                    name_span,
                    expr,
                    expected,
                    pointer_count,
                    left_node,
                    left_ty,
                    base,
                    generics,
                );
            }
            TypeInfo::Unknown(bounds) => {
                ctx.emit_unknown(bounds, ctx.span(left));
                ctx.invalidate(expected);
                return Node::Invalid;
            }
            other => {
                let hint =
                    matches!(other, TypeInfo::Enum(_)).then_some(error::MemberHint::InferredEnum);
                ctx.emit(Error::NonexistantMember(hint).at_span(name_span));
                ctx.invalidate(expected);
                return Node::Invalid;
            }
        }
    }
}

fn instance_member(
    ctx: &mut Ctx,
    name_span: TSpan,
    expr: ExprId,
    expected: LocalTypeId,
    pointer_count: u32,
    left_node: Node,
    left_ty: LocalTypeId,
    base: BaseType,
    generics: LocalTypeIds,
) -> Node {
    let name = &ctx.ast[name_span];
    let resolved = ctx.compiler.get_base_type_def(base);
    if let Some(&method) = resolved.methods.get(name) {
        let module = resolved.module;
        let signature = ctx.compiler.get_signature(module, method);
        let Some((required_pointer_count, call_generics)) =
            check_is_instance_method(signature, base, generics, ctx, |ast| ast[expr].span(ast))
        else {
            ctx.emit(Error::NotAnInstanceMethod.at_span(ctx.span(expr)));
            ctx.invalidate(expected);
            return Node::Invalid;
        };
        let self_value =
            ctx.auto_ref_deref(pointer_count, required_pointer_count, left_node, left_ty);
        ctx.specify(
            expected,
            TypeInfo::MethodItem {
                module,
                function: method,
                generics: call_generics,
            },
            |ast| ast[expr].span(ast),
        );
        return self_value;
    }
    if let ResolvedTypeContent::Struct(def) = &resolved.def {
        let (indexed_field, elem_types) = def.get_indexed_field(ctx, generics, name);
        if let Some((index, field_ty)) = indexed_field {
            // perform auto deref first
            let mut dereffed_node = left_node;
            let mut current_ty = ctx.hir.types[left_ty];
            for _ in 0..pointer_count {
                // the deref was already checked so we know the type is wrapped in
                // `pointer_count` pointers
                let pointee = match current_ty {
                    TypeInfo::Instance(BaseType::Pointer, pointee) => {
                        let pointee = pointee.nth(0).unwrap();
                        current_ty = ctx.hir.types[pointee];
                        pointee
                    }
                    TypeInfo::Known(ty) => {
                        let TypeFull::Instance(BaseType::Pointer, &[pointee]) =
                            ctx.compiler.types.lookup(ty)
                        else {
                            unreachable!()
                        };
                        current_ty = TypeInfo::Known(pointee);
                        ctx.hir.types.add(TypeInfo::Known(pointee))
                    }
                    _ => unreachable!(),
                };
                let value = ctx.hir.add(dereffed_node);
                dereffed_node = Node::Deref {
                    value,
                    deref_ty: pointee,
                };
            }
            ctx.unify(expected, field_ty, |ast| ast[expr].span(ast));
            return Node::Element {
                tuple_value: ctx.hir.add(dereffed_node),
                index,
                elem_types,
            };
        }
    }
    ctx.emit(Error::NonexistantMember(None).at_span(name_span));
    ctx.invalidate(expected);
    Node::Invalid
}

/// checks if the provided method signature is valid as an instance method of the provided type.
/// Returns the number of pointer indirections of the self type and the call's generics
/// or None if the function is not a valid instance method.
fn check_is_instance_method(
    signature: &crate::compiler::Signature,
    id: BaseType,
    generics: LocalTypeIds,
    ctx: &mut Ctx,
    span: impl Copy + FnOnce(&Ast) -> TSpan,
) -> Option<(u32, LocalTypeIds)> {
    let (_, self_param_ty) = signature.all_params().next()?;
    let call_generics = create_method_call_generics(
        &mut ctx.hir.types,
        &ctx.compiler.types,
        signature,
        generics,
        span(ctx.ast),
    );
    let mut required_pointer_count = 0;
    let mut current_ty = self_param_ty;
    loop {
        match ctx.compiler.types.lookup(current_ty) {
            TypeFull::Instance(BaseType::Pointer, pointee) => {
                required_pointer_count += 1;
                current_ty = pointee[0];
            }
            TypeFull::Instance(base, signature_generics) if id == base => {
                // generics count should always matched because the type is already checked and
                // resolved
                debug_assert_eq!(generics.count as usize, signature_generics.len());
                for (ty, &signature_ty) in generics.iter().zip(signature_generics) {
                    ctx.hir.types.specify_type_instance(
                        ty,
                        signature_ty,
                        generics,
                        ctx.generics,
                        ctx.compiler,
                        || ModuleSpan {
                            module: ctx.module,
                            span: span(ctx.ast),
                        },
                    );
                }
                return Some((required_pointer_count, call_generics));
            }
            _ => {
                return None;
            }
        }
    }
}

fn create_method_call_generics(
    table: &mut TypeTable,
    types: &Types,
    signature: &crate::compiler::Signature,
    type_generics: LocalTypeIds,
    span: TSpan,
) -> LocalTypeIds {
    if signature.generics.count() as u32 != type_generics.count {
        debug_assert!(signature.generics.count() as u32 > type_generics.count);
        // perf: instantiates the outer type's generics again unnecessarily
        let call_generics = signature.generics.instantiate(table, types, span);
        for (r, generic) in call_generics.iter().zip(type_generics.iter()) {
            table.replace(r, generic);
        }
        call_generics
    } else {
        type_generics
    }
}

fn check_type_item_member_access(
    ctx: &mut Ctx,
    ty: LocalTypeId,
    name: &str,
    name_span: TSpan,
    expected: LocalTypeId,
    left: ExprId,
    span: impl Copy + Fn(&Ast) -> TSpan,
) -> Node {
    // first check if the member is a special type property
    if let Some(property) = hir::TypeProperty::from_name(name) {
        // TODO: usize type
        ctx.specify(expected, Primitive::U64, span);
        return Node::TypeProperty(ty, property);
    }
    match ctx.hir.types[ty] {
        TypeInfo::Instance(BaseType::Invalid, _) => return Node::Invalid,
        TypeInfo::Instance(base, generics) => {
            return instance_type_item_member_access(
                ctx, base, generics, name, name_span, expected, span,
            );
        }
        TypeInfo::Known(ty) => {
            if let TypeFull::Instance(base, generics) = ctx.compiler.types.lookup(ty) {
                let generics = ctx
                    .hir
                    .types
                    .add_multiple(generics.iter().map(|&ty| TypeInfo::Known(ty)));
                return instance_type_item_member_access(
                    ctx, base, generics, name, name_span, expected, span,
                );
            }
        }
        TypeInfo::Enum { .. } => todo!("local enum variant from type item"),
        TypeInfo::Unknown(bounds) => {
            let needed_bound = bounds.iter().next().map(|bound| {
                let id = ctx.hir.types.get_bound(bound).trait_id;
                ctx.compiler.get_trait_name(id.0, id.1).to_owned()
            });
            ctx.emit(Error::TypeMustBeKnownHere { needed_bound }.at_span(ctx.span(left)));
            return Node::Invalid;
        }
        _ => {}
    };
    ctx.emit(Error::NonexistantMember(None).at_span(name_span));
    ctx.invalidate(expected);
    Node::Invalid
}

fn instance_type_item_member_access(
    ctx: &mut Ctx,
    base: BaseType,
    generics: LocalTypeIds,
    name: &str,
    name_span: TSpan,
    expected: LocalTypeId,
    span: impl Copy + Fn(&Ast) -> TSpan,
) -> Node {
    let ty = ctx.compiler.get_base_type_def(base);
    if let Some(&method) = ty.methods.get(name) {
        let module = ty.module;
        let signature = ctx.compiler.get_signature(module, method);
        let call_generics = create_method_call_generics(
            &mut ctx.hir.types,
            &ctx.compiler.types,
            signature,
            generics,
            span(ctx.ast),
        );
        ctx.specify(
            expected,
            TypeInfo::FunctionItem {
                module,
                function: method,
                generics: call_generics,
            },
            span,
        );
        return Node::FunctionItem(module, method, call_generics);
    }
    if let ResolvedTypeContent::Enum(def) = &ty.def
        && let Some((_, ordinal, args)) = def.get_by_name(name)
    {
        let ordinal_ty = type_info_from_variant_count(def.variants.len() as u32);
        let node = if args.is_empty() {
            ctx.specify(expected, TypeInfo::Instance(base, generics), span);
            let ordinal_ty = ctx.hir.types.add(ordinal_ty);
            let elem_types = ctx.hir.types.add_multiple_info_or_idx([ordinal_ty.into()]);
            let elems = ctx.hir.add_nodes([Node::IntLiteral {
                val: ordinal as u128,
                ty: ordinal_ty,
            }]);
            Node::TupleLiteral { elems, elem_types }
        } else {
            let arg_types = ctx.hir.types.add_multiple_unknown(args.len() as u32 + 1);
            let mut arg_type_iter = arg_types.iter();
            ctx.hir
                .types
                .replace(arg_type_iter.next().unwrap(), ordinal_ty);
            for (r, &ty) in arg_type_iter.zip(args.iter()) {
                let ty = ctx.from_type_instance(ty, generics);
                ctx.hir.types.replace(r, ty);
            }
            ctx.specify(
                expected,
                TypeInfo::EnumVariantItem {
                    enum_type: base,
                    generics,
                    ordinal,
                    arg_types,
                },
                span,
            );
            Node::Invalid
        };
        return node;
    }
    ctx.emit(Error::NonexistantMember(None).at_span(name_span));
    ctx.invalidate(expected);
    Node::Invalid
}

pub fn type_from_variant_count(count: u32) -> Type {
    int_primitive_from_variant_count(count).map_or(Type::Unit, Type::from)
}

pub fn type_info_from_variant_count(count: u32) -> TypeInfo {
    int_primitive_from_variant_count(count).map_or(TypeInfo::UNIT, |p| {
        TypeInfo::Instance(p.into(), LocalTypeIds::EMPTY)
    })
}

pub fn int_primitive_from_variant_count(count: u32) -> Option<Primitive> {
    match count {
        0 | 1 => None,
        2..=255 => Some(Primitive::U8),
        256..=65535 => Some(Primitive::U16),
        _ => Some(Primitive::U32),
    }
}
