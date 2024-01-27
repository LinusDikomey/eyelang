mod cast;
mod exhaust;

use dmap::DHashMap;
use id::ModuleId;
use span::TSpan;
use types::{Primitive, Type};

use crate::{
    Compiler,
    parser::{ast::{Ast, ExprId, Expr, UnOp, FunctionId}, token::{IntLiteral, Operator, AssignType}},
    compiler::{LocalScope, LocalItem, Def, VarId, Signature},
    type_table::{TypeInfo, LocalTypeId, TypeTable},
    eval::ConstValue,
    hir::{HIRBuilder, Node, Pattern, HIR, CastId, Cast, CastType, LValue}, error::{Error, CompileError},
};

use self::exhaust::Exhaustion;

pub struct Ctx<'a> {
    pub compiler: &'a mut Compiler,
    pub ast: &'a Ast,
    pub module: ModuleId,
    pub hir: HIRBuilder,
    /// Exhaustion value, type, pattern expr
    pub deferred_exhaustions: Vec<(Exhaustion, LocalTypeId, ExprId)>,
    /// from, to, cast_expr
    pub deferred_casts: Vec<(LocalTypeId, LocalTypeId, ExprId, CastId)>,
}
impl<'a> Ctx<'a> {
    fn span(&self, expr: ExprId) -> span::Span {
        self.ast[expr].span_in(self.ast, self.module)
    }

    fn specify(&mut self, ty: LocalTypeId, info: impl Into<TypeInfo>, span: impl FnOnce(&Ast) -> TSpan) {
        self.hir.types.specify(
            ty,
            info.into(),
            &mut self.compiler.errors,
            || span(self.ast).in_mod(self.module),
        )
    }

    fn unify(&mut self, a: LocalTypeId, b: LocalTypeId, span: impl FnOnce(&Ast) -> TSpan) {
        self.hir.types.unify(a, b, &mut self.compiler.errors, || span(self.ast).in_mod(self.module))
    }

    fn invalidate(&mut self, ty: LocalTypeId) {
        self.hir.types.invalidate(ty);
    }

    pub(crate) fn finish(self, root: Node) -> (HIR, TypeTable) {
        // TODO: finalize types?
        let (mut hir, types) = self.hir.finish(root);
        for (exhaustion, ty, pat) in self.deferred_exhaustions {
            if let Some(false) = exhaustion.is_exhausted(types[ty], &types, self.compiler) {
                let error = Error::Inexhaustive.at_span(self.ast[pat].span_in(&self.ast, self.module));
                self.compiler.errors.emit_err(error)
            }
        }
        for (from_ty, to_ty, cast_expr, cast_id) in self.deferred_casts {
            let res = cast::check(from_ty, to_ty, &types,
                || self.ast[cast_expr].span_in(self.ast, self.module));
            match res {
                Result::Ok(cast_ty) => hir[cast_id].cast_ty = cast_ty,
                Result::Err(Some(err)) => {
                    // cast_ty of this cast should be set to invalid by default, we are just
                    // leaving it that way
                    self.compiler.errors.emit_err(err);
                }
                Result::Err(None) => {}
            }
        }
        (hir, types)
    }
}

pub fn check_expr(
    ctx: &mut Ctx,
    expr: ExprId,
    scope: &mut LocalScope,
    expected: LocalTypeId,
    return_ty: LocalTypeId,
) -> Node {
    let ast = ctx.ast;
    match &ast[expr] {
        Expr::IntLiteral(span) => {
            let lit = IntLiteral::parse(&ast.src()[span.range()]);
            let info = lit.ty.map_or(
                TypeInfo::Integer,
                |int| TypeInfo::Primitive(int.into()),
            );
            ctx.specify(expected, info, |_| *span);
            Node::IntLiteral { val: lit.val, ty: expected }
        }
        &Expr::Ident { span } => {
            let name = &ast[span];
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
                    Def::Function(module, id) => function_item(ctx, module, id, expected, expr),
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
                                    TypeInfo::Primitive(Primitive::I32),
                                    |_| span,
                                );
                            }
                        }
                        Node::Const(const_val)
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
        Expr::ReturnUnit { .. } => {
            ctx.specify(return_ty, TypeInfo::Primitive(Primitive::Unit), |ast| ast[expr].span(ast));
            Node::Return(ctx.hir.add(Node::Unit))
        }
        &Expr::Return { val, .. } => {
            let val = check_expr(ctx, val, scope, return_ty, return_ty);
            Node::Return(ctx.hir.add(val))
        }
        &Expr::Function { id } => function_item(ctx, ctx.module, id, expected, expr),
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
                    check_expr(ctx, item, &mut scope, unknown, return_ty)
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
            let val = check_expr(ctx, *val, scope, ty, return_ty);
            let pattern = check_pat(ctx, &mut scope.variables, &mut exhaustion, *pat, ty);
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
                    todo!("arith ops")
                }
                Operator::Assignment(AssignType::Assign) => {
                    ctx.specify(expected, Primitive::Unit, |ast| ast[expr].span(ast));
                    let (lval, ty) = check_lval(ctx, l, scope);
                    let val = check_expr(ctx, r, scope, ty, return_ty);
                    Node::Assign(ctx.hir.add_lvalue(lval), ctx.hir.add(val))
                }
                Operator::Assignment(_ty) => todo!("assignment-op type checking"),
                Operator::Or | Operator::And => {
                    ctx.specify(expected, Primitive::Bool, |ast| ast[expr].span(ast));
                    let l = check_expr(ctx, l, scope, expected, return_ty);
                    let r = check_expr(ctx, r, scope, expected, return_ty);
                    let l = ctx.hir.add(l);
                    let r = ctx.hir.add(r);
                    if op == Operator::Or {
                        Node::Or(l, r)
                    } else {
                        Node::And(l, r)
                    }
                }
                Operator::Equals | Operator::NotEquals => {
                    let compared = ctx.hir.types.add_unknown();
                    let l = check_expr(ctx, l, scope, compared, return_ty);
                    let r = check_expr(ctx, r, scope, compared, return_ty);
                    let l = ctx.hir.add(l);
                    let r = ctx.hir.add(r);
                    if op == Operator::Equals {
                        Node::Equals(l, r)
                    } else {
                        Node::NotEquals(l, r)
                    }
                }
                Operator::LT | Operator::GT | Operator::LE | Operator::GE => todo!(),
                Operator::Range | Operator::RangeExclusive => todo!("range types not implemented yet"),
            }
        }
        &Expr::FunctionCall(call) => {
            let call = &ast[call];
            let function_ty = ctx.hir.types.add_unknown();
            let _called = check_expr(ctx, call.called_expr, scope, function_ty, return_ty);
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
                        let node = check_expr(ctx, arg, scope, ty, return_ty);
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
            let val = check_expr(ctx, *val, scope, from_ty, return_ty);
            let val = ctx.hir.add(val);
            let new_type_info = ctx.hir.types.info_from_unresolved(
                new_ty,
                ctx.compiler,
                ctx.module,
                scope.static_scope,
            );
            ctx.specify(expected, new_type_info, |_| new_ty.span());
            let cast_id = ctx.hir.add_cast(Cast {
                val,
                cast_ty: CastType::Invalid, // will be filled in in deferred check
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
                let node = check_expr(ctx, value, scope, ty, return_ty);
                ctx.hir.modify_node(node_id, node);
            }
            Node::Tuple { elems, elem_types }
        }
        expr => todo!("typecheck {expr:?}")
    }
}

pub fn check_lval(
    ctx: &mut Ctx,
    expr: ExprId,
    scope: &mut LocalScope,
) -> (LValue, LocalTypeId) {
    match &ctx.ast[expr] {
        &Expr::Ident { span } => {
            match scope.resolve(&ctx.ast.src()[span.range()], span, ctx.compiler) {
                LocalItem::Invalid | LocalItem::Def(Def::Invalid) => (
                    LValue::Invalid,
                    ctx.hir.types.add(TypeInfo::Invalid),
                ),
                LocalItem::Var(id) => {
                    let var_ty = ctx.hir.get_var(id);
                    (LValue::Variable(id), var_ty)
                }
                LocalItem::Def(Def::Global(module, id)) => {
                    let global_ty = &ctx.compiler.get_checked_global(module, id).0;
                    let ty = ctx.hir.types.info_from_resolved(global_ty);
                    let ty = ctx.hir.types.add(ty);
                    (LValue::Global(module, id), ty)
                }
                LocalItem::Def(_) => {
                    ctx.compiler.errors.emit_err(Error::CantAssignTo.at_span(ctx.span(expr)));
                    (
                        LValue::Invalid,
                        ctx.hir.types.add(TypeInfo::Invalid),
                    )
                }
            }
        }
        Expr::UnOp(_, UnOp::Deref, _) => todo!("assign to derefs"),
        Expr::MemberAccess { .. } => todo!("struct member assignment"),
        _ => {
            ctx.compiler.errors.emit_err(Error::CantAssignTo.at_span(ctx.span(expr)));
            (
                LValue::Invalid,
                ctx.hir.types.add(TypeInfo::Invalid),
            )
        }
    }
}

pub fn check_pat(
    ctx: &mut Ctx,
    variables: &mut DHashMap<String, VarId>,
    exhaustion: &mut Exhaustion,
    pat: ExprId,
    expected: LocalTypeId,
) -> Pattern {
    match &ctx.ast[pat] {
        Expr::Ident { span, .. } => {
            let var = ctx.hir.add_var(expected);
            let name = ctx.ast.src()[span.range()].to_owned();
            variables.insert(name, var);
            exhaustion.exhaust_full();
            Pattern::Variable(var)
        }
        Expr::Hole(_) => {
            exhaustion.exhaust_full();
            Pattern::Ignore
        }
        &Expr::BinOp(op @ (Operator::Range | Operator::RangeExclusive), l, r) => {
            enum Kind {
                Int(exhaust::SignedInt),
                Float,
                Invalid,
            }
            let mut range_side = |expr_ref: ExprId| {
                let expr = &ctx.ast[expr_ref];
                match *expr {
                    Expr::IntLiteral(l) => {
                        let lit = IntLiteral::parse(&ctx.ast.src()[l.range()]);
                        ctx.specify(expected, TypeInfo::Integer, |ast| ast[expr_ref].span(ast));
                        Kind::Int(exhaust::SignedInt(lit.val, false))
                    }
                    Expr::FloatLiteral(_) => {
                        ctx.specify(expected, TypeInfo::Float, |ast| ast[expr_ref].span(ast));
                        Kind::Float
                    }
                    Expr::UnOp(_, UnOp::Neg, inner) => match ctx.ast[inner] {
                        Expr::IntLiteral(l) => {
                            let lit = IntLiteral::parse(&ctx.ast.src()[l.range()]);
                            ctx.specify(expected, TypeInfo::Integer, |ast| ast[expr_ref].span(ast));
                            Kind::Int(exhaust::SignedInt(lit.val, true))
                        }
                        Expr::FloatLiteral(_) => {
                            ctx.specify(expected, TypeInfo::Float, |ast| ast[expr_ref].span(ast));
                            Kind::Float
                        }
                        _ => {
                            ctx.compiler.errors.emit_span(Error::NotAPatternRangeValue, ctx.span(expr_ref));
                            ctx.invalidate(expected);
                            Kind::Invalid
                        }
                    }
                    _ => {
                        ctx.compiler.errors.emit_span(Error::NotAPatternRangeValue, ctx.span(expr_ref));
                        ctx.invalidate(expected);
                        Kind::Invalid
                    }
                }
            };
            if let (Kind::Int(l), Kind::Int(r)) = (range_side(l), range_side(r)) {
                exhaustion.exhaust_int_range(l, r);
                let inclusive = op == Operator::Range;
                Pattern::Range { min_max: (l.0, r.0), min_max_signs: (l.1, r.1), inclusive }
            } else {
                ctx.compiler.errors.emit_err(
                    Error::NotAPattern { coming_soon: false }.at_span(ctx.span(pat))
                );
                Pattern::Invalid
            }
        }
        /*
        &Expr::Tuple(span, members) => {
            let member_types = ctx.hir.types.add_multiple_unknown(members.count);
            ctx.specify(expected, TypeInfo::Tuple(member_types, TupleCountMode::Exact), span.in_mod(ctx.scope().module.id));
            let do_exhaust_checks = match exhaustion {
                Exhaustion::Full | Exhaustion::Invalid => true,
                Exhaustion::None => {
                    *exhaustion = Exhaustion::Tuple(vec![Exhaustion::None; members.count as usize]);
                    true
                }
                Exhaustion::Tuple(_) => true,
                _ => {
                    *exhaustion = Exhaustion::Invalid;
                    false
                }
            };
            for (i, (&item_pat, ty)) in ctx.ast[members].iter().zip(member_types.iter()).enumerate() {
                if do_exhaust_checks {
                    let Exhaustion::Tuple(members) = exhaustion else { unreachable!() };
                    pat(item_pat, ty, ctx.reborrow(), &mut members[i]);
                } else {
                    pat(item_pat, ty, ctx.reborrow(), &mut Exhaustion::Full);
                };
            }
        }
        */
        _ => {
            ctx.compiler.errors.emit_err(
                Error::NotAPattern { coming_soon: false }.at_span(ctx.span(pat))
            );
            Pattern::Invalid
        }
    }
}

pub fn function_item(
    ctx: &mut Ctx,
    _module: ModuleId,
    function: FunctionId,
    expected: LocalTypeId,
    expr: ExprId,
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
        |ast| ast[expr].span(ast),
    );
    // TODO: should this stay a unit node?
    Node::Unit
}

pub fn verify_main_signature(
    signature: &Signature,
    main_module: ModuleId,
) -> Result<(), Option<CompileError>> {
    if signature.args.len() != 0 || signature.varargs {
        return Err(Some(Error::MainArgs.at_span(signature.span.in_mod(main_module))));
    }
    if !signature.generics.is_empty() {
        return Err(Some(Error::MainGenerics.at_span(signature.span.in_mod(main_module))));
    }
    match &signature.return_type {
        Type::Invalid => return Err(None),
        Type::Primitive(p) if p.is_int() | matches!(p, Primitive::Unit) => Ok(()),
        ty => return Err(Some(
            Error::InvalidMainReturnType(ty.to_string())
                .at_span(signature.span.in_mod(main_module))
        )),
    }
}
