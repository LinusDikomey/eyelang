mod exhaust;

use dmap::DHashMap;
use id::ModuleId;
use span::TSpan;
use types::Primitive;

use crate::{
    Compiler,
    parser::{ast::{Ast, ExprId, Expr, UnOp}, token::{IntLiteral, Operator}},
    compiler::{LocalScope, LocalItem, Def, VarId},
    type_table::{TypeInfo, LocalTypeId},
    eval::ConstValue,
    hir::{HIRBuilder, Node, Pattern}, error::Error,
};

use self::exhaust::Exhaustion;

pub struct Ctx<'a> {
    pub compiler: &'a mut Compiler,
    pub ast: &'a Ast,
    pub module: ModuleId,
    pub hir: HIRBuilder,
    pub deferred_exhaustions: Vec<(Exhaustion, LocalTypeId, ExprId)>,
}
impl<'a> Ctx<'a> {
    fn span(&self, expr: ExprId) -> span::Span {
        self.ast[expr].span_in(self.ast, self.module)
    }

    fn specify(&mut self, ty: LocalTypeId, info: TypeInfo, span: impl FnOnce(&Ast) -> TSpan) {
        self.hir.types.specify(ty, info, &mut self.compiler.errors, || span(self.ast).in_mod(self.module))
    }

    fn unify(&mut self, a: LocalTypeId, b: LocalTypeId, span: impl FnOnce() -> TSpan) {
        self.hir.types.unify(a, b, &mut self.compiler.errors, || span().in_mod(self.module))
    }

    fn invalidate(&mut self, ty: LocalTypeId) {
        self.hir.types.invalidate(ty);
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
        &Expr::Variable { span, id: _ } => {
            let name = &ast[span];
            match scope.resolve(name, span, ctx.compiler) {
                LocalItem::Var(var) => {
                    let ty = ctx.hir.get_var(var);
                    ctx.unify(expected, ty, || span);
                    Node::Variable(var)
                }
                LocalItem::Def(def) => match def {
                    Def::Function(_, _) => todo!("function items"),
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
                        ctx.compiler.emit_error(
                            Error::ExpectedValue.at_span(span.in_mod(ctx.module)),
                        );
                        ctx.invalidate(expected);
                        Node::Invalid
                    }
                    Def::Global(_, _) => todo!("globals"),
                    Def::Invalid => {
                        ctx.specify(expected, TypeInfo::Invalid, |_| span);
                        Node::Invalid
                    }
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
        Expr::Function { id: _ } => todo!("function items (+ closures)"),
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
        expr => todo!("typecheck {expr:?}")
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
        Expr::Variable { span, .. } => {
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
                ctx.compiler.emit_error(
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
            ctx.compiler.emit_error(
                Error::NotAPattern { coming_soon: false }.at_span(ctx.span(pat))
            );
            Pattern::Invalid
        }
    }
}
