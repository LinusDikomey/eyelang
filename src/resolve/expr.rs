use crate::{ast::{ExprRef, self, CallId}, error::Error, token::{FloatLiteral, IntLiteral}, types::Primitive, resolve::exhaust::Exhaustion};

use super::{Ctx, type_info::{TypeInfo, TypeInfoOrIndex}, const_val::ConstSymbol, Ident, ResolvedCall, scope::{LocalScope, ExprInfo, LocalDefId}, types::DefId};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum UseHint {
    Should,
    Can,
}

pub enum Res {
    Val { use_hint: UseHint },
    Symbol(ConstSymbol),
    Method,
}
impl Res {
    fn should_use(&self) -> UseHint {
        match self {
            Res::Val { use_hint } => *use_hint,
            Res::Symbol(_) => UseHint::Should,
            Res::Method => UseHint::Should,
        }
    }
}

impl<'a> LocalScope<'a> {
    pub(super) fn val_expr(&mut self, expr: ExprRef, info: ExprInfo, mut ctx: Ctx, unused: bool) {
        match self.expr(expr, info, ctx.reborrow()) {
            Res::Val { use_hint } => if use_hint == UseHint::Should && unused {
                ctx.errors.emit_span(Error::UnusedExpressionValue, self.span(expr, ctx.ast));
            },
            Res::Symbol(_) | Res::Method => ctx.errors.emit_span(Error::ExpectedValue, self.span(expr, ctx.ast)),
        }
    }

    #[must_use]
    pub(super) fn expr(&mut self, expr: ExprRef, mut info: ExprInfo, mut ctx: Ctx) -> Res {
        ctx.symbols.expr_types[expr.idx()] = info.expected;
        let mut use_hint = UseHint::Can;
        match &ctx.ast[expr] {
            ast::Expr::Block { span: _, items, defs } => {
                let mut block_scope = self.child_with_defs(&ctx.ast[*defs], ctx.ast, ctx.symbols, ctx.errors);

                for item in &ctx.ast[*items] {
                    let expected = ctx.types.add_unknown();
                    let res = block_scope.expr(*item, info.with_expected(expected), ctx.reborrow());
                    if res.should_use() == UseHint::Should {
                        ctx.errors.emit_span(Error::UnusedExpressionValue, self.span(*item, ctx.ast));
                    }
                }
            }
            ast::Expr::Declare { pat, annotated_ty } => {
                let ty = self.resolve_type_info(annotated_ty, &ctx.symbols, ctx.types, ctx.errors);
                let ty = ctx.types.add_info_or_idx(ty);

                let mut exhaustion = Exhaustion::None;
                self.pat(*pat, ty, ctx.reborrow(), &mut exhaustion);
                if !matches!(exhaustion.is_exhausted(None, &ctx.symbols), Some(true)) {
                    ctx.errors.emit_span(Error::Inexhaustive, self.span(*pat, ctx.ast));
                }
            }
            ast::Expr::DeclareWithVal { pat, annotated_ty, val } => {
                let ty = self.resolve_type_info(annotated_ty, &ctx.symbols, ctx.types, ctx.errors);
                let ty = ctx.types.add_info_or_idx(ty);

                self.val_expr(*val, info.with_expected(ty), ctx.reborrow(), false);
                
                let mut exhaustion = Exhaustion::None;
                self.pat(*pat, ty, ctx.reborrow(), &mut exhaustion);
                if !matches!(exhaustion.is_exhausted(None, &ctx.symbols), Some(true)) {
                    ctx.errors.emit_span(Error::Inexhaustive, self.span(*pat, ctx.ast));
                }
            }
            ast::Expr::Return { val, .. } => {
                self.val_expr(*val, info.with_expected(info.ret), ctx, false);
            }
            ast::Expr::ReturnUnit { .. } => {
                ctx.specify(info.expected, TypeInfo::Primitive(Primitive::Unit), self.span(expr, ctx.ast));
            }
            ast::Expr::IntLiteral(span) => {
                let lit = IntLiteral::parse(&self.scope.module.src()[span.range()]);
                let ty = lit.ty.map_or(TypeInfo::Int, |ty| TypeInfo::Primitive(ty.into()));
                ctx.specify(info.expected, ty, span.in_mod(self.scope.module.id));
                use_hint = UseHint::Should;
            }
            ast::Expr::FloatLiteral(span) => {
                let lit = FloatLiteral::parse(&self.scope.module.src()[span.range()]);
                let ty = lit.ty.map_or(TypeInfo::Float, |ty| TypeInfo::Primitive(ty.into()));
                ctx.specify(info.expected, ty, span.in_mod(self.scope.module.id));
                use_hint = UseHint::Should;
            }
            ast::Expr::StringLiteral(_span) => {
                use_hint = UseHint::Should;
            }
            ast::Expr::BoolLiteral { .. } => {
                ctx.specify(info.expected, TypeInfo::Primitive(Primitive::Bool), self.span(expr, ctx.ast));
                use_hint = UseHint::Should;
            }
            ast::Expr::EnumLiteral { ident, .. } => {
                let name = &self.scope.module.src()[ident.range()];
                ctx.specify_enum_variant(info.expected, name, ident.in_mod(self.scope.module.id))
            }
            ast::Expr::Record { .. } => todo!(),
            ast::Expr::Nested(_, _) => todo!(),
            ast::Expr::Unit(_) => {
                ctx.specify(info.expected, TypeInfo::UNIT, self.span(expr, ctx.ast));
            }
            ast::Expr::Variable { span, id } => {
                let resolved = self.resolve_local(&self.scope.module.src()[span.range()], *span, ctx.errors);
                let ident = match resolved {
                    LocalDefId::Def(DefId::Invalid) => Ident::Invalid,
                    LocalDefId::Def(def) => return Res::Symbol(def.into()),
                    LocalDefId::Var(var) => {
                        let ty = ctx.var(var).ty;
                        ctx.merge(info.expected, ty, span.in_mod(self.scope.module.id));
                        Ident::Var(var)
                    }
                    LocalDefId::Type(_) => todo!(),
                };
                ctx.set_ident(*id, ident);
            }
            ast::Expr::Hole(_) => {}
            ast::Expr::Array(_, _) => todo!(),
            ast::Expr::Tuple(_, _) => todo!(),
            ast::Expr::If { start, cond, then } => todo!(),
            ast::Expr::IfElse { start, cond, then, else_ } => todo!(),
            ast::Expr::Match { start, end, val, extra_branches, branch_count } => todo!(),
            ast::Expr::While { start, cond, body } => todo!(),
            ast::Expr::FunctionCall(call) => {
                return self.call(*call, expr, info, ctx);
            }
            ast::Expr::UnOp(_, _, _) => todo!(),
            ast::Expr::BinOp(_, _, _) => todo!(),
            ast::Expr::MemberAccess { left, name } => todo!(),
            ast::Expr::Index { expr, idx, end } => todo!(),
            ast::Expr::TupleIdx { expr, idx, end } => todo!(),
            ast::Expr::Cast(_, _, _) => todo!(),
            ast::Expr::Root(_) => todo!(),
            ast::Expr::Asm { span, asm_str_span, args } => todo!(),
        };
        Res::Val { use_hint }
    }

    fn call(&mut self, id: CallId, call_expr: ExprRef, mut info: ExprInfo, mut ctx: Ctx) -> Res {
        let call = &ctx.ast[id];
        let called_ty = ctx.types.add_unknown();

        let (res, call) = match self.expr(call.called_expr, info.with_expected(called_ty), ctx.reborrow()) {
            Res::Symbol(ConstSymbol::Func(func_id)) => {
                let signature = ctx.symbols.get_func(func_id);
                
                let generics = ctx.types.add_multiple_unknown(signature.generic_count() as _);
                let on_generic = |i| TypeInfoOrIndex::Idx(generics.nth(i as usize));

                match signature.params.len().cmp(&(call.args.count as usize)) {
                    std::cmp::Ordering::Less if signature.varargs => {}
                    std::cmp::Ordering::Equal => {}
                    _ => {
                        ctx.errors.emit_span(Error::InvalidArgCount {
                            expected: signature.params.len() as _,
                            varargs: signature.varargs,
                            found: call.args.count,
                        }, self.span(call_expr, &ctx.ast));
                    }
                }

                let ret = signature.return_type.as_info(ctx.types, on_generic);
                
                let call_span = self.span(call_expr, ctx.ast);
                ctx.types.specify_or_merge(info.expected, ret, ctx.errors, call_span, &ctx.symbols);
                
                let params = signature.params
                    .iter()
                    .map(|(_, ty)| {
                        let ty = ty.as_info(ctx.types, on_generic);
                        ctx.types.add_info_or_idx(ty)
                    })
                    .collect::<Vec<_>>();

                let mut params = params.into_iter();

                for arg in &ctx.ast[call.args] {
                    let param_ty = params.next().unwrap_or_else(|| ctx.types.add_unknown());
                    self.val_expr(*arg, info.with_expected(param_ty), ctx.reborrow(), false);
                }

                (Res::Val { use_hint: UseHint::Can }, ResolvedCall::Function { func_id, generics })
            }
            Res::Symbol(ConstSymbol::Type(_)) => todo!(),
            Res::Method => todo!(),
            _ => {
                if !ctx.types.invalidate(called_ty) {
                    ctx.errors.emit_span(
                        Error::FunctionOrStructTypeExpected,
                        ctx.ast[call.called_expr].span_in(&ctx.ast, self.scope.module.id)
                    );
                }
                (Res::Val { use_hint: UseHint::Can }, ResolvedCall::Invalid)
            }
        };
        ctx.symbols.place_call(id, call);
        res
    }
}

