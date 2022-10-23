use crate::{
    ir::{
        exhaust::Exhaustion,
        Ref,
        SymbolKey,
        TypeTableIndex,
        TypeInfo,
        TypeTableIndices,
        RefVal,
        TypeDef,
        BlockIndex, builder::BinOp, FunctionHeader, TupleCountMode, TypeInfoOrIndex, Type,
    },
    error::Error,
    span::TSpan,
    ast::{Expr, ExprRef, UnOp, ExprExtra, ModuleId},
    token::{IntLiteral, Operator, FloatLiteral, AssignType},
    dmap,
    types::Primitive, irgen::{string_literal, gen_string, const_eval}
};
use super::{ConstSymbol, IrBuilder, pat, Scope, GenCtx, int_literal, Symbol, ExprResult};

pub struct ExprInfo<'a> {
    pub expected: TypeTableIndex,
    pub ret: TypeTableIndex,
    pub noreturn: &'a mut bool,
}
impl<'a> ExprInfo<'a> {
    pub fn mark_noreturn(&mut self) {
        *self.noreturn = true;
    }
    pub fn with_expected(&mut self, expected: TypeTableIndex) -> ExprInfo {
        ExprInfo { expected, ret: self.ret, noreturn: self.noreturn }
    }
    pub fn with_noreturn<'b>(&self, noreturn: &'b mut bool) -> ExprInfo<'b> {
        ExprInfo { expected: self.expected, ret: self.ret, noreturn }
    }
    pub fn reborrow(&mut self) -> ExprInfo<'_> {
        ExprInfo { expected: self.expected, ret: self.ret, noreturn: &mut *self.noreturn }
    }


}

pub fn val_expr(
    scope: &mut Scope,
    ctx: &mut GenCtx,
    ir: &mut IrBuilder,
    expr: ExprRef,
    mut info: ExprInfo,
) -> Ref {
    reduce_expr(scope, ctx, ir, &ctx.ast[expr], info.reborrow())
        .get_or_load(ir, &ctx.ctx, info.expected, &mut ctx.errors, ctx.ast[expr].span(ctx.ast).in_mod(ctx.module))
}

fn reduce_expr(
    scope: &mut Scope,
    ctx: &mut GenCtx,
    ir: &mut IrBuilder,
    expr: &Expr,
    mut info: ExprInfo,
) -> ExprResult {
    let expected = info.expected;
    reduce_expr_any(
        scope, ctx, ir, expr, info.reborrow(),
        |ir| ir.build_decl(expected), // declare new var
    ).0
}

fn reduce_unused_expr(
    scope: &mut Scope,
    ctx: &mut GenCtx,
    ir: &mut IrBuilder,
    expr: &Expr,
    mut info: ExprInfo,
) {
    let expected = info.expected;
    if reduce_expr_any(
        scope, ctx, ir, expr, info.reborrow(),
        |ir| ir.build_decl(expected), // declare new var
    ).1 {
        ctx.errors.emit_span(Error::UnusedStatementValue, expr.span(ctx.ast).in_mod(ctx.module));
    }
}

fn reduce_expr_store_into_var(
    scope: &mut Scope,
    ctx: &mut GenCtx,
    ir: &mut IrBuilder,
    expr: &Expr,
    var: Ref,
    mut info: ExprInfo,
) {
    let val = match reduce_expr_any(scope, ctx, ir, expr, info.reborrow(), |_| var).0 {
        ExprResult::Stored(_) => return,
        ExprResult::VarRef(other_var) => ir.build_load(other_var, info.expected),
        ExprResult::Val(val) => val,
        ExprResult::Symbol(symbol) => {
            // TODO: this should only happen in compile time code
            let span = ctx.span(expr);
            symbol.add_instruction(ir, &ctx.ctx, info.expected, &mut ctx.errors, span)
        }
        _ => {
            ctx.errors.emit_span(Error::ExpectedValueFoundDefinition, expr.span(ctx.ast).in_mod(ctx.module));
            Ref::UNDEF
        }
    };
    ir.build_store(var, val);
}

fn reduce_lval_expr(
    scope: &mut Scope,
    ctx: &mut GenCtx,
    ir: &mut IrBuilder,
    expr: &Expr,
    mut info: ExprInfo,
    error: Error,
) -> Ref {
    let expected = info.expected;
    match reduce_expr_any(
        scope, ctx, ir, expr, info.reborrow(),
        |ir| ir.build_decl(expected)
    ).0 {
        ExprResult::VarRef(var) | ExprResult::Stored(var) => var,
        ExprResult::Val(_) | ExprResult::Method(_, _) | ExprResult::Symbol(_) => {
            if !ir.types.get_type(info.expected).is_invalid() {
                ctx.errors.emit_span(error, expr.span(ctx.ast).in_mod(ctx.module));
            }
            Ref::UNDEF
        }
    }
}

fn reduce_expr_any(
    scope: &mut Scope,
    ctx: &mut GenCtx,
    ir: &mut IrBuilder,
    expr: &Expr,
    mut info: ExprInfo,
    get_var: impl Fn(&mut IrBuilder) -> Ref,
) -> (ExprResult, bool) {
    crate::log!("reducing expr {expr:?}");
    let (r, should_use) = match expr {
        Expr::Block { span, items, defs } => {
            let defs = &ctx.ast[*defs];
            let mut block_symbols = dmap::new();
            let mut block_scope = scope.child(&mut block_symbols, defs);
            //types2::gen_locals(&mut block_scope, errors);
            
            super::generate_bodies(&mut block_scope, defs, ctx);
            let prev_emit = ir.emit;
            let mut block_noreturn = false;
            for item in &ctx.ast[*items] {
                let item_ty = ir.types.add(TypeInfo::Unknown);
                reduce_unused_expr(&mut block_scope, ctx, ir, &ctx.ast[*item],
                    info.with_expected(item_ty).with_noreturn(&mut block_noreturn));
                ir.emit = prev_emit && !block_noreturn;
            }
            ir.emit = prev_emit;
            *info.noreturn |= block_noreturn;
            if !block_noreturn {
                ir.specify(info.expected, TypeInfo::UNIT, &mut ctx.errors, *span, &ctx.ctx);
            }
            (Ref::UNIT, items.count == 0)
        }
        Expr::Declare { name, end: _, annotated_ty } => {
            let expr_span = ctx.span(expr);
            ir.types.specify(info.expected, TypeInfo::UNIT, &mut ctx.errors, expr_span, &ctx.ctx);
            let ty = match scope.resolve_type(annotated_ty, &mut ir.types, ctx) {
                Ok(t) => t,
                Err(err) => {
                    ctx.errors.emit_span(err, annotated_ty.span().in_mod(ctx.module));
                    TypeInfo::Invalid
                }
            };
            let ty = ir.types.add(ty);

            scope.declare_var(ir, ctx.src(*name).to_owned(), ty);

            (Ref::UNIT, false)
        }
        Expr::DeclareWithVal { name, annotated_ty, val } => {
            let ty = match scope.resolve_type(annotated_ty, &mut ir.types, ctx) {
                Ok(t) => t,
                Err(err) => {
                    ctx.errors.emit_span(err, annotated_ty.span().in_mod(ctx.module));
                    TypeInfo::Invalid
                }
            };
            let ty = ir.types.add(ty);

            let var = scope.declare_var(ir, ctx.src(*name).to_owned(), ty);

            reduce_expr_store_into_var(scope, ctx, ir, &ctx.ast[*val], var, info.with_expected(ty));
            (Ref::UNIT, false)
        }
        Expr::Return { start: _, val } => {
            info.mark_noreturn();
            let r = val_expr(scope, ctx, ir, *val, info.with_expected(info.ret));
            ir.specify(info.expected, TypeInfo::Primitive(Primitive::Never), &mut ctx.errors,
                ctx.ast[*val].span(ctx.ast), &ctx.ctx);
            ir.build_ret(r);
            (Ref::UNDEF, false)
        }
        Expr::IntLiteral(span) => {
            let s = ctx.src(*span);
            (int_literal(IntLiteral::parse(s), *span, ir, info.expected, ctx), true)
        }
        Expr::FloatLiteral(span) => {
            let lit = FloatLiteral::parse(ctx.src(*span));
            let float_ty = lit.ty.map_or(TypeInfo::Float, |float_ty| {
                TypeInfo::Primitive(float_ty.into())
            });
            ir.specify(info.expected, float_ty, &mut ctx.errors, *span, &ctx.ctx);
            (ir.build_float(lit.val, info.expected), true)
        }
        Expr::StringLiteral(span) => {
            let lit = string_literal(*span, ctx.ast.src(ctx.module).0);
            (gen_string(&lit, ir, info.expected, *span, &mut ctx.errors, &ctx.ctx), true)
        }
        Expr::BoolLiteral { val, start } => {
            let span = TSpan::new(*start, start + if *val {4} else {5});
            ir.specify(info.expected, TypeInfo::Primitive(Primitive::Bool), &mut ctx.errors, span, &ctx.ctx);
            (Ref::val(if *val { RefVal::True } else { RefVal::False }), true)
        }
        Expr::EnumLiteral { dot: _, ident } => {
            let name = &ctx.ast.src(ctx.module).0[ident.range()];
            ir.specify_enum_variant(info.expected, name, *ident, &ctx.ctx, &mut ctx.errors);
            let variant_name = ctx.src(*ident);
            (ir.build_enum_lit(variant_name, info.expected), true)
        }
        Expr::Nested(_, inner) => {
            return reduce_expr_any(scope, ctx, ir, &ctx.ast[*inner], info, get_var);
        }
        Expr::Unit(span) => {
            ir.specify(info.expected, TypeInfo::Primitive(Primitive::Unit), &mut ctx.errors, *span, &ctx.ctx);
            (Ref::UNIT, true)
        }
        Expr::Variable(span) => {
            let name = &ctx.ast.sources[ctx.module.idx()].0[span.range()];
            if let Some(resolved) = scope.resolve(name, ctx) {
                return (match resolved {
                    Symbol::Var { ty, var } => {
                        ir.types.merge(ty, info.expected, &mut ctx.errors, span.in_mod(ctx.module), &ctx.ctx);
                        ExprResult::VarRef(var)
                    }
                    Symbol::GlobalVar(key) => {
                        let (ty, _) = ctx.ctx.get_global(key);
                        let ty_info = ty.as_info(&mut ir.types);
                        ir.specify(info.expected, ty_info, &mut ctx.errors, expr.span(ctx.ast), &ctx.ctx);
                        let ptr = ir.types.add(TypeInfo::Pointer(info.expected));
                        ExprResult::VarRef(ir.build_global(key, ptr))
                    }
                    Symbol::Func(f) => ExprResult::Symbol(ConstSymbol::Func(f)),
                    Symbol::GenericFunc(idx) => ExprResult::Symbol(ConstSymbol::GenericFunc(idx)),
                    Symbol::Type(t) => ExprResult::Symbol(ConstSymbol::Type(t)),
                    Symbol::Trait(t) => ExprResult::Symbol(ConstSymbol::Trait(t)),
                    Symbol::LocalType(t) => ExprResult::Symbol(ConstSymbol::LocalType(t)),
                    Symbol::Module(m) => ExprResult::Symbol(ConstSymbol::Module(m)),
                    Symbol::Const(c) => {
                        let const_val = Scope::get_or_gen_const(ctx, c, *span);
                        let const_ty = const_val.type_info(&mut ir.types);
                        ir.specify(info.expected, const_ty, &mut ctx.errors, *span, &ctx.ctx);
                        let val = ctx.ctx.get_const(c);
                        const_eval::to_expr_result(val, ir, info)
                    }
                    Symbol::Generic(_) => todo!(),
                    Symbol::Invalid => {
                        ir.invalidate(info.expected);
                        ExprResult::Val(Ref::UNDEF)
                    }
                }, true)
            } else {
                ctx.errors.emit_span(Error::UnknownIdent, span.in_mod(ctx.module));
                ir.invalidate(info.expected);
                (Ref::UNDEF, true)
            }
        }
        Expr::Array(span, elems) => {
            let elems = &ctx.ast[*elems];
            let elem_ty = ir.types.add(TypeInfo::Unknown);
            let elem_ty_ptr = ir.types.add(TypeInfo::Pointer(elem_ty));
            let arr_ty = TypeInfo::Array(Some(elems.len() as u32), elem_ty);
            ir.types.specify(info.expected, arr_ty, &mut ctx.errors, span.in_mod(ctx.module), &ctx.ctx);
            let arr = get_var(ir);
            for (i, elem) in elems.iter().enumerate() {
                let elem_val = val_expr(scope, ctx, ir, *elem, info.with_expected(elem_ty));
                let elem_ptr = ir.build_member_int(arr, i as u32, elem_ty_ptr);
                ir.build_store(elem_ptr, elem_val);
            }
            return (ExprResult::Stored(arr), true)
        }
        Expr::Tuple(span, elems) => {
            let elems = &ctx.ast[*elems];
            let var = get_var(ir);
            let types = ir.types.add_multiple_unknown(elems.len() as _);
            ir.types.specify(
                info.expected,
                TypeInfo::Tuple(types, TupleCountMode::Exact),
                &mut ctx.errors, span.in_mod(ctx.module), &ctx.ctx
            );
            for (i, elem) in elems.iter().enumerate() {
                let member_ty = types.iter().nth(i).unwrap();
                let member_ty_ptr = ir.types.add(TypeInfo::Pointer(member_ty));
                let member_val = val_expr(scope, ctx, ir, *elem, info.with_expected(member_ty));
                let member = ir.build_member_int(var, i as u32, member_ty_ptr);
                ir.build_store(member, member_val);
            }
            return (ExprResult::Stored(var), true);
        }
        Expr::If { start: _, cond, then } => {
            let after_block = gen_if_then(scope, ctx, ir, *cond, info.ret, info.noreturn);

            ir.specify(info.expected, TypeInfo::Primitive(Primitive::Unit), &mut ctx.errors, expr.span(ctx.ast), &ctx.ctx);
            let then_ty = ir.types.add(TypeInfo::Unknown);
            let mut then_noreturn = false;
            reduce_expr(scope, ctx, ir, &ctx.ast[*then],
                ExprInfo { expected: then_ty, noreturn: &mut then_noreturn, ret: info.ret});
            if !then_noreturn {
                ir.build_goto(after_block);
            } else if !ir.currently_terminated() {
                ir.build_ret_undef();
            }
            ir.begin_block(after_block);
            (Ref::UNIT, false)
        }
        Expr::IfElse { start: _, cond, then, else_ } => {
            let else_block = gen_if_then(scope, ctx, ir, *cond, info.ret, info.noreturn);
            let mut then_noreturn = false;
            let then_val = val_expr(scope, ctx, ir, *then, info.with_noreturn(&mut then_noreturn));
            let then_exit = ir.current_block();
            let after_block = if !then_noreturn {
                let after_block = ir.create_block();
                ir.build_goto(after_block);
                Some(after_block)
            } else {
                if !ir.currently_terminated() {
                    ir.build_ret_undef();
                }
                None
            };
            ir.begin_block(else_block);
            let mut else_noreturn = false;
            let else_val = val_expr(scope, ctx, ir, *else_, info.with_noreturn(&mut else_noreturn));
            let else_exit = ir.current_block();
            (if then_noreturn && else_noreturn {
                *info.noreturn = true;
                Ref::UNDEF
            } else {
                let after_block = after_block.unwrap_or_else(|| ir.create_block());
                if else_noreturn {
                    if !ir.currently_terminated() {
                        ir.build_ret_undef();
                    }
                } else {
                    ir.build_goto(after_block);
                }
                ir.begin_block(after_block);
                if then_noreturn {
                    else_val
                } else if else_noreturn {
                    then_val
                } else {
                    ir.build_phi([(then_exit, then_val), (else_exit, else_val)], info.expected)
                }
            }, false)
        }
        Expr::Match { start: _, end: _, val, extra_branches, branch_count } => {
            // TODO: match is not checked for exhaustiveness right now

            let val_ty = ir.types.add_unknown();
            let val_span = expr.span(ctx.ast);
            let val = val_expr(scope, ctx, ir, *val, info.with_expected(val_ty));
            let extra = &ctx.ast[ExprExtra { idx: *extra_branches, count: *branch_count * 2 }];

            let else_block = ir.create_block();
            let after_block = ir.create_block();


            let mut all_branches_noreturn = true;
            
            let mut branches = Vec::new();
            let mut exhaustion = Exhaustion::None;

            for (i, [pat, branch]) in extra.array_chunks().enumerate() {
                let mut branch_block_symbols = dmap::new();
                let branch_block_defs = dmap::new();
                let mut branch_block = scope.child(&mut branch_block_symbols, &branch_block_defs);
                let on_match = ir.create_block();
                let otherwise = if i as u32 == *branch_count - 1 {
                    else_block
                } else {
                    ir.create_block()
                };
                let bool_ty = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
                let matches = pat::reduce_pat(&mut branch_block, ctx, ir, val, *pat, val_ty, bool_ty, &mut exhaustion);   
                ir.build_branch(matches, on_match, otherwise);
                ir.begin_block(on_match);
                let mut branch_noreturn = false;
                let val = val_expr(&mut branch_block, ctx, ir, *branch, info.with_noreturn(&mut branch_noreturn));

                if branch_noreturn {
                    ir.build_ret_undef();
                } else {
                    branches.push((on_match, val));
                    ir.build_goto(after_block);
                }
                ir.begin_block(otherwise);

                all_branches_noreturn |= branch_noreturn;
            }

            ir.add_exhaustion_check(exhaustion, val_ty, val_span);

            if extra.is_empty() {
                ir.build_goto(else_block);
                ir.begin_block(else_block);
            }
            // we are now in else_block
            let uninit = ir.build_uninit(info.expected);
            branches.push((else_block, uninit));
            ir.build_goto(after_block);
            ir.begin_block(after_block);

            _ = all_branches_noreturn;
            // TODO: exhaustive match, will also make this sensible to enable
            // if all_branches_noreturn {
            //     info.mark_noreturn();
            // }
            (ir.build_phi(branches, info.expected), false)
        }
        Expr::While { start: _, cond, body } => {
            ir.specify(info.expected, TypeInfo::Primitive(Primitive::Unit), &mut ctx.errors, expr.span(ctx.ast), &ctx.ctx);

            let cond_block = ir.create_block();
            let body_block = ir.create_block();
            let after_block = ir.create_block();

            ir.build_goto(cond_block);
            ir.begin_block(cond_block);
            
            let b = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
            let cond = val_expr(scope, ctx, ir, *cond, info.with_expected(b));

            ir.build_branch(cond, body_block, after_block);
            ir.begin_block(body_block);
            let body_ty = ir.types.add(TypeInfo::Unknown);
            let mut body_noreturn = false;
            val_expr(scope, ctx, ir, *body,
                ExprInfo { expected: body_ty, ret: info.ret, noreturn: &mut body_noreturn });
            if !body_noreturn {
                ir.build_goto(cond_block);
            } else if !ir.currently_terminated() {
                ir.build_ret_undef();
            }
            ir.begin_block(after_block);
            (Ref::UNIT, false)
        }
        &Expr::FunctionCall { func, args, end: _ } => return call(func, args, expr, ctx, ir, scope, info, get_var),
        Expr::UnOp(_, un_op, val) => {
            enum UnOpTag { Neg, Not }
            let span = expr.span(ctx.ast);
            let (inner_expected, tag) = match un_op {
                UnOp::Neg => (info.expected, UnOpTag::Neg),
                UnOp::Not => (ir.types.add(TypeInfo::Primitive(Primitive::Bool)), UnOpTag::Not),
                UnOp::Ref => {
                    let ptr_ty = TypeInfo::Pointer(ir.types.add(TypeInfo::Unknown));
                    ir.types.specify(info.expected, ptr_ty, &mut ctx.errors, span.in_mod(ctx.module), &ctx.ctx);
                    let inner_expected = match ir.types.get_type(info.expected) {
                        TypeInfo::Pointer(inner) => inner,
                        _ => ir.types.add(TypeInfo::Invalid)
                    };
                    return (ExprResult::Val(match 
                        reduce_expr(scope, ctx, ir, &ctx.ast[*val], info.with_expected(inner_expected))
                    {
                        ExprResult::VarRef(r) | ExprResult::Stored(r) => {
                            ir.types.specify(info.expected, TypeInfo::Pointer(inner_expected),
                                &mut ctx.errors, span.in_mod(ctx.module), &ctx.ctx);
                            r
                        }
                        ExprResult::Val(val) => {
                            let val_expected = match ir.types.get_type(info.expected) {
                                TypeInfo::Pointer(inner) => inner,
                                _ => ir.types.add(TypeInfo::Invalid)
                            };
                            let var = ir.build_decl(val_expected);
                            ir.build_store(var, val);
                            var
                        }
                        _ => {
                            ctx.errors.emit_span(Error::CantTakeRef, expr.span(ctx.ast).in_mod(ctx.module));
                            Ref::UNDEF
                        }
                    }), true)
                }
                UnOp::Deref => {
                    let expected = ir.types.add(TypeInfo::Pointer(info.expected));
                    let pointer_val = val_expr(scope, ctx, ir, *val, info.with_expected(expected));
                    return (ExprResult::VarRef(pointer_val), true); // just use the pointer value as variable
                }
            };
            let inner = val_expr(scope, ctx, ir, *val, info.with_expected(inner_expected));
            let res = match un_op {
                UnOp::Neg => match ir.types.get_type(inner_expected) {
                    TypeInfo::Float | TypeInfo::Int | TypeInfo::Unknown => Ok(()),
                    TypeInfo::Primitive(p) => {
                        if let Some(int) = p.as_int() {
                            if int.is_signed() {
                                Ok(())
                            } else {
                                Err(Error::CantNegateType)
                            }
                        } else if p.as_float().is_some() {
                            Ok(())
                        } else {
                            Err(Error::CantNegateType)
                        }
                    }
                    _ => Err(Error::CantNegateType),
                }
                UnOp::Not => Ok(()), // type was already constrained before
                UnOp::Ref | UnOp::Deref => unreachable!(),
            };
            if let Err(err) = res {
                ctx.errors.emit_span(err, ctx.span(expr));
            }
            (match tag {
                UnOpTag::Neg => ir.build_neg(inner, inner_expected),
                UnOpTag::Not => ir.build_not(inner, inner_expected),
            }, true)
        }
        Expr::BinOp(op, l, r) => {
            if let Operator::Assignment(assignment) = op {
                ir.specify(info.expected, TypeInfo::UNIT, &mut ctx.errors, expr.span(ctx.ast), &ctx.ctx);
                let var_ty = ir.types.add_unknown();
                let lval = reduce_lval_expr(scope, ctx, ir, &ctx.ast[*l], info.with_expected(var_ty),
                    Error::CantAssignTo);
                let r = val_expr(scope, ctx, ir, *r, info.with_expected(var_ty));

                let val = if *assignment == AssignType::Assign {
                    r
                } else {
                    let left_val = ir.build_load(lval, var_ty);
                    let op = match assignment {
                        AssignType::Assign => unreachable!(),
                        AssignType::AddAssign => BinOp::Add,
                        AssignType::SubAssign => BinOp::Sub,
                        AssignType::MulAssign => BinOp::Mul,
                        AssignType::DivAssign => BinOp::Div,
                        AssignType::ModAssign => BinOp::Mod,
                    };
                    ir.build_bin_op(op, left_val, r, var_ty)
                };
                ir.build_store(lval, val);
                (Ref::UNDEF, false)
            } else {
                // binary operations always require the same type on both sides right now
                let inner_ty = if op.is_boolean() {
                    ir.types.add(TypeInfo::Primitive(Primitive::Bool))
                } else if op.is_logical() {
                    ir.types.add(TypeInfo::Unknown)
                } else {
                    info.expected
                };
                let l = val_expr(scope, ctx, ir, *l, info.with_expected(inner_ty));
                let r = val_expr(scope, ctx, ir, *r, info.with_expected(inner_ty));
                let op = match op {
                    Operator::Add => BinOp::Add,
                    Operator::Sub => BinOp::Sub,
                    Operator::Mul => BinOp::Mul,
                    Operator::Div => BinOp::Div,
                    Operator::Mod => BinOp::Mod,

                    Operator::Or => BinOp::Or,
                    Operator::And => BinOp::And,

                    Operator::Equals => BinOp::Eq,
                    Operator::NotEquals => BinOp::NE,

                    Operator::LT => BinOp::LT,
                    Operator::GT => BinOp::GT,
                    Operator::LE => BinOp::LE,
                    Operator::GE => BinOp::GE,
                    
                    Operator::Range | Operator::RangeExclusive => {
                        todo!("range expressions")
                    }

                    Operator::Assignment(_) => unreachable!()
                };
                (ir.build_bin_op(op, l, r, info.expected), true)
            }
        }
        Expr::MemberAccess { left, name: name_span } => {
            let member = &ctx.ast.src(ctx.module).0[name_span.range()];
            let left_ty = ir.types.add(TypeInfo::Unknown);
            enum MemberAccessType {
                Val { val: Ref, is_ptr: bool },
                Module(ModuleId),
                Associated(SymbolKey),
                TraitFunction(SymbolKey),
                Invalid
            }
            let left = &ctx.ast[*left];
            let left_val = match reduce_expr(scope, ctx, ir, left, info.with_expected(left_ty)) {
                ExprResult::VarRef(val) | ExprResult::Stored(val) => MemberAccessType::Val { val, is_ptr: true },
                ExprResult::Val(val) => MemberAccessType::Val { val, is_ptr: false },
                ExprResult::Symbol(ConstSymbol::Type(ty)) => MemberAccessType::Associated(ty),
                ExprResult::Symbol(ConstSymbol::Trait(t)) => MemberAccessType::TraitFunction(t),
                ExprResult::Symbol(ConstSymbol::Module(id)) => MemberAccessType::Module(id),
                ExprResult::Symbol(_) | ExprResult::Method(_, _) => {
                    ctx.errors.emit_span(Error::NonexistantMember, name_span.in_mod(ctx.module));
                    MemberAccessType::Invalid
                }
            };

            (match left_val {
                MemberAccessType::Val { val, is_ptr } => {
                    let (ty, idx) = match ir.types.get_type(left_ty) {
                        TypeInfo::Pointer(_) => todo!("auto deref"),
                        TypeInfo::Resolved(key, generics) => {
                            match &ctx.ctx.types[key.idx()].1 {
                                TypeDef::Struct(struct_) => {
                                    if let Some(func_id) = struct_.functions.get(member) {
                                        let func = ctx.ctx.get_func(*func_id);
                                        let header = func.header();
                                        let var = if let Some(first_arg) = header.params.first() {
                                            let this_ty = &first_arg.1;
                                            // TODO: this is a very primitive auto deref and can probably be made
                                            // more flexible
                                            let (val, this_info) = match this_ty {
                                                Type::Pointer(inner) => {

                                                    let val = if is_ptr {
                                                        val
                                                    } else {
                                                        let var = ir.build_decl(left_ty);
                                                        ir.build_store(var, val);
                                                        var
                                                    };
                                                    (val, inner.as_info(&mut ir.types))
                                                }
                                                _ => {
                                                    let val = if is_ptr {
                                                        ir.build_load(val, left_ty)
                                                    } else {
                                                        val
                                                    };
                                                    (val, this_ty.as_info(&mut ir.types))
                                                }
                                            };
                                            ir.specify(left_ty, this_info, &mut ctx.errors, left.span(ctx.ast), &ctx.ctx);
                                            val
                                        } else {
                                            ctx.errors.emit_span(
                                                Error::NotAnInstanceMethod,
                                                name_span.in_mod(ctx.module)
                                            );
                                            ir.invalidate(info.expected);
                                            Ref::UNDEF
                                        };
                                        return (ExprResult::Method(var, *func_id), true);
                                    } else if let Some((i, (_, ty))) = struct_
                                        .members
                                        .iter()
                                        .enumerate()
                                        .find(|(_, (name, _))| name == member)
                                    {
                                        (ty.as_info_instanced(&mut ir.types, generics), i)
                                    } else {
                                        ctx.errors.emit_span(Error::NonexistantMember, name_span.in_mod(ctx.module));
                                        (TypeInfo::Invalid.into(), 0)
                                    }
                                }
                                TypeDef::Enum(_) => {
                                    todo!("Enum functions")
                                }
                                TypeDef::NotGenerated { .. } => unreachable!()
                            }
                        }
                        TypeInfo::Invalid => (TypeInfo::Invalid.into(), 0),
                        TypeInfo::Unknown => {
                            ctx.errors.emit_span(Error::TypeMustBeKnownHere, ctx.span(left));
                            (TypeInfo::Invalid.into(), 0)
                        }
                        _ => {
                            ctx.errors.emit_span(Error::NonexistantMember, name_span.in_mod(ctx.module));
                            (TypeInfo::Invalid.into(), 0)
                        }
                    };
                    ir.types.specify_or_merge(info.expected, ty, &mut ctx.errors, ctx.module, expr.span(ctx.ast),
                        &ctx.ctx);
                    let ptr = ir.types.add(TypeInfo::Pointer(info.expected));
                    let member = if is_ptr {
                        ir.build_member_int(val, idx as u32, ptr)
                    } else {
                        eprintln!("TODO: this member will probably not work because we need a ptr");
                        ir.build_member_int(val, idx as u32, ptr)
                    };
                    return (ExprResult::VarRef(member), true);
                }
                MemberAccessType::Module(id) => {
                    if let Some(symbol) = ctx.resolve_module_symbol(id, member) {
                        return (match symbol {
                            Symbol::Func(f) => ExprResult::Symbol(ConstSymbol::Func(f)),
                            Symbol::GenericFunc(f) => ExprResult::Symbol(ConstSymbol::GenericFunc(f)),
                            Symbol::Type(t) => ExprResult::Symbol(ConstSymbol::Type(t)),
                            Symbol::Trait(t) => ExprResult::Symbol(ConstSymbol::Trait(t)),
                            Symbol::LocalType(t) => ExprResult::Symbol(ConstSymbol::LocalType(t)),
                            Symbol::Generic(_) => todo!(), // is this a possibility
                            Symbol::Module(m) => ExprResult::Symbol(ConstSymbol::Module(m)),
                            Symbol::Var { .. } => unreachable!("vars in module shouldn't exist"),
                            Symbol::GlobalVar(key) => {
                                let (ty, _) = ctx.ctx.get_global(key);
                                let ty_info = ty.as_info(&mut ir.types);
                                let span = name_span.in_mod(ctx.module);
                                ir.types.specify(info.expected, ty_info, &mut ctx.errors, span, &ctx.ctx);
                                ExprResult::VarRef(ir.build_global(key, info.expected))
                            }
                            Symbol::Const(key) => {
                                let val = ctx.ctx.get_const(key);
                                const_eval::to_expr_result(val, ir, info)
                            }
                            Symbol::Invalid => {
                                ir.invalidate(info.expected);
                                ExprResult::Val(Ref::UNDEF)
                            }
                        }, true);
                    } else {
                        ctx.errors.emit_span(Error::UnknownIdent, name_span.in_mod(ctx.module));
                        ir.invalidate(info.expected);
                        Ref::UNDEF
                    }
                }
                MemberAccessType::Associated(key) => {
                    match ctx.ctx.get_type(key) {
                        TypeDef::Struct(def) => {
                            if let Some(method) = def.functions.get(member) {
                                return (ExprResult::Symbol(ConstSymbol::Func(*method)), true);
                            } else {
                                ctx.errors.emit_span(Error::UnknownFunction, name_span.in_mod(ctx.module));
                                ir.invalidate(info.expected);
                                Ref::UNDEF
                            }
                        }
                        TypeDef::Enum(def) => {
                            let expr_span = ctx.span(expr);
                            return (if let Some(&variant) = def.variants.get(member) {
                                ir.types.specify(info.expected, TypeInfo::Resolved(key, TypeTableIndices::EMPTY),
                                    &mut ctx.errors, expr_span, &ctx.ctx);
                                let r = ir.build_int(variant as u64, info.expected);
                                ExprResult::Val(r)
                            } else {
                                ctx.errors.emit_span(Error::NonexistantEnumVariant, name_span.in_mod(ctx.module));
                                ir.invalidate(info.expected);
                                ExprResult::Val(Ref::UNDEF)
                            }, true)
                        }
                        TypeDef::NotGenerated { .. } => unreachable!()
                    }
                }
                MemberAccessType::TraitFunction(t) => {
                    if let Some((idx, _)) = ctx.ctx.get_trait(t).functions.get(member) {
                        return (ExprResult::Symbol(ConstSymbol::TraitFunc(t, *idx)), true);
                    } else {
                        ctx.errors.emit_span(Error::UnknownFunction, name_span.in_mod(ctx.module));
                        ir.invalidate(info.expected);
                        Ref::UNDEF
                    }
                }
                MemberAccessType::Invalid => {
                    ir.invalidate(info.expected);
                    Ref::UNDEF
                }
            }, true)
        }
        Expr::Index { expr: indexed, idx, end: _ } => {
            let array_ty = ir.types.add(TypeInfo::Array(None, info.expected));
            let ptr_ty = ir.types.add(TypeInfo::Pointer(info.expected));
            let indexed = &ctx.ast[*indexed];
            let val = reduce_lval_expr(scope, ctx, ir, indexed, info.with_expected(array_ty), Error::CantIndex);
            
            let idx_ty = ir.types.add(TypeInfo::Int);
            let idx = val_expr(scope, ctx, ir, *idx, info.with_expected(idx_ty));
            return (ExprResult::VarRef(ir.build_member(val, idx, ptr_ty)), true)
        }
        Expr::TupleIdx { expr: indexed, idx, end: _ } => {
            let elem_types = ir.types.add_multiple_info_or_index(
                (0..if *idx == 0 { 0 } else { *idx - 1 }).map(|_| TypeInfoOrIndex::Type(TypeInfo::Unknown))
                .chain(std::iter::once(TypeInfoOrIndex::Idx(info.expected)))
            );

            let indexed_ty = ir.types.add(TypeInfo::Tuple(elem_types, TupleCountMode::AtLeast));
            let res = reduce_expr(scope, ctx, ir, &ctx.ast[*indexed], info.with_expected(indexed_ty));
            let expr_var = match res {
                ExprResult::VarRef(r) | ExprResult::Stored(r) => r,
                ExprResult::Val(val) => {
                    let var = ir.build_decl(info.expected);
                    ir.build_store(var, val);
                    var
                }
                ExprResult::Method(_, _) | ExprResult::Symbol(_) => {
                    ctx.errors.emit_span(Error::TupleIndexingOnNonValue, ctx.span(expr));
                    ir.invalidate(info.expected);
                    return (ExprResult::Val(Ref::UNDEF), true)
                }
            };
            
            let elem_ty_ptr = ir.types.add(TypeInfo::Pointer(info.expected));
            let member = ir.build_member_int(expr_var, *idx as u32, elem_ty_ptr);
            return (ExprResult::VarRef(member), true);
        }
        Expr::Cast(span, target, val) => {
            let target = match scope.resolve_type(target, &mut ir.types, ctx) {
                Ok(target) => target,
                Err(err) => {
                    ctx.errors.emit_span(err, span.in_mod(ctx.module));
                    TypeInfo::Invalid
                }
            };

            ir.specify(info.expected, target, &mut ctx.errors, expr.span(ctx.ast), &ctx.ctx);
            let inner_ty = ir.types.add(TypeInfo::Unknown);
            let val = val_expr(scope, ctx, ir, *val, info.with_expected(inner_ty));
            //TODO: check table for available casts
            (ir.build_cast(val, info.expected), true)
        }
        Expr::Root(_) => {
            return (ExprResult::Symbol(ConstSymbol::Module(ctx.ast[ctx.module].root_module)), true)
        }
        Expr::Asm { span: _, asm_str_span, args } => {
            let expr_refs = ctx.ast[*args].iter()
            .map(|arg| {
                let info = info.with_expected(ir.types.add_unknown());
                val_expr(scope, ctx, ir, *arg, info)
            })
            .collect::<Vec<_>>();
            
            let asm_str = ctx.src(TSpan::new(asm_str_span.start + 1, asm_str_span.end - 1));
            ir.build_asm(asm_str, expr_refs);
            return (ExprResult::Val(Ref::UNDEF), false)
        }
    };
    (ExprResult::Val(r), should_use)
}

fn call(
    func: ExprRef, args: ExprExtra, call_expr: &Expr,
    ctx: &mut GenCtx, ir: &mut IrBuilder, scope: &mut Scope, mut info: ExprInfo,
    get_var: impl Fn(&mut IrBuilder) -> Ref,
) -> (ExprResult, bool) {
    struct FuncInfo {
        params: TypeTableIndices,
        ret: TypeTableIndex,
        varargs: bool,
        key: SymbolKey,
    }
    fn gen_call(
        scope: &mut Scope,
        ctx: &mut GenCtx,
        expr: &Expr,
        f: FuncInfo,
        this_arg: Option<(Ref, TypeTableIndex, TSpan)>,
        args: impl ExactSizeIterator<Item = ExprRef>,
        ir: &mut IrBuilder,
        mut info: ExprInfo,
    ) -> Ref {
        let arg_count = args.len() + this_arg.is_some() as usize;
        /*let mut get_header_types = |header: &crate::ir::FunctionHeader| {
            let params = header.params
                .iter()
                .map(|(_, ty)| ty.as_info(&mut ir.types))
                .collect::<Vec<_>>();
            (
                ir.types.add_multiple(params),
                header.return_type.as_info(&mut ir.types),
                header.varargs,
                None,
            )
        };*/

        if let TypeInfo::Primitive(Primitive::Never) = ir.types.get_type(f.ret) {
            *info.noreturn = true;
        }
        ir.types.merge(info.expected, f.ret, &mut ctx.errors, expr.span_in(ctx.ast, ctx.module), &ctx.ctx);

        let invalid_arg_count = if f.varargs {
            arg_count < f.params.len()
        } else {
            arg_count != f.params.len()
        };
        if invalid_arg_count {
            ctx.errors.emit_span(Error::InvalidArgCount, expr.span(ctx.ast).in_mod(ctx.module));
            Ref::UNDEF
        } else {
            let mut arg_refs = Vec::with_capacity(arg_count + this_arg.is_some() as usize);
            let mut param_iter = f.params.iter();
            if let Some((this, this_ty, this_span)) = this_arg {
                // argument count was checked above so the iterator will only be empty if varargs are used.
                let ty = param_iter.next().unwrap_or_else(|| ir.types.add_unknown());
                ir.types.merge(this_ty, ty, &mut ctx.errors,
                    this_span.in_mod(ctx.module), &ctx.ctx
                );
                arg_refs.push(this);
            }
            for arg in args {
                let ty = param_iter.next().unwrap_or_else(|| ir.types.add_unknown());
                let expr = val_expr(scope, ctx, ir, arg, info.with_expected(ty));
                arg_refs.push(expr);
            }
            let call_ref = ir.build_call(f.key, arg_refs, info.expected);
            call_ref
        }
    }
    let args = &ctx.ast[args];
    let called_ty = ir.types.add(TypeInfo::Unknown);
    let called = &ctx.ast[func];
    let func_info = |header: &FunctionHeader, generics, key, ir: &mut IrBuilder| {
        let params = header.params.iter().map(|(_, ty)| ty.as_info_instanced(&mut ir.types, generics)).collect::<Vec<_>>();
        let ret = header.return_type.as_info_instanced(&mut ir.types, generics);
        
        FuncInfo {
            params: ir.types.add_multiple_info_or_index(params),
            ret: match ret {
                crate::ir::TypeInfoOrIndex::Type(ty) => ir.types.add(ty),
                crate::ir::TypeInfoOrIndex::Idx(idx) => idx,
            },
            varargs: header.varargs,
            key,
        }
    };
    let r = match reduce_expr(scope, ctx, ir, called, info.with_expected(called_ty)) {
        ExprResult::Symbol(ConstSymbol::Func(key)) => {
            let header = ctx.ctx.get_func(key).header();
            let f = func_info(header, TypeTableIndices::EMPTY, key, ir);
            gen_call(scope, ctx, call_expr, f, None, args.iter().copied(), ir, info)
        }
        ExprResult::Symbol(ConstSymbol::GenericFunc(idx)) => {
            let func = &ctx.ctx.generic_funcs[idx as usize];
            let generics = ir.types.add_multiple_unknown(func.generic_count as _);
            let f = func_info(&func.header, generics, SymbolKey::MISSING, ir);
            let val = gen_call(scope, ctx, call_expr, f, None, args.iter().copied(), ir, info);
            ir.add_generic_instantiation(idx, generics, val);
            val
        }
        ExprResult::Method(self_var, key) => {
            let called_span = called.span(ctx.ast);
            let this = Some((self_var, called_ty, called_span));
            let header = ctx.ctx.get_func(key).header();
            let f = func_info(header, TypeTableIndices::EMPTY, key, ir);
            gen_call(scope, ctx, call_expr, f, this, args.iter().copied(), ir, info)
        }
        ExprResult::Symbol(ConstSymbol::Type(ty)) => {
            let (_, TypeDef::Struct(struct_)) = &ctx.ctx.types[ty.idx()] else {
                ctx.errors.emit_span(Error::FunctionOrStructTypeExpected, ctx.span(called));
                return (ExprResult::Val(Ref::UNDEF), false)
            };
            let generics = ir.types.add_multiple_unknown(struct_.generic_count as _);
            ir.specify(info.expected, TypeInfo::Resolved(ty, generics), &mut ctx.errors, call_expr.span(ctx.ast),
                &ctx.ctx);

            if args.len() == struct_.members.len() {
                let var = get_var(ir);
                let member_types: Vec<_> =
                    struct_.members.iter()
                        .map(|(_, ty)| ty.as_info_instanced(&mut ir.types, generics))
                        .collect();
                for (i, (member_val, member_ty)) in
                    args.iter().zip(member_types).enumerate()
                {
                    let member_ty = ir.types.add_info_or_idx(member_ty);
                    let member_ty_ptr = ir.types.add(TypeInfo::Pointer(member_ty));
                    let member_val =
                        val_expr(scope, ctx, ir, *member_val, info.with_expected(member_ty));
                    let member = ir.build_member_int(var, i as u32, member_ty_ptr);

                    ir.build_store(member, member_val);
                }
                return (ExprResult::Stored(var), true);
            } else {
                ctx.errors.emit_span(Error::InvalidArgCount, call_expr.span(ctx.ast).in_mod(ctx.module));
                return (ExprResult::Val(Ref::UNDEF), true)
            }
        }
        _ => {
            if !ir.types.get_type(called_ty).is_invalid() {
                ctx.errors.emit_span(
                    Error::FunctionOrStructTypeExpected,
                    called.span(ctx.ast).in_mod(ctx.module)
                );
            }
            ir.invalidate(info.expected);
            Ref::UNDEF
        }
    };
    (ExprResult::Val(r), false)
}

fn gen_if_then(scope: &mut Scope, ctx: &mut GenCtx, ir: &mut IrBuilder, cond: ExprRef, ret: TypeTableIndex,
    noreturn: &mut bool)
-> BlockIndex {
    let b = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
    let cond = val_expr(scope, ctx, ir, cond, ExprInfo { expected: b, ret, noreturn });
    let then_block = ir.create_block();
    let other_block = ir.create_block();

    ir.build_branch(cond, then_block, other_block);
    ir.begin_block(then_block);
    other_block
}
