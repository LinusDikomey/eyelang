use crate::{
    ast::{ExprRef, self, CallId, ExprExtra},
    error::Error,
    token::{FloatLiteral, IntLiteral, Operator},
    types::Primitive,
    resolve::{exhaust::Exhaustion, types::ResolvedTypeDef},
    dmap, span::TSpan
};

use super::{
    Ctx,
    type_info::{TypeInfo, TypeInfoOrIndex, TypeTableIndex, TypeTableIndices},
    Ident,
    ResolvedCall,
    scope::{LocalScope, ExprInfo, LocalDefId},
    types::{DefId, TupleCountMode}, MemberAccess
};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum UseHint {
    Should,
    Can,
}

pub enum Res {
    Val { use_hint: UseHint, lval: bool }
}
impl Res {
    fn should_use(&self) -> UseHint {
        match self {
            Res::Val { use_hint, lval: _ } => *use_hint,
        }
    }
}

impl<'a> LocalScope<'a> {
    pub(super) fn val_expr(&mut self, expr: ExprRef, info: ExprInfo, mut ctx: Ctx, unused: bool) {
        match self.expr(expr, info, ctx.reborrow(), false) {
            Res::Val { use_hint, lval: _ } => {
                if use_hint == UseHint::Should && unused {
                    ctx.errors.emit_span(Error::UnusedExpressionValue, self.span(expr, ctx.ast));
                }
            }
            /*Res::Symbol(_) | Res::Method(_) => {
                ctx.errors.emit_span(Error::ExpectedValue, self.span(expr, ctx.ast));
                ValRes { lval: false }
            }*/
        }
    }

    #[must_use]
    pub(super) fn expr(&mut self, expr: ExprRef, mut info: ExprInfo, mut ctx: Ctx, hole_allowed: bool) -> Res {
        ctx.symbols.expr_types[expr.idx()] = info.expected;
        let mut use_hint = UseHint::Can;
        let mut lval = false;

        match &ctx.ast[expr] {
            ast::Expr::Block { span: _, items, defs } => {
                let mut block_scope = self.child_with_defs(&ctx.ast[*defs], ctx.ast, ctx.symbols, ctx.errors);

                for item in &ctx.ast[*items] {
                    let expected = ctx.types.add_unknown();
                    let res = block_scope.expr(*item, info.with_expected(expected), ctx.reborrow(), false);
                    if res.should_use() == UseHint::Should {
                        ctx.errors.emit_span(Error::UnusedExpressionValue, self.span(*item, ctx.ast));
                    }
                }
            }
            ast::Expr::Declare { pat, annotated_ty } => {
                let ty = self.resolve_type_info(annotated_ty, ctx.types, ctx.errors, ctx.symbols, ctx.ast);
                let ty = ctx.types.add_info_or_idx(ty);

                let mut exhaustion = Exhaustion::None;
                self.pat(*pat, ty, ctx.reborrow(), &mut exhaustion);
                if !matches!(exhaustion.is_exhausted(None, &ctx.symbols), Some(true)) {
                    ctx.errors.emit_span(Error::Inexhaustive, self.span(*pat, ctx.ast));
                }
            }
            ast::Expr::DeclareWithVal { pat, annotated_ty, val } => {
                let ty = self.resolve_type_info(annotated_ty, ctx.types, ctx.errors, ctx.symbols, ctx.ast);
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
            ast::Expr::StringLiteral(span) => {
                use_hint = UseHint::Should;
                let i8_ty = ctx.types.add(TypeInfo::Primitive(Primitive::I8));
                let ty = TypeInfo::Pointer(i8_ty);
                ctx.specify(info.expected, ty, span.in_mod(self.scope.module.id))
            }
            ast::Expr::BoolLiteral { .. } => {
                ctx.specify(info.expected, TypeInfo::Primitive(Primitive::Bool), self.span(expr, ctx.ast));
                use_hint = UseHint::Should;
            }
            ast::Expr::EnumLiteral { ident, .. } => {
                let name = &self.scope.module.src()[ident.range()];
                ctx.specify_enum_variant(info.expected, name, ident.in_mod(self.scope.module.id))
            }
            ast::Expr::Record { .. } => todo!("record literals"),
            ast::Expr::Nested(_, inner) => return self.expr(*inner, info, ctx, hole_allowed),
            ast::Expr::Unit(_) => {
                ctx.specify(info.expected, TypeInfo::UNIT, self.span(expr, ctx.ast));
            }
            ast::Expr::Variable { span, id } => {
                let name = &self.scope.module.src()[span.range()];
                let resolved = self.resolve_local(name, *span, ctx.errors, ctx.symbols, ctx.ast);
                let ident = match resolved {
                    LocalDefId::Def(DefId::Invalid) => {
                        ctx.types.invalidate(info.expected);
                        Ident::Invalid
                    }
                    LocalDefId::Def(DefId::Global(id)) => {
                        lval = true;

                        let (_, ty, _) = ctx.symbols.get_global(id);
                        let global_ty = ty.as_info(ctx.types, |_| panic!("global type shouldn't be generic"));
                        let span = self.span(expr, ctx.ast);
                        ctx.types.specify_or_merge(info.expected, global_ty, ctx.errors, span, ctx.symbols);

                        Ident::Global(id)
                    }
                    LocalDefId::Def(def) => {
                        ctx.specify(info.expected, TypeInfo::SymbolItem(def), span.in_mod(self.mod_id()));
                        Ident::Invalid
                    }
                    LocalDefId::Var(var) => {
                        lval = true;

                        let ty = ctx.var(var).ty;
                        ctx.merge(info.expected, ty, span.in_mod(self.mod_id()));
                        Ident::Var(var)
                    }
                    LocalDefId::Type(idx) => {
                        ctx.specify(info.expected, TypeInfo::LocalTypeItem(idx), span.in_mod(self.mod_id()));
                        Ident::Invalid
                    }
                };
                ctx.set_ident(*id, ident);
            }
            ast::Expr::Hole(_) => if !hole_allowed {
                ctx.errors.emit_span(Error::HoleLHSOnly, self.span(expr, ctx.ast));
            }
            ast::Expr::Array(span, elems) => {
                use_hint = UseHint::Should;

                let elems = &ctx.ast[*elems];
                let elem_ty = ctx.types.add_unknown();
                let arr_ty = TypeInfo::Array(Some(elems.len() as u32), elem_ty);
                ctx.specify(info.expected, arr_ty, span.in_mod(self.mod_id()));
                
                for elem in elems.iter() {
                    self.val_expr(*elem, info.with_expected(elem_ty), ctx.reborrow(), false);
                }
            }
            ast::Expr::Tuple(span, elems) => {
                let elem_types = ctx.types.add_multiple_unknown(elems.count);
                let tuple_ty = TypeInfo::Tuple(elem_types, TupleCountMode::Exact);
                ctx.specify(info.expected, tuple_ty, span.in_mod(self.mod_id()));

                for (elem, elem_ty) in ctx.ast[*elems].iter().zip(elem_types.iter()) {
                    self.val_expr(*elem, info.with_expected(elem_ty), ctx.reborrow(), false);
                }
            }
            ast::Expr::If { cond, then, .. } => {
                ctx.specify(info.expected, TypeInfo::UNIT, self.span(expr, ctx.ast));

                let bool_ty = ctx.types.add(TypeInfo::Primitive(Primitive::Bool));
                self.val_expr(*cond, info.with_expected(bool_ty), ctx.reborrow(), false);

                let then_ty = ctx.types.add_unknown();
                self.val_expr(*then, info.with_expected(then_ty), ctx, true);
            }
            ast::Expr::IfElse { cond, then, else_, .. } => {
                let bool_ty = ctx.types.add(TypeInfo::Primitive(Primitive::Bool));
                self.val_expr(*cond, info.with_expected(bool_ty), ctx.reborrow(), false);

                let mut then_noreturn = false;
                let mut else_noreturn = false;
                // TODO: setting unused to false can be incorrect if the if-else is unused
                self.val_expr(*then, info.with_noreturn(&mut then_noreturn), ctx.reborrow(), false);
                self.val_expr(*else_, info.with_noreturn(&mut else_noreturn), ctx, false);
                if then_noreturn && else_noreturn {
                    info.mark_noreturn();
                }
            }
            ast::Expr::Match { span: _, val, extra_branches, branch_count } => {
                let matched_ty = ctx.types.add_unknown();
                self.val_expr(*val, info.with_expected(matched_ty), ctx.reborrow(), false);
                let extra = &ctx.ast[ExprExtra { idx: *extra_branches, count: *branch_count * 2 }];
                let mut all_noreturn = true;
                let mut exhaustion = Exhaustion::None;
                for [pat, branch] in extra.array_chunks() {
                    let mut branch_scope = self.child(dmap::new());
                    
                    branch_scope.pat(*pat, matched_ty, ctx.reborrow(), &mut exhaustion);

                    let mut branch_noreturn = false;
                    branch_scope.val_expr(*branch, info.with_noreturn(&mut branch_noreturn), ctx.reborrow(), false);
                    all_noreturn &= branch_noreturn;
                }
                if all_noreturn {
                    info.mark_noreturn();
                }
            }
            ast::Expr::While { start: _, cond, body } => {
                ctx.specify(info.expected, TypeInfo::UNIT, self.span(expr, ctx.ast));

                let bool_ty = ctx.types.add(TypeInfo::Primitive(Primitive::Bool));
                self.val_expr(*cond, info.with_expected(bool_ty), ctx.reborrow(), false);

                let body_ty = ctx.types.add_unknown();
                let mut body_noreturn = false;
                self.val_expr(*body, info.with_expected(body_ty).with_noreturn(&mut body_noreturn), ctx, true);
            }
            ast::Expr::FunctionCall(call) => {
                return self.call(*call, expr, info, ctx);
            }
            ast::Expr::UnOp(_, op, val) => {
                use_hint = UseHint::Should;
                match op {
                    ast::UnOp::Neg => {
                        // TODO: type check negation properly (number TypeInfo or traits)
                        self.val_expr(*val, info, ctx, false);
                    }
                    ast::UnOp::Not => {
                        ctx.specify(info.expected, TypeInfo::Primitive(Primitive::Bool), self.span(expr, ctx.ast));
                        self.val_expr(*val, info, ctx, false);
                    }
                    ast::UnOp::Ref => {
                        let pointee_ty = ctx.types.add_unknown();
                        let ptr_ty = TypeInfo::Pointer(pointee_ty);
                        ctx.specify(info.expected, ptr_ty, self.span(*val, ctx.ast));
                        self.val_expr(*val, info.with_expected(pointee_ty), ctx, false);
                    }
                    ast::UnOp::Deref => {
                        lval = true;

                        let ptr_ty = ctx.types.add(TypeInfo::Pointer(info.expected));
                        self.val_expr(*val, info.with_expected(ptr_ty), ctx, false);
                    }
                }
            }
            &ast::Expr::BinOp(op, l, r) => {
                if let Operator::Assignment(_assign) = op {
                    ctx.specify(info.expected, TypeInfo::UNIT, self.span(expr, ctx.ast));
                    let var_ty = ctx.types.add_unknown();
                    self.val_expr(r, info.with_expected(var_ty), ctx.reborrow(), false);

                    // TODO: handle lvals properly
                    let lval = self.expr(l, info.with_expected(var_ty), ctx.reborrow(), true);
                    match lval {
                        Res::Val { use_hint: _, lval } => {
                            if !lval {
                                ctx.errors.emit_span(Error::CantAssignTo, self.span(l, ctx.ast));
                            }
                        }
                    }
                    // TODO: type checking for all assign variants like AddAssign (same with BinOp)
                } else {
                    use_hint = UseHint::Should;

                    let inner_ty = if op.is_boolean() {
                        ctx.types.add(TypeInfo::Primitive(Primitive::Bool))
                    } else if op.is_logical() {
                        ctx.types.add(TypeInfo::Unknown)
                    } else {
                        info.expected
                    };
                    self.val_expr(l, info.with_expected(inner_ty), ctx.reborrow(), false);
                    self.val_expr(r, info.with_expected(inner_ty), ctx, false);
                    if op == Operator::Range || op == Operator::RangeExclusive {
                        todo!("range operators only implemented in patterns for now")
                    }
                }
            }
            &ast::Expr::MemberAccess { left, name: name_span, id } => {
                let name = &ctx.ast.src(self.mod_id()).0[name_span.range()];
                use_hint = UseHint::Should;
                lval = true;
                let left_ty = ctx.types.add_unknown();
                let Res::Val { .. } = self.expr(left, info.with_expected(left_ty), ctx.reborrow(), false);
                // auto deref
                let mut deref_ty = ctx.types.get(left_ty);
                let (member_access, ty) = loop {
                    deref_ty = match deref_ty {
                        TypeInfo::Pointer(inner) => ctx.types.get(inner),
                        TypeInfo::Resolved(id, generics) => match ctx.symbols.get_type(id) {
                            ResolvedTypeDef::Struct(s) => {
                                let member = s.members
                                    .iter()
                                    .enumerate()
                                    .find(|(_, (member_name, _))| member_name == name);
                                if let Some((i, (_, ty))) = member {
                                    let ty = ty.as_info(ctx.types, |i| generics.nth(i as usize).into());
                                    break (MemberAccess::StructMember(i as _), ty);
                                } else if let Some(id) = s.methods.get(name) {
                                    let ty = TypeInfo::MethodItem { function: *id, this_ty: left_ty };
                                    break (MemberAccess::Method(*id), ty.into());
                                } else {
                                    ctx.errors.emit_span(Error::NonexistantMember, self.span(expr, ctx.ast));
                                    break (MemberAccess::Invalid, TypeInfo::Invalid.into());
                                }
                            }
                            ResolvedTypeDef::Enum(_) => {
                                ctx.errors.emit_span(Error::NonexistantMember, self.span(expr, ctx.ast));
                                break (MemberAccess::Invalid, TypeInfo::Invalid.into());
                            }
                            ResolvedTypeDef::NotGenerated { .. } => unreachable!(),
                        }
                        TypeInfo::Unknown => {
                            ctx.errors.emit_span(Error::TypeMustBeKnownHere, self.span(left, ctx.ast));
                            break (MemberAccess::Invalid, TypeInfo::Invalid.into());
                        }
                        TypeInfo::Invalid => {
                            break (MemberAccess::Invalid, TypeInfo::Invalid.into());
                        }
                        TypeInfo::Generic(_) => todo!("generic member checking (traits?)"),
                        TypeInfo::SymbolItem(DefId::Type(id)) => {
                            match name {
                                "size" => {
                                    ctx.specify(info.expected, TypeInfo::Primitive(Primitive::U64), self.span(expr, ctx.ast));
                                    break (MemberAccess::Size(id), TypeInfo::Primitive(Primitive::U64).into());
                                }
                                "align" => {
                                    ctx.specify(info.expected, TypeInfo::Primitive(Primitive::U64), self.span(expr, ctx.ast));
                                    break (MemberAccess::Align(id), TypeInfo::Primitive(Primitive::U64).into());
                                }
                                _ => {}
                            }
                            match ctx.symbols.get_type(id) {
                                ResolvedTypeDef::Struct(def) => match def.methods.get(name) {
                                    Some(method) => break (
                                        MemberAccess::Symbol(DefId::Function(*method)),
                                        TypeInfo::SymbolItem(DefId::Function(*method)).into()
                                    ),
                                    None => {
                                        ctx.errors.emit_span(Error::NonexistantMember, name_span.in_mod(self.mod_id()));
                                        break (MemberAccess::Invalid, TypeInfo::Invalid.into());
                                    }
                                }
                                ResolvedTypeDef::Enum(def) => {
                                    match def.variants.get(name) {
                                        Some(variant) => break (
                                            MemberAccess::EnumItem(id, *variant),
                                             // TODO: generic enums
                                            TypeInfo::Resolved(id, TypeTableIndices::EMPTY).into(),
                                        ),
                                        None => {
                                            ctx.errors.emit_span(Error::NonexistantMember, name_span.in_mod(self.mod_id()));
                                            break (MemberAccess::Invalid, TypeInfo::Invalid.into());
                                        }
                                    }
                                }
                                ResolvedTypeDef::NotGenerated { .. } => unreachable!(),
                            };
                        }
                        TypeInfo::SymbolItem(DefId::Module(id)) => {
                            let def = self.scope.module_scope(id)
                                .resolve(name, name_span.in_mod(self.mod_id()), ctx.errors, ctx.symbols, ctx.ast);
                            break (MemberAccess::Symbol(def), TypeInfo::SymbolItem(def).into());
                        }
                        TypeInfo::LocalTypeItem(idx) => {
                            match name {
                                "size" => {
                                    ctx.specify(info.expected, TypeInfo::Primitive(Primitive::U64), self.span(expr, ctx.ast));
                                    break (MemberAccess::LocalSize(idx), TypeInfo::Primitive(Primitive::U64).into());
                                }
                                "align" => {
                                    ctx.specify(info.expected, TypeInfo::Primitive(Primitive::U64), self.span(expr, ctx.ast));
                                    break (MemberAccess::LocalAlign(idx), TypeInfo::Primitive(Primitive::U64).into());
                                }
                                _ => todo!("member access on generics")
                            }
                        }
                        TypeInfo::SymbolItem(DefId::Function(_)) | TypeInfo::MethodItem { .. }
                        | TypeInfo::EnumItem(_, _)
                        | TypeInfo::Int | TypeInfo::Float | TypeInfo::Primitive(_)
                        | TypeInfo::SymbolItem(_)
                        | TypeInfo::Array(_, _) | TypeInfo::Tuple(_, _) | TypeInfo::Enum(_) => {
                            ctx.errors.emit_span(Error::NonexistantMember, self.span(expr, ctx.ast));
                            break (MemberAccess::Invalid, TypeInfo::Invalid.into());
                        }
                    }
                };
                ctx.symbols.member_accesses[id.idx()] = member_access;
                ctx.types.specify_or_merge(info.expected, ty, ctx.errors, self.span(expr, ctx.ast), ctx.symbols);
            }
            &ast::Expr::Index { expr, idx, .. } => {
                lval = true;
                
                let arr_ty = ctx.types.add(TypeInfo::Array(None, info.expected));
                self.val_expr(expr, info.with_expected(arr_ty), ctx.reborrow(), false);

                let idx_ty = ctx.types.add(TypeInfo::Int);
                self.val_expr(idx, info.with_expected(idx_ty), ctx, false);
            }
            &ast::Expr::TupleIdx { expr, idx, .. } => {
                lval = true;

                let elem_types = ctx.types.add_multiple_info_or_index(
                    (0..idx).map(|_| TypeInfoOrIndex::Type(TypeInfo::Unknown))
                    .chain(std::iter::once(TypeInfoOrIndex::Idx(info.expected)))
                );
    
                let tuple_ty = ctx.types.add(TypeInfo::Tuple(elem_types, TupleCountMode::AtLeast));
                self.val_expr(expr, info.with_expected(tuple_ty), ctx, false);
            }
            ast::Expr::Cast(span, ty, val) => {
                // TODO: check casts properly, maybe defer check to end of function
                let val_ty = ctx.types.add_unknown();
                self.val_expr(*val, info.with_expected(val_ty), ctx.reborrow(), false);
                let cast_info = self.resolve_type_info(ty, ctx.types, ctx.errors, ctx.symbols, ctx.ast);
                ctx.types.specify_or_merge(
                    info.expected, cast_info,
                    ctx.errors, span.in_mod(self.mod_id()), &ctx.symbols
                );
            }
            ast::Expr::Root(_) => {
                let ty = TypeInfo::SymbolItem(DefId::Module(self.scope.module.root));
                ctx.specify(info.expected, ty, self.span(expr, ctx.ast));
            }
            ast::Expr::Asm { .. } => todo!("inline asm is unsupported right now"),
        };
        Res::Val { use_hint, lval }
    }

    fn call(&mut self, id: CallId, call_expr: ExprRef, mut info: ExprInfo, mut ctx: Ctx) -> Res {
        
        let call = &ctx.ast[id];
        let called_ty = ctx.types.add_unknown();

        _ = self.expr(call.called_expr, info.with_expected(called_ty), ctx.reborrow(), false);
        let (res, call) = match ctx.types.get(called_ty) {
            TypeInfo::SymbolItem(DefId::Function(func_id)) => {                
                let call = self.call_func(func_id, ctx.reborrow(), None, call, call_expr, info);
                
                (Res::Val { use_hint: UseHint::Can, lval: false }, call)
            }
            TypeInfo::SymbolItem(DefId::Type(id)) => {
                match ctx.symbols.get_type(id) {
                    ResolvedTypeDef::Struct(def) => {
                        if call.args.count as usize != def.members.len() {
                            ctx.errors.emit_span(
                                Error::InvalidArgCount {
                                    expected: def.members.len() as _,
                                    varargs: false,
                                    found: call.args.count,
                                },
                                self.span(call_expr, ctx.ast)
                            )
                        }
                        let generics = ctx.types.add_multiple_unknown(def.generic_count() as _);
                        
                        
                        let arg_types = ctx.types.add_multiple_unknown(call.args.count);
                        for (i, (_, ty)) in def.members.iter().enumerate() {
                            let param_ty = ty.as_info(ctx.types, |i| generics.nth(i as usize).into());
                            ctx.types.replace_idx(arg_types.nth(i), param_ty);
                            
                        }
                        for (arg, ty) in ctx.ast[call.args].iter().zip(arg_types.iter()) {
                            self.val_expr(*arg, info.with_expected(ty), ctx.reborrow(), false);
                        }

                        ctx.specify(info.expected, TypeInfo::Resolved(id, generics), self.span(call_expr, ctx.ast));
                        
                        (
                            Res::Val { use_hint: UseHint::Can, lval: false },
                            ResolvedCall::Struct { type_id: id, generics }
                        )
                    }
                    ResolvedTypeDef::Enum(_) => {
                        ctx.errors.emit_span(
                            Error::FunctionOrStructTypeExpected,
                            ctx.ast[call.called_expr].span_in(&ctx.ast, self.scope.module.id),
                        );
                        (Res::Val { use_hint: UseHint::Can, lval: false }, ResolvedCall::Invalid)
                    }
                    ResolvedTypeDef::NotGenerated { .. } => unreachable!(),
                } 
            }
            TypeInfo::MethodItem { function: id, this_ty } => {
                let this = Some((this_ty, ctx.ast[call.called_expr].span(ctx.ast)));
                let call = self.call_func(id, ctx.reborrow(), this, call, call_expr, info);
                (Res::Val { use_hint: UseHint::Can, lval: false }, call)
            }
            _other => {
                if !ctx.types.invalidate(called_ty) {
                    ctx.errors.emit_span(
                        Error::FunctionOrStructTypeExpected,
                        ctx.ast[call.called_expr].span_in(&ctx.ast, self.scope.module.id)
                    );
                }
                (Res::Val { use_hint: UseHint::Can, lval: false }, ResolvedCall::Invalid)
            }
        };
        ctx.symbols.place_call(id, call);
        res
    }

    fn call_func(
        &mut self,
        func_id: ast::FunctionId,
        mut ctx: Ctx,
        this: Option<(TypeTableIndex, TSpan)>,
        call: &ast::Call,
        call_expr: ExprRef,
        mut info: ExprInfo
    )
    -> ResolvedCall {
        let sig = ctx.symbols.get_func(func_id);

        let generics = ctx.types.add_multiple_unknown(sig.generic_count() as _);
        let on_generic = |i| TypeInfoOrIndex::Idx(generics.nth(i as usize));

        let arg_count = call.args.count + this.is_some() as u32;

        match sig.params.len().cmp(&(arg_count as usize)) {
            std::cmp::Ordering::Less if sig.varargs => {}
            std::cmp::Ordering::Equal => {}
            _ => {
                ctx.errors.emit_span(Error::InvalidArgCount {
                    expected: sig.params.len() as _,
                    varargs: sig.varargs,
                    found: arg_count,
                }, self.span(call_expr, &ctx.ast));
            }
        }

        let ret = sig.return_type.as_info(ctx.types, on_generic);
        
        let call_span = self.span(call_expr, ctx.ast);
        ctx.types.specify_or_merge(info.expected, ret, ctx.errors, call_span, &ctx.symbols);
        
        let params = sig.params
            .iter()
            .map(|(_, ty)| {
                let ty = ty.as_info(ctx.types, on_generic);
                ctx.types.add_info_or_idx(ty)
            })
            .collect::<Vec<_>>();

        let mut params = params.into_iter();

        if let Some((this, this_span)) = this {
            let this_param = params.next().unwrap_or_else(|| ctx.types.add_unknown());
            ctx.types.merge_dereffed(this, this_param, ctx.errors, this_span.in_mod(self.mod_id()), ctx.symbols);
        }

        for arg in &ctx.ast[call.args] {
            let param_ty = params.next().unwrap_or_else(|| ctx.types.add_unknown());
            self.val_expr(*arg, info.with_expected(param_ty), ctx.reborrow(), false);
        }
        ResolvedCall::Function { func_id, generics }
    }
}

