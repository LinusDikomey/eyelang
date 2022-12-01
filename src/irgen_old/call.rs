use crate::{
    ast::{ExprRef, ExprExtra, Expr},
    ir::{
        Ref, TypeTableIndices, TypeTableIndex, SymbolKey,
        TypeInfo, FunctionHeader, ConstSymbol, StructMemberSymbol, TypeDef
    },
    span::TSpan,
    types::Primitive,
    error::Error,
};

use super::{GenCtx, IrBuilder, expr::ExprInfo, Scope, ExprResult, expr::{val_expr, reduce_expr}};

pub(super) fn call(
    func: ExprRef, args: ExprExtra, call_expr: &Expr,
    ctx: &mut GenCtx, ir: &mut IrBuilder, scope: &mut Scope, mut info: ExprInfo,
    get_var: impl Fn(&mut IrBuilder) -> Ref,
) -> (ExprResult, bool) {
    let args = &ctx.ast[args];
    let called_ty = ir.types.add(TypeInfo::Unknown);
    let called = &ctx.ast[func];

    let r = match reduce_expr(scope, ctx, ir, called, info.with_expected(called_ty)) {
        ExprResult::Symbol(ConstSymbol::Func(key)) => {
            let header = ctx.ctx.get_func(key).header();
            let f = func_info(header, TypeTableIndices::EMPTY, key, ir);
            gen_call(scope, ctx, call_expr, f, None, args.iter().copied(), ir, info)
        }
        ExprResult::Symbol(ConstSymbol::GenericFunc(key)) => {
            generic_call(key, None, args, call_expr, info, scope, ctx, ir)
        }
        ExprResult::Method { self_val, self_ty, method_symbol } => {
            let called_span = called.span(ctx.ast);
            let this = Some((self_val, self_ty, called_span));

            match method_symbol {
                StructMemberSymbol::Func(key) => {
                    let header = ctx.ctx.get_func(key).header();
                    let f = func_info(header, TypeTableIndices::EMPTY, key, ir);
                    gen_call(scope, ctx, call_expr, f, this, args.iter().copied(), ir, info)
                }
                StructMemberSymbol::GenericFunc(key) => {
                    generic_call(key, this, args, call_expr, info, scope, ctx, ir)
                }
            }
        }
        ExprResult::Symbol(ConstSymbol::Type(ty)) => {
            let (_, TypeDef::Struct(struct_)) = &ctx.ctx.types[ty.idx()] else {
                ctx.errors.emit_span(Error::FunctionOrStructTypeExpected, ctx.span(called));
                return (ExprResult::Val(Ref::UNDEF), false)
            };
            let generics = ir.types.add_multiple_unknown(struct_.generic_count as _);
            ir.specify(info.expected, TypeInfo::Resolved(ty, generics),
                &mut ctx.errors, call_expr.span(ctx.ast), &ctx.ctx);

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
                return (ExprResult::VarRef(var), true);
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

fn func_info(header: &FunctionHeader, generics: TypeTableIndices, key: SymbolKey, ir: &mut IrBuilder) -> FuncInfo {
    let params = header.params
        .iter()
        .map(|(_, ty)| ty.as_info_instanced(&mut ir.types, generics))
        .collect::<Vec<_>>();
    
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
}

fn generic_call(
    key: u32, this_arg: Option<(Ref, TypeTableIndex, TSpan)>, args: &[ExprRef], call_expr: &Expr, info: ExprInfo,
    scope: &mut Scope, ctx: &mut GenCtx, ir: &mut IrBuilder
) -> Ref {
    let func = ctx.ctx.get_generic_func(key);
    let generics = ir.types.add_multiple_unknown(func.generic_count() as _);
    crate::log!("generic call with generics {generics:?}");
    let f = func_info(&func.header, generics, SymbolKey::MISSING, ir);
    let val = gen_call(scope, ctx, call_expr, f, this_arg, args.iter().copied(), ir, info);
    if val != Ref::UNDEF {
        ir.add_generic_instantiation(key, generics, val);
    }
    val
}
