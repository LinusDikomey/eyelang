use std::ops::Index;

use crate::{ast::{Ast, ExprRef, Expr, ModuleId, FunctionId}, resolve::{types::{SymbolTable, MaybeTypeDef, ResolvedTypeDef, FunctionHeader, Type}, self, type_info::{TypeTableIndex, TypeInfo, TypeTableIndices}, VarId}, ir::{self, Function, builder::{IrBuilder, BinOp}, Ref, RefVal, FunctionIr}, token::{IntLiteral, Operator}, span::TSpan, types::Primitive, dmap::{DHashMap, self}};


struct Ctx<'a> {
    ast: &'a Ast,
    symbols: &'a SymbolTable,
    var_refs: &'a mut [Ref],
    idents: &'a [resolve::Ident],
    //ident_refs: &'a mut [Ref],
    module: ModuleId,
    functions: &'a mut Functions,
}
impl<'a> Ctx<'a> {
    fn src(&self) -> &'a str {
        &self.ast.sources[self.module.idx()].0
    }
    fn src_at(&self, span: TSpan) -> &'a str {
        &self.src()[span.range()]
    }
}
impl<'a> Index<ExprRef> for Ctx<'a> {
    type Output = TypeTableIndex;

    fn index(&self, index: ExprRef) -> &Self::Output {
        &self.symbols.expr_types[index.idx()]
    }
}
impl<'a> Index<VarId> for Ctx<'a> {
    type Output = Ref;

    fn index(&self, index: VarId) -> &Self::Output {
        &self.var_refs[index.idx()]
    }
}

enum FunctionIds {
    Simple(ir::FunctionId),
    Generic(DHashMap<Vec<Type>, ir::FunctionId>)
}

struct Functions {
    // ir::FunctionId implied by position in functions_to_create
    functions_to_create: Vec<(FunctionId, Vec<Type>)>,
    ids: DHashMap<FunctionId, FunctionIds>, 
}
impl Functions {
    fn get(&mut self, function: FunctionId, symbols: &SymbolTable, generic_args: Vec<Type>) -> ir::FunctionId {
        if let Some(ids) = self.ids.get_mut(&function) {
            match ids {
                FunctionIds::Simple(id) => *id,
                FunctionIds::Generic(generic) => {
                    if let Some(id) = generic.get(generic_args.as_slice()) {
                        *id
                    } else {
                        let id = ir::FunctionId::new(self.functions_to_create.len() as u64);
                        self.functions_to_create.push((function, generic_args.clone()));
                        generic.insert(generic_args, id);

                        id
                    }
                }
            }
        } else {
            let id = ir::FunctionId::new(self.functions_to_create.len() as u64);
            let entry = if symbols.get_func(function).generic_count() != 0 {
                debug_assert_eq!(generic_args.len(), symbols.get_func(function).generic_count() as usize);
                self.functions_to_create.push((function, generic_args.clone()));
                let mut map = dmap::with_capacity(1);
                map.insert(generic_args, id);
                FunctionIds::Generic(map)
            } else {
                debug_assert!(generic_args.is_empty());
                self.functions_to_create.push((function, generic_args));
                FunctionIds::Simple(id)
            };
            self.ids.insert(function, entry);

            id
        }
    }
}

pub fn reduce(ast: &Ast, symbols: SymbolTable, main: Option<FunctionId>) -> ir::Module {
    let mut functions = Functions {
        functions_to_create: main.map_or(Vec::new(), |main| vec![(main, vec![])]),
        ids: dmap::new(),
    };

    let mut funcs: Vec<Function> = Vec::with_capacity(1);
    
    let mut i = 0;
    while i < functions.functions_to_create.len() {
        assert_eq!(i, funcs.len());

        // PERF: cloning here
        let (id, generic_instance) = functions.functions_to_create[i].clone();
        let header = symbols.get_func(id);
        let func = gen_func(header.clone(), &ast, &symbols, &mut functions, &generic_instance);

        // PERF: don't clone header here?
        funcs.push(func);
        i += 1;
    }

    let types = symbols.types.into_iter().map(|(name, def)| {
        let MaybeTypeDef::Some(ty) = def else { unreachable!() };
        (name, ty)
    }).collect();

    let globals = symbols.globals;

    ir::Module {
        name: "MainModule".to_owned(),
        funcs,
        globals,
        types,
    }
}

fn gen_func(
    mut header: FunctionHeader,
    ast: &Ast,
    symbols: &SymbolTable,
    functions: &mut Functions,
    generics: &[Type]
)
-> Function {
    let Some(body) = &mut header.resolved_body else { return Function {
        header, ir: None
    } };

    let mut builder = IrBuilder::new(&mut body.types);

    let mut var_refs = vec![Ref::UNDEF; body.vars.len()];

    for (i, (_, param_ty)) in header.params.iter().enumerate() {
        let ty = param_ty.as_info(builder.types, |_| todo!());
        let ty = builder.types.add_info_or_idx(ty);
        let ptr_ty = builder.types.add(TypeInfo::Pointer(ty));
        var_refs[i] = builder.build_param(i as u32, ptr_ty);
    }

    let mut noreturn = false;

    gen_expr(&mut builder, body.body, &mut Ctx {
        ast,
        symbols,
        var_refs: &mut var_refs,
        idents: &body.idents,
        module: header.module,
        functions,
    }, &mut noreturn);

    if !noreturn {
        debug_assert_eq!(
            header.return_type, Type::Prim(Primitive::Unit),
            "missing return value not caught in typecheck"
        );
        builder.build_ret_undef();
    }

    let ir = builder.finish();
    Function { header, ir: Some(ir) }
}

struct Res {
    r: Ref,
    is_ptr: bool,
}
impl Res {
    fn val(&self, ir: &mut IrBuilder, ty: TypeTableIndex) -> Ref {
        if self.is_ptr {
            ir.build_load(self.r, ty)
        } else {
            self.r
        }
    }
    fn var(&self, ir: &mut IrBuilder, ty: TypeTableIndex) -> Ref {
        if self.is_ptr {
            self.r
        } else {
            let var = ir.build_decl(ty);
            ir.build_store(var, self.r);
            var
        }
    }
}

fn val_expr(ir: &mut IrBuilder, expr: ExprRef, ctx: &mut Ctx, noreturn: &mut bool) -> Ref {
    let res = gen_expr(ir, expr, ctx, noreturn);
    if *noreturn {
        Ref::UNDEF
    } else {
        if res.is_ptr {
            ir.build_load(res.r, ctx[expr])
        } else {
            res.r
        }
    }
} 

fn gen_expr(ir: &mut IrBuilder, expr: ExprRef, ctx: &mut Ctx, noreturn: &mut bool) -> Res {
    debug_assert_eq!(*noreturn, false, "generating expression with noreturn enabled means dead code will be generated");
    let r = match &ctx.ast[expr] {
        Expr::Block { span, items, defs } => {
            for item in &ctx.ast[*items] {
                let res = gen_expr(ir, *item, ctx, noreturn);
                if *noreturn { break }
            }
            Ref::UNIT
        }
        Expr::Declare { pat, .. } => {
            let ty = ctx[*pat];
            let bool_ty = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
            gen_pat(ir, *pat, Ref::UNDEF, ty, bool_ty, ctx);
            Ref::UNIT
        }
        Expr::DeclareWithVal { pat, val, .. } => {
            let ty = ctx[*pat];
            let bool_ty = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
            let val = val_expr(ir, *val, ctx, noreturn);
            if ! *noreturn {
                gen_pat(ir, *pat, val, ty, bool_ty, ctx);
            }
            Ref::UNIT
        }
        Expr::Return { val, .. } => {
            let zero_sized = ir.types.get_type(ctx[*val])
                .is_zero_sized(TypeTableIndices::EMPTY, &ir.types, ctx.symbols);

            if zero_sized {
                ir.build_ret_undef();
            } else {
                let val = val_expr(ir, *val, ctx, noreturn);
                if !*noreturn {
                    ir.build_ret(val);
                }
            }
            *noreturn = true;
            Ref::UNDEF
        }
        Expr::ReturnUnit { .. } => {
            ir.build_ret_undef();
            *noreturn = true;
            Ref::UNDEF
        }
        Expr::IntLiteral(span) => {
            let lit = IntLiteral::parse(&ctx.src()[span.range()]);
            let ty = ctx[expr];
            int_literal(lit, ty, ir)
        }
        Expr::FloatLiteral(_) => todo!(),
        Expr::StringLiteral(_) => todo!(),
        Expr::BoolLiteral { start, val } => todo!(),
        Expr::EnumLiteral { dot, ident } => todo!(),
        Expr::Record { span, names, values } => todo!(),
        Expr::Nested(_, _) => todo!(),
        Expr::Unit(_) => Ref::UNIT,
        Expr::Variable { id, .. } => {
            match ctx.idents[id.idx()] {
                resolve::Ident::Invalid => unreachable!(),
                resolve::Ident::Var(var_id) => return Res { r: ctx.var_refs[var_id.idx()], is_ptr: true }
            }
        }
        Expr::Hole(_) => todo!(),
        Expr::Array(_, _) => todo!(),
        Expr::Tuple(_, _) => todo!(),
        Expr::If { start, cond, then } => todo!(),
        Expr::IfElse { start, cond, then, else_ } => todo!(),
        Expr::Match { start, end, val, extra_branches, branch_count } => todo!(),
        Expr::While { start, cond, body } => todo!(),
        Expr::FunctionCall(call_id) => {
            match &ctx.symbols.calls[call_id.idx()].unwrap() {
                resolve::ResolvedCall::Function { func_id, generics } => {
                    debug_assert_eq!(generics.len(), 0, "TODO: generics are unimplemented");
                    let func = ctx.symbols.get_func(*func_id);
                    let call = &ctx.ast.calls[call_id.idx()];

                    // PERF: reuse buffer here (maybe by pre-reserving in extra_refs buffer in ir)
                    let mut args = Vec::with_capacity(call.args.count as usize);
                    for arg in &ctx.ast[call.args] {
                        let arg_val = val_expr(ir, *arg, ctx, noreturn);
                        if *noreturn {
                            return Res { r: Ref::UNDEF, is_ptr: false }
                        }
                        args.push(arg_val);
                    }

                    let func_noreturn = func.return_type == Type::Prim(Primitive::Never);
                    let ty = ctx[expr];
                    
                    let generics = generics.iter().map(|idx| ir.types.get_type(idx).finalize(ir.types)).collect();
                    let ir_func_id = ctx.functions.get(*func_id, ctx.symbols, generics);
                    let call_val = ir.build_call(ir_func_id, args, ty);

                    if func_noreturn {
                        *noreturn = true;
                        ir.build_ret_undef();
                    }
                    call_val
                }
                resolve::ResolvedCall::Type(_) => todo!(),
                resolve::ResolvedCall::Invalid => todo!(),
            }
        }
        Expr::UnOp(_, _, _) => todo!(),
        Expr::BinOp(_, _, _) => todo!(),
        Expr::MemberAccess { left, name } => todo!(),
        Expr::Index { expr, idx, end } => todo!(),
        Expr::TupleIdx { expr, idx, end } => todo!(),
        Expr::Cast(_, _, _) => todo!(),
        Expr::Root(_) => todo!(),
        Expr::Asm { span, asm_str_span, args } => todo!(),
    };
    Res { r, is_ptr: false }
}

fn gen_pat(ir: &mut IrBuilder, pat: ExprRef, pat_val: Ref, ty: TypeTableIndex, bool_ty: TypeTableIndex, ctx: &mut Ctx) -> Ref {
    match &ctx.ast[pat] {
        Expr::IntLiteral(lit) => {
            let lit = IntLiteral::parse(&ctx.src()[lit.range()]);
            let int_val = int_literal(lit, ty, ir);
            ir.build_bin_op(BinOp::Eq, pat_val, int_val, bool_ty)
        }
        Expr::FloatLiteral(_) => todo!(),
        Expr::BoolLiteral { val, .. } => {
            let val = if *val {
                Ref::val(RefVal::True)
            } else {
                Ref::val(RefVal::False)
            };
            ir.build_bin_op(BinOp::Eq, pat_val, val, bool_ty)
        }
        Expr::EnumLiteral { ident, .. } => {
            let name = ctx.src_at(*ident);
            let ordinal = match ir.types.get_type(ty) {
                TypeInfo::Enum(variants) => ir.types.get_names(variants)
                    .iter()
                    .enumerate()
                    .find(|(_, n)| n.as_str() == name)
                    .unwrap()
                    .0 as u64,
                TypeInfo::Resolved(id, _generics) => {
                    let ResolvedTypeDef::Enum(def) = ctx.symbols.get_type(id) else { unreachable!() };
                    *def.variants.get(name).unwrap() as u64
                }
                _ => unreachable!()
            };
            let i = ir.build_int(ordinal, ty);
            ir.build_bin_op(BinOp::Eq, pat_val, i, bool_ty)
        }
        Expr::Nested(_, inner) => gen_pat(ir, *inner, pat_val, ty, bool_ty, ctx),
        Expr::Unit(_) => Ref::val(RefVal::True),
        Expr::Variable { id, .. } => {
            match ctx.idents[id.idx()] {
                resolve::Ident::Invalid => unreachable!(),
                resolve::Ident::Var(var_id) => {
                    let var = ir.build_decl(ty);
                    ir.build_store(var, pat_val);
                    ctx.var_refs[var_id.idx()] = var;
                }
            }
            Ref::val(RefVal::True)
        }
        Expr::Hole(_) => Ref::val(RefVal::True),
        Expr::BinOp(Operator::Range | Operator::RangeExclusive, l, r) => todo!(),
        Expr::Tuple(_, items) => {
            let TypeInfo::Tuple(types, _) = ir.types.get_type(ty) else {
                unreachable!()
            };
            let i32_ty = ir.types.add(TypeInfo::Primitive(Primitive::I32));
            let mut matches_bool = Ref::val(RefVal::True);
            for (i, (item, item_ty)) in ctx.ast[*items].iter().zip(types.iter()).enumerate() {
                let i_val = ir.build_int(i as u64, i32_ty);
                let item_val = ir.build_member(pat_val, i_val, item_ty);
                let item_matches = gen_pat(ir, *item, item_val, item_ty, bool_ty, ctx);
                matches_bool = ir.build_bin_op(BinOp::And, matches_bool, item_matches, item_ty);
            }
            matches_bool
        }

        Expr::Record { .. } // very useful to match on records
            | Expr::StringLiteral(_) // TODO definitely very important
            | Expr::Block { .. }
            | Expr::Declare { .. }
            | Expr::DeclareWithVal { .. }
            | Expr::Return { .. }
            | Expr::ReturnUnit { .. }
            | Expr::Array(_, _)
            | Expr::If { .. } 
            | Expr::IfElse { .. } 
            | Expr::Match { .. } 
            | Expr::While { .. } 
            | Expr::FunctionCall { .. } 
            | Expr::UnOp(_, _, _) 
            | Expr::BinOp(_, _, _) 
            | Expr::MemberAccess { .. } // maybe when variables are allowed. Also qualified enum variants!
            | Expr::Index { .. } 
            | Expr::TupleIdx { .. } 
            | Expr::Cast(_, _, _)
            | Expr::Root(_) 
            | Expr::Asm { .. } 
            => unreachable!(),
    }
}

fn int_literal(lit: IntLiteral, ty: TypeTableIndex, ir: &mut IrBuilder) -> Ref {
    // TODO: check int type for overflow
    if lit.val <= std::u64::MAX as u128 {
        ir.build_int(lit.val as u64, ty)
    } else {
        ir.build_large_int(lit.val, ty)
    }
}