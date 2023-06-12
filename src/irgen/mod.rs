use std::ops::Index;

use crate::{
    ast::{Ast, ExprRef, Expr, ModuleId, FunctionId, UnOp, ExprExtra, MemberAccessId, VariantId},
    resolve::{
        types::{SymbolTable, MaybeTypeDef, Type, ResolvedFunc, Enum, ResolvedTypeBody},
        self,
        type_info::TypeInfo, VarId, MemberAccess},
    ir::{self, Function, builder::{IrBuilder, BinOp, IdxOrTy}, Ref, RefVal, types::{IrType, TypeRef, TypeRefs}, BlockIndex},
    token::{IntLiteral, Operator, AssignType, FloatLiteral}, span::TSpan, types::Primitive, dmap::{DHashMap, self}
};

mod const_val;
mod main_func;

/// Macro for internal errors. Indicates that type checking went wrong or some internal assumption was broken
macro_rules! int {
    () => {{
        
        line!();
        ::color_format::ceprintln!("#r<internal irgen error> at #u<{}:{}:{}>",
            ::core::file!(), ::core::line!(), ::core::column!()
        );
        panic!("internal error")
    }};
    ($($arg: tt)*) => {{
        ::color_format::ceprintln!("#r<internal irgen error>: {} at #u<{}:{}:{}>",
            format!($($arg)*),
            ::core::file!(), ::core::line!(), ::core::column!()
        );
        panic!("internal error")
    }}
}
pub struct Ctx<'a> {
    pub ast: &'a Ast,
    pub symbols: &'a SymbolTable,
    pub var_refs: &'a mut [Ref],
    pub idents: &'a [resolve::Ident],
    pub module: ModuleId,
    pub functions: &'a mut Functions,
    pub function_generics: &'a [Type],
    pub member_accesses: &'a [MemberAccess],
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
    type Output = TypeRef;

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
impl<'a> Index<MemberAccessId> for Ctx<'a> {
    type Output = MemberAccess;

    fn index(&self, index: MemberAccessId) -> &Self::Output {
        &self.member_accesses[index.idx()]
    }
}

#[derive(Debug)]
enum FunctionIds {
    Simple(ir::FunctionId, CreateReason),
    Generic(DHashMap<Vec<Type>, (ir::FunctionId, CreateReason)>)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub enum CreateReason {
    Comptime = 0,
    Runtime = 1,
}

#[derive(Debug)]
pub struct Functions {
    // ir::FunctionId implied by position in functions_to_create
    functions_to_create: Vec<(FunctionId, Vec<Type>)>,
    funcs: Vec<Option<Function>>,
    ids: DHashMap<FunctionId, FunctionIds>, 
}
impl Functions {
    pub fn new() -> Self {
        Self {
            functions_to_create: vec![],
            funcs: vec![],
            ids: dmap::new(),
        }
    }
    pub fn get(&mut self, function: FunctionId, symbols: &SymbolTable, generic_args: Vec<Type>, create_reason: CreateReason) -> ir::FunctionId {
        if let Some(ids) = self.ids.get_mut(&function) {
            match ids {
                FunctionIds::Simple(id, prev_create_reason) => {
                    if create_reason > *prev_create_reason {
                        *prev_create_reason = create_reason;
                    }
                    *id
                }
                FunctionIds::Generic(generic) => {
                    if let Some((id, prev_create_reason)) = generic.get_mut(generic_args.as_slice()) {
                        if create_reason > *prev_create_reason {
                            *prev_create_reason = create_reason;
                        }
                        *id
                    } else {
                        let id = ir::FunctionId::new(self.functions_to_create.len() as u64);
                        self.functions_to_create.push((function, generic_args.clone()), );
                        generic.insert(generic_args, (id, create_reason));

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
                map.insert(generic_args, (id, create_reason));
                FunctionIds::Generic(map)
            } else {
                debug_assert!(generic_args.is_empty());
                self.functions_to_create.push((function, generic_args));
                FunctionIds::Simple(id, create_reason)
            };
            self.ids.insert(function, entry);

            id
        }
    }
    pub fn get_ir<'a>(&'a mut self, id: ir::FunctionId, symbols: &SymbolTable, ast: &Ast) -> &'a Function {
        // if let gives a lifetime error here for some reason
        if self.funcs.get(id.idx()).map_or(false, |item| item.is_some()) {
            return self.funcs[id.idx()].as_ref().unwrap();
        }

        // PERF: cloning here
        let (ast_id, generic_instance) = self.functions_to_create[id.idx()].clone();
        let generic_header = symbols.get_func(ast_id);

        let mut name = generic_header.name.to_owned();
        if generic_instance.len() > 0 {
            name.push('[');
            let mut first = true;
            for ty in &generic_instance {
                if first {
                    first = false;
                } else {
                    name.push(',');
                }
                use std::fmt::Write;
                write!(name, "{}", ty.display_fn(|key| symbols.get_type(key).name())).unwrap();
            }
            name.push(']');
        }

        let params = generic_header.params
            .iter()
            .map(|(name, ty)| (name.clone(), ty.instantiate_generics(&generic_instance)))
            .collect();
        
        let return_type = generic_header.return_type.instantiate_generics(&generic_instance);
        let func = gen_func(
            name,
            params,
            generic_header.varargs,
            return_type,
            generic_header.module,
            generic_header.resolved_body.as_ref(),
            ast,
            &symbols,
            self,
            &generic_instance,
            CreateReason::Runtime, // FIXME: proper CreateReason?
        );

        if self.funcs.len() <= id.idx() {
            self.funcs.resize_with(id.idx() + 1, || None);
        }

        self.funcs[id.idx()] = Some(func);
        self.funcs[id.idx()].as_ref().unwrap()
    }
    pub fn finish_module(mut self, symbols: SymbolTable, ast: &Ast, main: Option<FunctionId>) -> ir::Module {
        
        let main_function = main.map(|main| {
            (
                self.get(main, &symbols, vec![], CreateReason::Runtime),
                symbols.get_func(main).module,
            )
        });
        
        let mut i: u64 = 0;
        while (i as usize) < self.functions_to_create.len() {
            self.get_ir(ir::FunctionId::new(i), &symbols, ast);
            i += 1;
        }

        let mut finished_functions = Vec::with_capacity(self.funcs.len() + main_function.is_some() as usize);
        finished_functions.extend(self.funcs.into_iter().map(|func| func.unwrap()));

        if let Some((main_id, main_module)) = main_function {
            // main is always at idx 0
    
            finished_functions[main_id.idx()].name = "eyemain".to_owned();
            let return_type = finished_functions[main_id.idx()].return_type.clone();
    
            let func = main_func::main_wrapper(main_id, main_module, return_type);
            finished_functions.push(func);
        }
        
        let types = symbols.types.into_iter().map(|(name, def)| {
            let MaybeTypeDef::Some(ty) = def else { int!() };
            (name, ty)
        }).collect();
    
        let globals = symbols.globals;

        ir::Module {
            name: "MainModule".to_owned(),
            funcs: finished_functions,
            globals: globals.into_iter().map(|global| global.unwrap()).collect(),
            types,
        }
    }
}

fn gen_func(
    name: String,
    params: Vec<(String, Type)>,
    varargs: bool,
    return_type: Type,
    module: ModuleId,
    body: Option<&ResolvedFunc>,
    ast: &Ast,
    symbols: &SymbolTable,
    functions: &mut Functions,
    generics: &[Type],
    create_reason: CreateReason,
)
-> Function {
    let Some(body) = body else {
        return Function {
            name,
            params,
            varargs,
            return_type,
            ir: None,
        }
    };

    debug_assert_eq!(body.types.generics().len(), generics.len());
    let mut ir_types = body.types.finalize();
    
    for (i, ty) in generics.iter().enumerate() {
        let ir_ty = ir_types.from_resolved(ty, TypeRefs::EMPTY);
        ir_types.instantiate_generic(i as u8, ir_ty);
    }
    let mut builder = IrBuilder::new(ir_types, &body.types, create_reason);

    let mut var_refs = vec![Ref::UNDEF; body.vars.len()];

    for (i, (_, param_ty)) in params.iter().enumerate() {
        let types_generics = builder.types.generics();
        let ty = builder.types.from_resolved(&param_ty.instantiate_generics(generics), types_generics);
        let ty = builder.types.add(ty);
        var_refs[i] = builder.build_param(i as u32, IrType::Ptr(ty));
    }

    let mut noreturn = false;

    let body_res = gen_expr(&mut builder, body.body, &mut Ctx {
        ast,
        symbols,
        var_refs: &mut var_refs,
        idents: &body.idents,
        module,
        functions,
        function_generics: generics,
        member_accesses: &symbols.member_accesses,
    }, &mut noreturn);
    if !noreturn {  
        if return_type == Type::Prim(Primitive::Unit) {
            builder.build_ret_undef();
        } else {
            let val = body_res.val(&mut builder, symbols.expr_types[body.body.idx()]);
            builder.build_ret(val);
        }
    }

    let ir = builder.finish();
    Function {
        name,
        params,
        varargs,
        return_type,
        ir: Some(ir),
    }
}

#[derive(Clone, Copy)]
pub enum Res {
    Val(Ref),
    Var(Ref),
    Hole,
}
impl Res {
    pub fn val(self, ir: &mut IrBuilder, ty: TypeRef) -> Ref {
        match self {
            Res::Val(r) => r,
            Res::Var(r) => ir.build_load(r, ty),
            Res::Hole => int!(),
        }
    }

    pub fn var(self, ir: &mut IrBuilder, ty: TypeRef) -> Ref {
        match self {
            Res::Val(r) => {
                let var = ir.build_decl(ty);
                ir.build_store(var, r);
                var
            }
            Res::Var(r) => r,
            Res::Hole => int!(),
        }
    }
}

fn val_expr(ir: &mut IrBuilder, expr: ExprRef, ctx: &mut Ctx, noreturn: &mut bool) -> Ref {
    let res = gen_expr(ir, expr, ctx, noreturn);
    if *noreturn {
        Ref::UNDEF
    } else {
        match res {
            Res::Val(r) => r,
            Res::Var(r) => ir.build_load(r, ctx[expr]),
            Res::Hole => int!(),
        }
    }
} 

pub fn gen_expr(ir: &mut IrBuilder, expr: ExprRef, ctx: &mut Ctx, noreturn: &mut bool) -> Res {
    debug_assert_eq!(*noreturn, false,
        "generating expression with noreturn enabled means dead code will be generated, expression is: {:?}",
        ctx.ast[expr],
    );
    let r = match &ctx.ast[expr] {
        Expr::Block { items, .. } => {
            for item in &ctx.ast[*items] {
                gen_expr(ir, *item, ctx, noreturn);
                if *noreturn { break }
            }
            Ref::UNIT
        }
        Expr::Declare { pat, .. } => {
            let ty = ctx[*pat];
            let bool_ty = ir.types.add(IrType::Primitive(Primitive::Bool));
            gen_pat(ir, *pat, Ref::UNDEF, ty, &mut |_ir| None, bool_ty, ctx);
            Ref::UNIT
        }
        Expr::DeclareWithVal { pat, val, .. } => {
            let ty = ctx[*pat];
            let bool_ty = ir.types.add(IrType::Primitive(Primitive::Bool));
            let val = val_expr(ir, *val, ctx, noreturn);
            if ! *noreturn {
                gen_pat(ir, *pat, val, ty, &mut |_ir| None, bool_ty, ctx);
            }
            Ref::UNIT
        }
        Expr::Return { val, .. } => {
            let val = val_expr(ir, *val, ctx, noreturn);
            if !*noreturn {
                ir.build_ret(val);
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
        Expr::FloatLiteral(span) => {
            let lit = FloatLiteral::parse(&ctx.src()[span.range()]);
            let ty = ctx[expr];
            ir.build_float(lit.val, ty)
        }
        Expr::StringLiteral(span) => {
            return Res::Var(string_literal(ir, *span, ctx));
        }
        Expr::BoolLiteral { val, .. } => if *val { Ref::val(RefVal::True) } else { Ref::val(RefVal::False) }
        &Expr::EnumLiteral { ident, args, .. } => {
            let name = ctx.src_at(ident);
            // TODO: enums with args
            let (variant_id, tag, int_ty) = match ir.inferred_types[ctx[expr]] {
                TypeInfo::Resolved(id, _generics) => {
                    let ResolvedTypeBody::Enum(def) = &ctx.symbols.get_type(id).body else { int!() };
                    let (variant_id, tag, _) = def.variants[name];
                    (variant_id, tag, def.int_ty())
                }
                TypeInfo::Enum(variants) => {
                    let variants = ir.inferred_types.get_enum_variants(variants);
                    let variant = variants
                        .iter()
                        .position(|(s, _)| s.as_str() == name)
                        .unwrap() as u32;

                    (VariantId::new(variant as u16), variant, Enum::int_ty_from_variant_count(variants.len() as u32))

                }
                _ => int!()
            };
            let enum_var = ir.build_decl(ctx[expr]);
            if let Some(int_ty) = int_ty {
                let ty = ir.types.add(IrType::Primitive(int_ty.into()));
                let tag_ty = ir.types.add(IrType::Primitive(Primitive::from(int_ty)));
                let val_tag_ptr = ir.build_enum_tag(enum_var, IrType::Ptr(tag_ty));
                let tag = ir.build_int(tag as u64, ty);
                ir.build_store(val_tag_ptr, tag);
            }
            for (i, arg) in ctx.ast[args].iter().copied().enumerate() {
                let arg_val = val_expr(ir, arg, ctx, noreturn);
                if *noreturn { break }
                let arg_ptr = ir.build_enum_variant_member(enum_var, variant_id, i as u16, IrType::Ptr(ctx[arg]));
                ir.build_store(arg_ptr, arg_val);
            }
            return Res::Var(enum_var)
        }
        Expr::Record { .. } => todo!(),
        Expr::Nested(_, inner) => return gen_expr(ir, *inner, ctx, noreturn),
        Expr::Unit(_) => Ref::UNIT,
        Expr::Variable { id, .. } => {
            match ctx.idents[id.idx()] {
                resolve::Ident::Invalid => return Res::Val(Ref::UNDEF),
                resolve::Ident::Var(var_id) => return Res::Var(ctx.var_refs[var_id.idx()]),
                resolve::Ident::Global(global_id) => {
                    let ty = &ctx.symbols.get_global(global_id).1;
                    let ty = ir.types.from_resolved(ty, TypeRefs::EMPTY);
                    let ty = ir.types.add(ty);
                    let ptr_ty = ir.types.add(IrType::Ptr(ty));
                    return Res::Var(ir.build_global(global_id, ptr_ty))
                }
                resolve::Ident::Function(_) => return Res::Val(Ref::UNIT), // implement function pointers here
                resolve::Ident::Module(_) => return Res::Val(Ref::UNDEF),
                resolve::Ident::Type(idx) => {
                    ir.build_type(idx)
                }
                resolve::Ident::Const(id) => {
                    let val = ctx.symbols.get_const(id);
                    return const_val::build(ir, val, ctx[expr]);
                }
            }
        }
        Expr::Hole(_) => return Res::Hole,
        &Expr::Array(_, values) => {
            let array_var = ir.build_decl(ctx[expr]);
            let IrType::Array(member_ty, _) = ir.types[ctx[expr]] else { int!() };
            let member_ptr_ty = ir.types.add(IrType::Ptr(member_ty));

            for (i, value) in ctx.ast[values].iter().enumerate() {
                let val = val_expr(ir, *value, ctx, noreturn);
                if *noreturn { return Res::Val(Ref::UNDEF) }
                let ptr = ir.build_member_int(array_var, i as u32, member_ptr_ty);
                ir.build_store(ptr, val);
            }
            return Res::Var(array_var);
        }
        &Expr::Tuple(_, values) => {
            let tuple_var = ir.build_decl(ctx[expr]);

            for (i, value) in ctx.ast[values].iter().enumerate() {
                let val = val_expr(ir, *value, ctx, noreturn);
                if *noreturn { return Res::Val(Ref::UNDEF) }
                let member_ptr_ty = ir.types.add(IrType::Ptr(ctx[*value]));
                let ptr = ir.build_member_int(tuple_var, i as u32, member_ptr_ty);
                ir.build_store(ptr, val);
            }
            return Res::Var(tuple_var);
        }
        &Expr::If { cond, then, .. } => {
            let cond = val_expr(ir, cond, ctx, noreturn);
            if *noreturn { return Res::Val(Ref::UNDEF) }
            let then_block = ir.create_block();
            let after_block = ir.create_block();
            ir.build_branch(cond, then_block, after_block);
            
            ir.begin_block(then_block);
            let mut then_noreturn = false;
            gen_expr(ir, then, ctx, &mut then_noreturn);
            if !then_noreturn {
                ir.build_goto(after_block);
            }

            ir.begin_block(after_block);
            Ref::UNIT
        }
        &Expr::IfPat { pat, value, then, .. } => {
            let value = val_expr(ir, value, ctx, noreturn);
            if *noreturn { return Res::Val(Ref::UNDEF) }
            let after_block = ir.create_block();
            let bool_ty = ir.types.add(IrType::Primitive(Primitive::Bool));
            gen_pat(ir, pat, value, ctx[pat], &mut |_| Some(after_block), bool_ty, ctx);
            
            let mut then_noreturn = false;
            gen_expr(ir, then, ctx, &mut then_noreturn);
            if !then_noreturn {
                ir.build_goto(after_block);
            }

            ir.begin_block(after_block);
            Ref::UNIT
        }
        &Expr::IfElse { cond, then, else_, .. } => {
            let cond = val_expr(ir, cond, ctx, noreturn);
            if *noreturn { return Res::Val(Ref::UNDEF) }
            
            let then_block = ir.create_block();
            let else_block = ir.create_block();

            ir.build_branch(cond, then_block, else_block);
            ir.begin_block(then_block);
            
            let ty = ctx[expr];
            build_then_else(ir, ctx, noreturn, ty, then, else_, else_block)
        }
        &Expr::IfPatElse { pat, value, then, else_, .. } => {
            let value = val_expr(ir, value, ctx, noreturn);
            if *noreturn { return Res::Val(Ref::UNDEF) }
            let else_block = ir.create_block();
            let bool_ty = ir.types.add(IrType::Primitive(Primitive::Bool));
            gen_pat(ir, pat, value, ctx[pat], &mut |_| Some(else_block), bool_ty, ctx);
            
            let ty = ctx[expr];
            build_then_else(ir, ctx, noreturn, ty, then, else_, else_block)
        }
        &Expr::Match { span: _, val, extra_branches, branch_count } => {
            let matched = val_expr(ir, val, ctx, noreturn);
            if *noreturn { return Res::Val(Ref::UNDEF) }

            let extra = &ctx.ast[ExprExtra { idx: extra_branches, count: branch_count * 2 }];
            let mut all_noreturn = true;
            let bool_ty = ir.types.add(IrType::Primitive(Primitive::Bool));

            let after_block = ir.create_block();

            let mut phi_vals = vec![];

            for (i, [pat, branch]) in extra.array_chunks().enumerate() {
                let mut next_block = None;
                gen_pat(ir, *pat, matched, ctx[val], &mut |ir| {
                    if let Some(next) = next_block { return Some(next) };
                    if i as u32 == branch_count - 1 {
                        None
                    } else {
                        let next = ir.create_block();
                        next_block = Some(next);
                        Some(next)
                    }
                }, bool_ty, ctx);

                let mut branch_noreturn = false;    
                let branch_val = val_expr(ir, *branch, ctx, &mut branch_noreturn);
                all_noreturn &= branch_noreturn;

                if !branch_noreturn {
                    ir.build_goto(after_block);
                    phi_vals.push((ir.current_block(), branch_val));
                }
                if let Some(next) = next_block {
                    ir.begin_block(next);
                }
            }
            ir.begin_block(after_block);
            *noreturn = all_noreturn;
            if all_noreturn {
                Ref::UNDEF
            } else {
                match phi_vals.as_slice() {
                    [(_, r)] => *r, // don't build a phi when only one branch yields a value
                    _ => ir.build_phi(phi_vals, ctx[expr])
                }
            }
        }
        &Expr::While { cond, body, .. } => {
            build_while_loop(ir, ctx, noreturn, body, |ir, ctx, noreturn, after_block| {
                let cond = val_expr(ir, cond, ctx, noreturn);
                if !*noreturn {
                    let body_block = ir.create_block();
                    ir.build_branch(cond, body_block, after_block);
                    ir.begin_block(body_block);
                }
            })
        }
        &Expr::WhilePat { start: _, pat, val, body } => {
            build_while_loop(ir, ctx, noreturn, body, |ir, ctx, noreturn, after_block| {
                let val = val_expr(ir, val, ctx, noreturn);
                if !*noreturn {
                    let bool_ty = ir.types.add(IrType::Primitive(Primitive::Bool));
                    gen_pat(ir, pat, val, ctx[pat], &mut |_| Some(after_block), bool_ty, ctx);
                }
            })
        }
        Expr::FunctionCall(call_id) => {
            let call = &ctx.ast.calls[call_id.idx()];
            match &ctx.symbols.calls[call_id.idx()].unwrap() {
                resolve::ResolvedCall::Function { func_id, generics } => {
                    let func = ctx.symbols.get_func(*func_id);

                    let this_arg = if let TypeInfo::MethodItem { this_ty, .. } = ir.inferred_types.get(ctx[call.called_expr]) {
                        let mut ptr_count = 0u32;
                        let mut current_ty = this_ty;
                        
                        while let IrType::Ptr(pointee) = ir.types[current_ty] {
                            current_ty = pointee;
                            ptr_count += 1;
                        }
                        let Expr::MemberAccess { left: this_expr, .. } = ctx.ast[call.called_expr] else { int!() };
                        let mut req_ptr_count = 0u32;
                        let mut cur_req_ty = &ctx.symbols.get_func(*func_id).params.first().unwrap().1;
                        while let Type::Pointer(pointee) = cur_req_ty {
                            cur_req_ty = pointee;
                            req_ptr_count += 1;
                        }
                        
                        let (mut val, val_is_var) = match gen_expr(ir, this_expr, ctx, noreturn) {
                            Res::Val(v) => (v, false),
                            Res::Var(v) => {
                                ptr_count += 1;
                                (v, true)
                            }
                            Res::Hole => int!(),
                        };
                        if *noreturn { return Res::Val(Ref::UNDEF) }
                        if req_ptr_count < ptr_count {
                            if val_is_var {
                                val = ir.build_load(val, this_ty);
                                ptr_count -= 1;
                            }
                            let mut loaded_ty = this_ty;
                            while req_ptr_count < ptr_count {
                                let IrType::Ptr(pointee) = ir.types[loaded_ty] else { int!() };
                                loaded_ty = pointee;
                                val = ir.build_load(val, loaded_ty);
                                ptr_count -= 1;
                            }
                        } else if req_ptr_count > ptr_count { 
                            let mut current_ref_ty = if val_is_var {
                                ir.types.add(IrType::Ptr(this_ty))
                            } else {
                                this_ty
                            };
                            while req_ptr_count > ptr_count {
                                current_ref_ty = ir.types.add(IrType::Ptr(current_ref_ty));
                                let var = ir.build_decl(current_ref_ty);
                                ir.build_store(var, val);
                                val = var;
                                ptr_count += 1;
                            }
                        }
                        Some(val)
                    } else {
                        None
                    };


                    // PERF: reuse buffer here (maybe by pre-reserving in extra_refs buffer in ir)
                    let mut args = Vec::with_capacity(call.args.count as usize + this_arg.is_some() as usize);
                    if let Some(this) = this_arg {
                        args.push(this);
                    }
                    for arg in &ctx.ast[call.args] {
                        let arg_val = val_expr(ir, *arg, ctx, noreturn);
                        if *noreturn {
                            return Res::Val(Ref::UNDEF)
                        }
                        args.push(arg_val);
                    }

                    let func_noreturn = func.return_type == Type::Prim(Primitive::Never);
                    let ty = ctx[expr];
                    
                    let generics = generics.iter()
                        .map(|idx| ir.types[idx]
                            .as_resolved_type(&ir.types)
                            .instantiate_generics(ctx.function_generics)
                        )
                        .collect();
                    // TODO: proper create reason? Can be a problem if function is first created for comptime but used at runtime
                    let ir_func_id = ctx.functions.get(*func_id, ctx.symbols, generics, CreateReason::Runtime);
                    let call_val = ir.build_call(ir_func_id, args, ty);

                    if func_noreturn {
                        *noreturn = true;
                        ir.build_ret_undef();
                    }
                    call_val
                }
                resolve::ResolvedCall::Struct { type_id, .. } => {
                    let ResolvedTypeBody::Struct(def) = &ctx.symbols.get_type(*type_id).body else { int!() };
                    debug_assert_eq!(def.members.len(), call.args.count as usize);
                    let ty = ctx[expr];

                    let var = ir.build_decl(ty);

                    for (i, arg) in ctx.ast[call.args].iter().enumerate() {
                        let member_val = val_expr(ir, *arg, ctx, noreturn);
                        if *noreturn {
                            return Res::Val(Ref::UNDEF)
                        }
                        let arg_ty = ctx[*arg];
                        let arg_ptr_ty = ir.types.add(IrType::Ptr(arg_ty));

                        let member_ptr = ir.build_member_int(var, i as u32, arg_ptr_ty);
                        ir.build_store(member_ptr, member_val);
                    }

                    return Res::Var(var)
                }
                resolve::ResolvedCall::Invalid => int!(),
            }
        }
        &Expr::UnOp(_, op, val) => {
            match op {
                UnOp::Neg => {
                    let ty = ctx[val];
                    let val = val_expr(ir, val, ctx, noreturn);
                    if *noreturn { return Res::Val(Ref::UNDEF) }
                    ir.build_neg(val, ty)
                }
                UnOp::Not => {
                    let ty = ctx[val];
                    let val = val_expr(ir, val, ctx, noreturn);
                    if *noreturn { return Res::Val(Ref::UNDEF) }
                    ir.build_not(val, ty)
                }
                UnOp::Ref => {
                    let IrType::Ptr(ty) = ir.types[ctx[expr]] else { int!() };
                    let val = gen_expr(ir, val, ctx, noreturn);
                    if *noreturn { return Res::Val(Ref::UNDEF) }
                    match val {
                        Res::Val(r) => {
                            let temp = ir.build_decl(ty);
                            ir.build_store(temp, r);
                            temp
                        }
                        Res::Var(r) => r,
                        Res::Hole => int!(),
                    }
                }
                UnOp::Deref => {
                    let r = val_expr(ir, val, ctx, noreturn);
                    return Res::Var(r);
                }
            }
        }
        &Expr::BinOp(op, l, r) => {
            if let Operator::Assignment(assign) = op {
                let rval = val_expr(ir, r, ctx, noreturn);
                if *noreturn { return Res::Val(Ref::UNDEF) }

                // TODO: special assign lval expr here? Doesn't support patterns but also not exprs
                let lval = gen_expr(ir, l, ctx, noreturn);
                let var = match lval {
                    Res::Val(_) => int!(),
                    Res::Var(v) => v,
                    Res::Hole => {
                        return Res::Val(Ref::UNIT);
                    }
                };
                let op = match assign {
                    AssignType::Assign => {
                        ir.build_store(var, rval);
                        return Res::Val(Ref::UNIT);
                    }
                    AssignType::AddAssign => BinOp::Add,
                    AssignType::SubAssign => BinOp::Sub,
                    AssignType::MulAssign => BinOp::Mul,
                    AssignType::DivAssign => BinOp::Div,
                    AssignType::ModAssign => BinOp::Mod,
                };
                let ty = ctx[r];
                let loaded = ir.build_load(var, ty);
                let val = ir.build_bin_op(op, loaded, rval, ty);
                ir.build_store(var, val);
                Ref::UNIT
            } else {
                let ty = ctx[expr];
                let op = match op {
                    Operator::Add => BinOp::Add,
                    Operator::Sub => BinOp::Sub,
                    Operator::Mul => BinOp::Mul,
                    Operator::Div => BinOp::Div,
                    Operator::Mod => BinOp::Mod,
                    
                    Operator::Or => BinOp::Or,
                    Operator::And => BinOp::And,
                    
                    Operator::Equals | Operator::NotEquals
                        if ir.types[ctx[l]].is_id(ctx.symbols.builtins.str_ty())
                    => {
                        let l_val = val_expr(ir, l, ctx, noreturn);
                        if *noreturn { return Res::Val(Ref::UNDEF) }
                        let r_val = val_expr(ir, r, ctx, noreturn);
                        if *noreturn { return Res::Val(Ref::UNDEF) }

                        let str_eq = ctx.functions.get(
                            ctx.symbols.builtins.str_eq(),
                            ctx.symbols,
                            vec![],
                            ir.create_reason(),
                        );
                        let eq = ir.build_call(str_eq, [l_val, r_val], ty);
                        return Res::Val(match op {
                            Operator::Equals => eq,
                            Operator::NotEquals => ir.build_not(eq, ty),
                            _ => unreachable!(),
                        });
                    }
                    Operator::Equals | Operator::NotEquals
                        if matches!(ir.types[ctx[l]], IrType::Enum(_))
                    => {
                        let l_val = gen_expr(ir, l, ctx, noreturn);
                        if *noreturn { return Res::Val(Ref::UNDEF) }
                        let r_val = gen_expr(ir, r, ctx, noreturn);
                        if *noreturn { return Res::Val(Ref::UNDEF) }

                        let IrType::Enum(variants) = ir.types[ctx[l]] else { unreachable!() };
                        for variant in variants.iter() {
                            let IrType::Tuple(args) = ir.types[variant] else { int!() };
                            if args.len() != 0 {
                                todo!("comparing implicit enums with variants is unsupported right now, \
                                    use match instead");
                            };
                        }
                        if let Some(tag_int_ty) = Enum::int_ty_from_variant_count(variants.count) {
                            let tag_ty = ir.types.add(IrType::Primitive(tag_int_ty.into()));
                            let mut get_tag = |val| match val {
                                Res::Val(r) => ir.build_enum_value_tag(r, tag_ty),
                                Res::Var(r) => {
                                    let tag_ptr_ty = ir.types.add(IrType::Ptr(tag_ty));
                                    let tag_ptr = ir.build_enum_tag(r, tag_ptr_ty);
                                    ir.build_load(tag_ptr, tag_ty)
                                }
                                Res::Hole => int!()
                            };
                            let l_tag = get_tag(l_val);
                            let r_tag = get_tag(r_val);
                            let op = match op {
                                Operator::Equals => BinOp::Eq,
                                Operator::NotEquals => BinOp::NE,
                                _ => unreachable!()
                            };
                            return Res::Val(ir.build_bin_op(op, l_tag, r_tag, ty));
                        }
                        todo!()
                    }
                    Operator::Equals => {
                        BinOp::Eq
                    }
                    Operator::NotEquals => BinOp::NE,
                    
                    Operator::LT => BinOp::LT,
                    Operator::GT => BinOp::GT,
                    Operator::LE => BinOp::LE,
                    Operator::GE => BinOp::GE,
                    Operator::Range | Operator::RangeExclusive => {
                        todo!("range expressions")
                    }
                    
                    Operator::Assignment(_) => int!(),
                };

                let l_val = val_expr(ir, l, ctx, noreturn);
                if *noreturn { return Res::Val(Ref::UNDEF) }
                let r_val = val_expr(ir, r, ctx, noreturn);
                if *noreturn { return Res::Val(Ref::UNDEF) }

                ir.build_bin_op(op, l_val, r_val, ty)
            }
        }
        &Expr::MemberAccess { left, name: _, id } => {
            fn layout_val(ir: &mut IrBuilder, val: u64) -> Ref {
                let ty = ir.types.add(IrType::Primitive(Primitive::U64));
                ir.build_int(val, ty)
            }
            match ctx[id] {
                MemberAccess::Size(id) => {
                    let layout = ctx.symbols.get_type(id).layout(
                        |id| ctx.symbols.get_type(id),
                        &[]
                    );
                    layout_val(ir, layout.size)
                }
                MemberAccess::Align(id) => {
                    let layout = ctx.symbols.get_type(id).layout(
                        |id| ctx.symbols.get_type(id),
                        &[]
                    );
                    layout_val(ir, layout.alignment)
                }
                MemberAccess::Stride(id) => {
                    let layout = ctx.symbols.get_type(id).layout(
                        |id| ctx.symbols.get_type(id),
                        &[]
                    );
                    layout_val(ir, layout.stride())
                }
                MemberAccess::LocalSize(idx) => {
                    let layout = ir.types.layout(ir.types[idx], |id| ctx.symbols.get_type(id));
                    layout_val(ir, layout.size)
                }
                MemberAccess::LocalAlign(idx) => {
                    let layout = ir.types.layout(ir.types[idx], |id| ctx.symbols.get_type(id));
                    layout_val(ir, layout.alignment)
                }
                MemberAccess::LocalStride(idx) => {
                    let layout = ir.types.layout(ir.types[idx], |id| ctx.symbols.get_type(id));
                    layout_val(ir, layout.stride())
                }
                MemberAccess::StructMember(member_idx) => {
                    let mut member_ty = ir.types[ctx[left]];
                    let mut l_ptr_count = 0u32;
                    let (id, generics) = loop {
                        match member_ty {
                            IrType::Ptr(pointee) => {
                                l_ptr_count += 1;
                                member_ty = ir.types[pointee];
                            }
                            IrType::Id(id, generics) => break (id, generics),
                            _ => int!()
                        }
                    };
                    let mut left = match gen_expr(ir, left, ctx, noreturn) {
                        Res::Val(v) => v,
                        Res::Var(v) => {
                            l_ptr_count += 1;
                            v
                        }
                        Res::Hole => int!()
                    };

                    if *noreturn { return Res::Val(Ref::UNDEF) }

                    if l_ptr_count == 0 {
                        return Res::Val(ir.build_value(left, member_idx, ctx[expr]))
                    }
                    let mut ptr_ty = ir.types.add(IrType::Id(id, generics));
                    for _ in 0..l_ptr_count {
                        ptr_ty = ir.types.add(IrType::Ptr(ptr_ty));
                    }
                    while l_ptr_count > 1 {
                        let IrType::Ptr(loaded_ty) = ir.types[ptr_ty] else { unreachable!() };
                        left = ir.build_load(left, loaded_ty);
                        ptr_ty = loaded_ty;
                        l_ptr_count -= 1;
                    }

                    let member_ptr_ty = ir.types.add(IrType::Ptr(ctx[expr]));
                    return Res::Var(ir.build_member_int(left, member_idx, member_ptr_ty));
                }
                MemberAccess::Symbol(_) | MemberAccess::Method(_) => Ref::UNDEF,
                MemberAccess::EnumItem(id, variant) => {
                    let ResolvedTypeBody::Enum(def) = &ctx.symbols.get_type(id).body else { int!() };
                    let int_ty = ir.types.add(IrType::Primitive(def.int_ty().map_or(Primitive::Unit, Into::into)));
                    ir.build_int(variant as u64, int_ty)
                }
                MemberAccess::Invalid => todo!(),
            }
        }
        &Expr::Index { expr: val, idx, .. } => {
            let res = gen_expr(ir, val, ctx, noreturn);
            if *noreturn { return Res::Val(Ref::UNDEF) }
            let var = res.var(ir, ctx[val]);

            let member = val_expr(ir, idx, ctx, noreturn);
            if *noreturn { return Res::Val(Ref::UNDEF) }

            let ty = ir.types.add(IrType::Ptr(ctx[expr]));
            return Res::Var(ir.build_member(var, member, ty));
        }
        &Expr::TupleIdx { expr: val, idx, .. } => {
            let res = gen_expr(ir, val, ctx, noreturn);
            if *noreturn { return Res::Val(Ref::UNDEF) }


            let member_ty = ctx[expr];
            match res {
                Res::Val(r) => ir.build_value(r, idx, member_ty),
                Res::Var(r) => {
                    let pointer_ty = ir.types.add(IrType::Ptr(member_ty));
                    return Res::Var(ir.build_member_int(r, idx, pointer_ty))
                }
                Res::Hole => int!(),
            }

        }
        Expr::Cast(_, _, val) => {
            let val = val_expr(ir, *val, ctx, noreturn);
            if *noreturn { return Res::Val(Ref::UNDEF) }

            // let from_ty = ctx[val];
            let target_ty = ctx[expr];

            // TODO: handle cast here instead of in the backend?
            ir.build_cast(val, target_ty)

        }
        Expr::Root(_) => int!(),
        Expr::Asm { .. } => todo!("inline asm codegen"),
    };
    Res::Val(r)
}

fn string_literal(ir: &mut IrBuilder, span: TSpan, ctx: &mut Ctx) -> Ref {
    // PERF a little suboptimal
    let lit = ctx.src()[span.start as usize + 1 .. span.end as usize]
        .replace("\\n", "\n")
        .replace("\\t", "\t")
        .replace("\\r", "\r")
        .replace("\\0", "\0")
        .replace("\\\"", "\"");

    let i8_ty = ir.types.add(IrType::Primitive(Primitive::I8));
    let i8_ptr_ty = ir.types.add(IrType::Ptr(i8_ty));
    let i8_ptr_ptr_ty = ir.types.add(IrType::Ptr(i8_ptr_ty));

    let u64_ty = ir.types.add(IrType::Primitive(Primitive::U64));
    let u64_ptr_ty = ir.types.add(IrType::Ptr(u64_ty));

    let ptr = ir.build_string(lit.as_bytes(), true, i8_ptr_ty);
    let len = ir.build_int(lit.len() as u64, u64_ty);
    
    let str_struct = ir.build_decl(ctx.symbols.builtins.str_ir_ty());
    
    let ptr_ref = ir.build_member_int(str_struct, 0, i8_ptr_ptr_ty);
    ir.build_store(ptr_ref, ptr);
    
    let len_ref = ir.build_member_int(str_struct, 1, u64_ptr_ty);
    ir.build_store(len_ref, len);
    return str_struct
}

fn gen_pat(
    ir: &mut IrBuilder,
    pat: ExprRef,
    pat_val: Ref,
    ty: TypeRef,
    on_mismatch: &mut impl FnMut(&mut IrBuilder) -> Option<BlockIndex>,
    bool_ty: TypeRef,
    ctx: &mut Ctx
) {
    let mut cond_match = |ir: &mut IrBuilder, cond: Ref| {
        match on_mismatch(ir) {
            Some(on_mismatch) => {
                let on_match = ir.create_block();
                ir.build_branch(cond, on_match, on_mismatch);
                ir.begin_block(on_match);
            }
            None => {}
        }
    };
    match &ctx.ast[pat] {
        Expr::IntLiteral(lit) => {
            let lit = IntLiteral::parse(&ctx.src()[lit.range()]);
            let int_val = int_literal(lit, ty, ir);
            let eq = ir.build_bin_op(BinOp::Eq, pat_val, int_val, bool_ty);
            cond_match(ir, eq)
        }
        Expr::UnOp(_, UnOp::Neg, val) => {
            let val = &ctx.ast[*val];
            match val {
                Expr::IntLiteral(lit_span) => {
                    let lit = IntLiteral::parse(ctx.src_at(*lit_span));
                    let val = int_literal(lit, ty, ir);
                    let val = ir.build_neg(val, ty);
                    let eq = ir.build_bin_op(BinOp::Eq, pat_val, val, bool_ty);
                    cond_match(ir, eq)
                }
                Expr::FloatLiteral(_) => todo!(),
                _ => int!()
            }
        }
        Expr::FloatLiteral(_) => todo!(),
        Expr::BoolLiteral { val, .. } => if *val {
            cond_match(ir, pat_val);
        } else {
            let negated_val = ir.build_neg(pat_val, bool_ty);
            cond_match(ir, negated_val);
        }
        Expr::EnumLiteral { ident, args, .. } => {
            let name = ctx.src_at(*ident);
            let (variant_id, tag, tag_ty, arg_types) = match ir.inferred_types[ty] {
                TypeInfo::Enum(variants) => {
                    let (pos, (_, types)) = ir.inferred_types.get_enum_variants(variants)
                        .iter()
                        .enumerate()
                        .find(|(_, (other_name, _))| other_name.as_str() == name)
                        .unwrap();
                    (
                        VariantId::new(pos as u16),
                        pos as u64,
                        Enum::int_ty_from_variant_count(variants.count()),
                        *types,
                    )
                }
                TypeInfo::Resolved(id, generics) => {
                    let ResolvedTypeBody::Enum(def) = &ctx.symbols.get_type(id).body else { int!() };
                    let variant = def.variants.get(name).unwrap();
                    let types = ir.types.add_multiple(
                        (0..variant.2.len()).map(|_| IrType::Primitive(Primitive::Never))
                    );
                    for (i, ty) in variant.2.iter().enumerate() {
                        let ty = ir.types.from_resolved(ty, generics);
                        ir.types.replace(types.nth(i as u32), ty);
                    }
                    (
                        variant.0,
                        variant.1 as u64,
                        Enum::int_ty_from_variant_count(def.variants.len() as _),
                        types,
                    )
                }
                _ => int!()
            };
            let tag_matches = if let Some(tag_ty) = tag_ty {
                let tag_ty = IrType::Primitive(Primitive::from(tag_ty));
                let i = ir.build_int(tag, tag_ty);
                let tag_val = ir.build_enum_value_tag(pat_val, tag_ty);
                ir.build_bin_op(BinOp::Eq, tag_val, i, bool_ty)
            } else {
                // single-variant enum without arguments always matches
                if args.count == 0 { return };
                Ref::val(RefVal::True)
            };
            if args.count != 0 {
                debug_assert_eq!(ctx.ast[*args].len(), arg_types.len());
                // We duplicate some code here but that is fine since it saves potentially calling on_mismatch
                // when it isn't needed. That happens when the enum has a single variants and all
                // args match trivially.
                if tag_matches == Ref::val(RefVal::True) {
                    for ((i, arg), arg_ty) in ctx.ast[*args].iter().copied().enumerate().zip(arg_types.iter()) {
                        let arg_val = ir.build_enum_value_variant_member(pat_val, variant_id, i as u16, arg_ty);
                        gen_pat(ir, arg, arg_val, arg_ty, on_mismatch, bool_ty, ctx);
                    }
                } else {
                    if let Some(on_mismatch_branch) = on_mismatch(ir) {
                        let on_tag_match = ir.create_block();
                        ir.build_branch(tag_matches, on_tag_match, on_mismatch_branch);
                        ir.begin_block(on_tag_match);
                    }

                    for ((i, arg), arg_ty) in ctx.ast[*args].iter().copied().enumerate().zip(arg_types.iter()) {
                        let arg_val = ir.build_enum_value_variant_member(pat_val, variant_id, i as u16, arg_ty);
                        gen_pat(ir, arg, arg_val, arg_ty, on_mismatch, bool_ty, ctx);
                    }
                }
            } else {
                if let Some(on_mismatch) = on_mismatch(ir) {
                    let on_match = ir.create_block();
                    ir.build_branch(tag_matches, on_match, on_mismatch);
                    ir.begin_block(on_match);
                }
            }
        }
        Expr::StringLiteral(span) => {
            let lit = string_literal(ir, *span, ctx);
            let str_ty = ir.types.add(IrType::Id(ctx.symbols.builtins.str_ty(), TypeRefs::EMPTY));
            let lit_val = ir.build_load(lit,  str_ty);
            let str_eq = ctx.functions.get(ctx.symbols.builtins.str_eq(), ctx.symbols, vec![], ir.create_reason());
            let eq = ir.build_call(str_eq, [pat_val, lit_val], bool_ty);
            cond_match(ir, eq);
        }
        Expr::Nested(_, inner) => gen_pat(ir, *inner, pat_val, ty, on_mismatch, bool_ty, ctx),
        Expr::Unit(_) | Expr::Hole(_) => {}
        Expr::Variable { id, .. } => {
            match ctx.idents[id.idx()] {
                resolve::Ident::Invalid => int!(),
                resolve::Ident::Var(var_id) => {
                    let var = ir.build_decl(ty);
                    ir.build_store(var, pat_val);
                    ctx.var_refs[var_id.idx()] = var;
                }
                resolve::Ident::Global(_) => int!("global in pattern"),
                resolve::Ident::Function(_) => int!("function in pattern"),
                resolve::Ident::Module(_) => int!("module in pattern"),
                resolve::Ident::Type(_) => int!("type in pattern"),
                resolve::Ident::Const(id) => {
                    let val = ctx.symbols.get_const(id);
                    let val = const_val::build(ir, val, ty).val(ir, ty);
                    let eq = ir.build_bin_op(BinOp::Eq, pat_val, val, bool_ty);
                    cond_match(ir, eq)
                }
            }
        }
        &Expr::BinOp(op @ (Operator::Range | Operator::RangeExclusive), l, r) => {
            let mut side = |expr| match ctx.ast[expr] {
                Expr::IntLiteral(span) => {
                    let lit = IntLiteral::parse(ctx.src_at(span));
                    int_literal(lit, ty, ir)
                }
                Expr::FloatLiteral(span) => {
                    let lit = FloatLiteral::parse(ctx.src_at(span));
                    ir.build_float(lit.val, ty)
                }
                Expr::UnOp(_, UnOp::Neg, inner) if let Expr::IntLiteral(span) = ctx.ast[inner] => {
                    let lit = IntLiteral::parse(ctx.src_at(span));
                    int_literal(lit, ty, ir)
                }
                Expr::UnOp(_, UnOp::Neg, inner) if let Expr::FloatLiteral(span) = ctx.ast[inner] => {
                    let lit = FloatLiteral::parse(ctx.src_at(span));
                    ir.build_float(-lit.val, ty)
                }
                _ => int!()
            };
            let l = side(l);
            let r = side(r);

            
            let left_check = ir.build_bin_op(BinOp::GE, pat_val, l, bool_ty);
            let right_op = if op == Operator::RangeExclusive { BinOp::LT } else { BinOp::LE };
            let right_check = ir.build_bin_op(right_op, pat_val, r, bool_ty);

            // PERF: Is 'And' more efficient than branching twice? Probably doesn't matter much.
            let eq = ir.build_bin_op(BinOp::And, left_check, right_check, bool_ty);
            cond_match(ir, eq);
        }
        Expr::Tuple(_, items) => {
            let IrType::Tuple(types) = ir.types[ty] else { int!() };
            for (i, (item, item_ty)) in ctx.ast[*items].iter().zip(types.iter()).enumerate() {
                let item_val = ir.build_value(pat_val, i as u32, item_ty);
                gen_pat(ir, *item, item_val, item_ty, on_mismatch, bool_ty, ctx);
            }
        }

        Expr::Record { .. } // very useful to match on records
            | Expr::Block { .. }
            | Expr::Declare { .. }
            | Expr::DeclareWithVal { .. }
            | Expr::Return { .. }
            | Expr::ReturnUnit { .. }
            | Expr::Array(_, _)
            | Expr::If { .. } 
            | Expr::IfPat { .. }
            | Expr::IfElse { .. } 
            | Expr::IfPatElse { .. }
            | Expr::Match { .. } 
            | Expr::While { .. } 
            | Expr::WhilePat { .. }
            | Expr::FunctionCall { .. } 
            | Expr::UnOp(_, _, _) 
            | Expr::BinOp(_, _, _) 
            | Expr::MemberAccess { .. } // maybe when variables are allowed. Also qualified enum variants!
            | Expr::Index { .. } 
            | Expr::TupleIdx { .. } 
            | Expr::Cast(_, _, _)
            | Expr::Root(_) 
            | Expr::Asm { .. } 
            => int!(),
    }
}

fn build_then_else(
    ir: &mut IrBuilder, ctx: &mut Ctx, noreturn: &mut bool,
    ty: TypeRef, then: ExprRef, else_: ExprRef, else_block: BlockIndex
) -> Ref {
    let mut then_noreturn = false;
    let then_val = val_expr(ir, then, ctx, &mut then_noreturn);
    let then_exit = ir.current_block();

    let mut after_block = None;
    let mut goto_after = |ir: &mut IrBuilder| {
        let after = if let Some(after_block) = after_block {
            after_block
        } else {
            let after = ir.create_block();
            after_block = Some(after);
            after
        };
        ir.build_goto(after);
    };

    if !then_noreturn {
        goto_after(ir);
    }

    ir.begin_block(else_block);
    let mut else_noreturn = false;
    let else_val = val_expr(ir, else_, ctx, &mut else_noreturn);
    let else_exit = ir.current_block();

    // if else returns but then doesn't we can just skip the goto to after_block
    if !else_noreturn  && !then_noreturn {
        goto_after(ir);
    }
    
    if let Some(after_block) = after_block {
        ir.begin_block(after_block);
    }
    if then_noreturn && else_noreturn {
        *noreturn = true;
        Ref::UNDEF
    } else if then_noreturn {
        else_val
    } else if else_noreturn {
        then_val
    } else {
        if matches!(ir.types[ty], IrType::Primitive(Primitive::Unit)) {
            Ref::UNIT
        } else {
            ir.build_phi([(then_exit, then_val), (else_exit, else_val)], ty)
        }
    }
}
fn build_while_loop(
    ir: &mut IrBuilder, ctx: &mut Ctx, noreturn: &mut bool,
    body: ExprRef,
    build_cond: impl Fn(&mut IrBuilder, &mut Ctx, &mut bool, BlockIndex),
) -> Ref {
    let cond_block = ir.create_block();
    let after_block = ir.create_block();
    ir.build_goto(cond_block);

    ir.begin_block(cond_block);
    build_cond(ir, ctx, noreturn, after_block);
    if *noreturn { return Ref::UNDEF }
    let mut body_noreturn = false;
    gen_expr(ir, body, ctx, &mut body_noreturn);
    if !body_noreturn {
        ir.build_goto(cond_block);
    }
    ir.begin_block(after_block);
    Ref::UNIT
}

fn int_literal(lit: IntLiteral, ty: impl Into<IdxOrTy>, ir: &mut IrBuilder) -> Ref {
    // TODO: check int type for overflow
    if lit.val <= std::u64::MAX as u128 {
        ir.build_int(lit.val as u64, ty)
    } else {
        ir.build_large_int(lit.val, ty)
    }
}

