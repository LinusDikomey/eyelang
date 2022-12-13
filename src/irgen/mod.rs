use std::ops::Index;

use crate::{
    ast::{Ast, ExprRef, Expr, ModuleId, FunctionId, UnOp, ExprExtra, MemberAccessId},
    resolve::{
        types::{SymbolTable, MaybeTypeDef, ResolvedTypeDef, Type, ResolvedFunc, Enum},
        self,
        type_info::TypeInfo, VarId, MemberAccess},
    ir::{self, Function, builder::{IrBuilder, BinOp, IrTypeTable, IdxOrTy}, Ref, RefVal, types::{IrType, TypeRef, TypeRefs}},
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
            &generic_instance
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
    generics: &[Type]
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
    let mut builder = IrBuilder::new(ir_types, &body.types);

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
        module: module,
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
    pub fn val<IrTypes: IrTypeTable>(self, ir: &mut IrBuilder<IrTypes>, ty: TypeRef) -> Ref {
        match self {
            Res::Val(r) => r,
            Res::Var(r) => ir.build_load(r, ty),
            Res::Hole => int!(),
        }
    }

    pub fn var<IrTypes: IrTypeTable>(self, ir: &mut IrBuilder<IrTypes>, ty: TypeRef) -> Ref {
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

fn val_expr<IrTypes: IrTypeTable>(ir: &mut IrBuilder<IrTypes>, expr: ExprRef, ctx: &mut Ctx, noreturn: &mut bool) -> Ref {
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

pub fn gen_expr<IrTypes: IrTypeTable>(ir: &mut IrBuilder<IrTypes>, expr: ExprRef, ctx: &mut Ctx, noreturn: &mut bool) -> Res {
    debug_assert_eq!(*noreturn, false, "generating expression with noreturn enabled means dead code will be generated");
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
            gen_pat(ir, *pat, Ref::UNDEF, ty, bool_ty, ctx);
            Ref::UNIT
        }
        Expr::DeclareWithVal { pat, val, .. } => {
            let ty = ctx[*pat];
            let bool_ty = ir.types.add(IrType::Primitive(Primitive::Bool));
            let val = val_expr(ir, *val, ctx, noreturn);
            if ! *noreturn {
                gen_pat(ir, *pat, val, ty, bool_ty, ctx);
            }
            Ref::UNIT
        }
        Expr::Return { val, .. } => {
            let zero_sized = ir.types.layout(&ir.types[ctx[*val]], |id| ctx.symbols.get_type(id)).size == 0;

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
        Expr::FloatLiteral(span) => {
            let lit = FloatLiteral::parse(&ctx.src()[span.range()]);
            let ty = ctx[expr];
            ir.build_float(lit.val, ty)
        }
        Expr::StringLiteral(span) => {
            return Res::Var(string_literal(ir, *span, ctx));
        }
        Expr::BoolLiteral { val, .. } => if *val { Ref::val(RefVal::True) } else { Ref::val(RefVal::False) }
        &Expr::EnumLiteral { ident, .. } => {
            let name = ctx.src_at(ident);
            // TODO: enums with args
            let (variant, int_ty) = match ir.inferred_types[ctx[expr]] {
                TypeInfo::Resolved(id, _generics) => {
                    let ResolvedTypeDef::Enum(def) = ctx.symbols.get_type(id) else { int!() };
                    (def.variants[name].0, def.int_ty())
                }
                TypeInfo::Enum(variants) => {
                    let variants = ir.inferred_types.get_enum_variants(variants);
                    let variant = variants
                        .iter()
                        .enumerate()
                        .find(|(_, (s, _))| s.as_str() == name)
                        .unwrap()
                        .0 as u32;

                    (variant, Enum::int_ty_from_variant_count(variants.len() as u32))

                }
                _ => int!()
            };
            if let Some(int_ty) = int_ty {
                let ty = ir.types.add(IrType::Primitive(int_ty.into()));
                ir.build_int(variant as u64, ty)
            } else {
                // type only has one variant and is reduced to unit
                Ref::UNIT
            }
        }
        Expr::Record { .. } => todo!(),
        Expr::Nested(_, inner) => return gen_expr(ir, *inner, ctx, noreturn),
        Expr::Unit(_) => Ref::UNIT,
        Expr::Variable { id, .. } => {
            match ctx.idents[id.idx()] {
                resolve::Ident::Invalid => int!(),
                resolve::Ident::Var(var_id) => return Res::Var(ctx.var_refs[var_id.idx()]),
                resolve::Ident::Global(global_id) => {
                    let ty = &ctx.symbols.get_global(global_id).1;
                    let ty = ir.types.from_resolved(ty, TypeRefs::EMPTY);
                    let ty = ir.types.add(ty);
                    let ptr_ty = ir.types.add(IrType::Ptr(ty));
                    return Res::Var(ir.build_global(global_id, ptr_ty))
                }
                resolve::Ident::Const(const_id) => {
                    let val = ctx.symbols.get_const(const_id);

                    return const_val::build(ir, val, ctx[expr]);
                }
            }
        }
        Expr::Hole(_) => return Res::Hole,
        &Expr::Array(_, values) => {
            let array_var = ir.build_decl(ctx[expr]);
            let Some(IrType::Array(member_ty, _)) = ir.types.get_ir_type(ctx[expr]) else { int!() };
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
        &Expr::IfElse { cond, then, else_, .. } => {
            let cond = val_expr(ir, cond, ctx, noreturn);
            if *noreturn { return Res::Val(Ref::UNDEF) }
            
            let then_block = ir.create_block();
            let else_block = ir.create_block();
            let after_block = ir.create_block();

            ir.build_branch(cond, then_block, else_block);
            
            ir.begin_block(then_block);
            let mut then_noreturn = false;
            let then_val = val_expr(ir, then, ctx, &mut then_noreturn);
            let then_exit = ir.current_block();

            if !then_noreturn {
                ir.build_goto(after_block);
            }

            ir.begin_block(else_block);
            let mut else_noreturn = false;
            let else_val = val_expr(ir, else_, ctx, &mut else_noreturn);
            let else_exit = ir.current_block();

            if !else_noreturn {
                ir.build_goto(after_block);
            }

            ir.begin_block(after_block);
            
            if then_noreturn && else_noreturn {
                *noreturn = true;
                Ref::UNDEF
            } else if then_noreturn {
                else_val
            } else if else_noreturn {
                then_val
            } else {
                let ty = ctx[expr];
                ir.build_phi([(then_exit, then_val), (else_exit, else_val)], ty)
            }
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
                let matches = gen_pat(ir, *pat, matched, ctx[val], bool_ty, ctx);

                if let Some(RefVal::False) = matches.into_val() {
                    // branch never matches, do nothing
                } else if let Some(RefVal::True) = matches.into_val() {
                    let mut branch_noreturn = false;    
                    let branch_val = val_expr(ir, *branch, ctx, &mut branch_noreturn);
                    all_noreturn &= branch_noreturn;
                    
                    if !branch_noreturn {
                        ir.build_goto(after_block);
                        phi_vals.push((ir.current_block(), branch_val));
                    }
                    break; // branches after this won't be reached as this branch always matches
                } else {
                    let next_block = if i as u32 == branch_count - 1 {
                        None
                    } else {
                        let on_match = ir.create_block();
                        let next = ir.create_block();
                        ir.build_branch(matches, on_match, next);
                        ir.begin_block(on_match);
                        Some(next)
                    };
                
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
            let cond_block = ir.create_block();
            let body_block = ir.create_block();
            let after_block = ir.create_block();
            
            ir.build_goto(cond_block);
            
            ir.begin_block(cond_block);
            let cond = val_expr(ir, cond, ctx, noreturn);
            ir.build_branch(cond, body_block, after_block);
            
            ir.begin_block(body_block);
            let mut body_noreturn = false;
            gen_expr(ir, body, ctx, &mut body_noreturn);
            if !body_noreturn {
                ir.build_goto(cond_block);
            }
            ir.begin_block(after_block);

            Ref::UNIT
        }
        Expr::FunctionCall(call_id) => {
            let call = &ctx.ast.calls[call_id.idx()];
            match &ctx.symbols.calls[call_id.idx()].unwrap() {
                resolve::ResolvedCall::Function { func_id, generics } => {
                    let func = ctx.symbols.get_func(*func_id);

                    let this_arg = if let TypeInfo::MethodItem { this_ty, .. } = ir.inferred_types.get(ctx[call.called_expr]) {
                        let mut ptr_count = 0u32;
                        let mut current_ty = this_ty;
                        
                        while let Some(IrType::Ptr(pointee)) = ir.types.get_ir_type(current_ty) {
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
                                let Some(IrType::Ptr(pointee)) = ir.types.get_ir_type(loaded_ty) else { int!() };
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
                        .map(|idx| ir.types
                            .get_ir_type(idx)
                            .unwrap()
                            .as_resolved_type(&ir.types)
                            .unwrap()
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
                    let ResolvedTypeDef::Struct(def) = ctx.symbols.get_type(*type_id) else { int!() };
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
                    let Some(IrType::Ptr(ty)) = ir.types.get_ir_type(ctx[expr]) else { int!() };
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
                let l = val_expr(ir, l, ctx, noreturn);
                if *noreturn { return Res::Val(Ref::UNDEF) }
                let r = val_expr(ir, r, ctx, noreturn);
                if *noreturn { return Res::Val(Ref::UNDEF) }
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
                    
                    Operator::Assignment(_) => int!(),
                };

                let ty = ctx[expr];
                ir.build_bin_op(op, l, r, ty)
            }
        }
        &Expr::MemberAccess { left, name: _, id } => {
            fn layout_val<IrTypes: IrTypeTable>(ir: &mut IrBuilder<IrTypes>, val: u64) -> Ref {
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
                MemberAccess::LocalSize(idx) => {
                    let layout = ir.types.layout(&ir.types[idx], |id| ctx.symbols.get_type(id));
                    layout_val(ir, layout.size)
                }
                MemberAccess::LocalAlign(idx) => {
                    let layout = ir.types.layout(&ir.types[idx], |id| ctx.symbols.get_type(id));
                    layout_val(ir, layout.alignment)
                }
                MemberAccess::StructMember(member_idx) => {
                    let mut member_ty = ir.types.get_ir_type(ctx[left]);
                    let mut l_ptr_count = 0u32;
                    let (id, generics) = loop {
                        match member_ty {
                            Some(IrType::Ptr(pointee)) => {
                                l_ptr_count += 1;
                                member_ty = ir.types.get_ir_type(pointee);
                            }
                            Some(IrType::Id(id, generics)) => break (id, generics),
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
                        let Some(IrType::Ptr(loaded_ty)) = ir.types.get_ir_type(ptr_ty) else { unreachable!() };
                        left = ir.build_load(left, loaded_ty);
                        ptr_ty = loaded_ty;
                        l_ptr_count -= 1;
                    }

                    let member_ptr_ty = ir.types.add(IrType::Ptr(ctx[expr]));
                    return Res::Var(ir.build_member_int(left, member_idx, member_ptr_ty));
                }
                MemberAccess::Symbol(_) | MemberAccess::Method(_) => Ref::UNDEF,
                MemberAccess::EnumItem(id, variant) => {
                    let ResolvedTypeDef::Enum(def) = ctx.symbols.get_type(id) else { int!() };
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

fn string_literal<IrTypes: IrTypeTable>(ir: &mut IrBuilder<IrTypes>, span: TSpan, ctx: &mut Ctx) -> Ref {
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
    
    let str_struct = ir.build_decl(ctx.symbols.builtins.str_ty());
    
    let ptr_ref = ir.build_member_int(str_struct, 0, i8_ptr_ptr_ty);
    ir.build_store(ptr_ref, ptr);
    
    let len_ref = ir.build_member_int(str_struct, 1, u64_ptr_ty);
    ir.build_store(len_ref, len);
    return str_struct
}

fn gen_pat<IrTypes: IrTypeTable>(
    ir: &mut IrBuilder<IrTypes>,
    pat: ExprRef,
    pat_val: Ref,
    ty: TypeRef,
    bool_ty: TypeRef,
    ctx: &mut Ctx
) -> Ref {
    match &ctx.ast[pat] {
        Expr::IntLiteral(lit) => {
            let lit = IntLiteral::parse(&ctx.src()[lit.range()]);
            let int_val = int_literal(lit, ty, ir);
            ir.build_bin_op(BinOp::Eq, pat_val, int_val, bool_ty)
        }
        Expr::UnOp(_, UnOp::Neg, val) => {
            let val = &ctx.ast[*val];
            match val {
                Expr::IntLiteral(lit_span) => {
                    let lit = IntLiteral::parse(ctx.src_at(*lit_span));
                    let val = int_literal(lit, ty, ir);
                    let val = ir.build_neg(val, ty);
                    ir.build_bin_op(BinOp::Eq, pat_val, val, bool_ty)
                }
                Expr::FloatLiteral(_) => todo!(),
                _ => int!()
            }
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
        Expr::EnumLiteral { ident, args, .. } => {
            let name = ctx.src_at(*ident);
            let ordinal = match ir.inferred_types[ty] {
                TypeInfo::Enum(variants) => (variants.count() > 1).then(|| ir.inferred_types.get_enum_variants(variants)
                    .iter()
                    .enumerate()
                    .find(|(_, (other_name, _))| other_name.as_str() == name)
                    .unwrap()
                    .0 as u64
                ),
                TypeInfo::Resolved(id, _generics) => {
                    let ResolvedTypeDef::Enum(def) = ctx.symbols.get_type(id) else { int!() };
                    // TODO: enums with args
                    (def.variants.len() > 1).then(|| def.variants.get(name).unwrap().0 as u64)
                }
                _ => int!()
            };
            if let Some(ordinal) = ordinal {
                let i = ir.build_int(ordinal, ty);
                ir.build_bin_op(BinOp::Eq, pat_val, i, bool_ty)
            } else {
                Ref::val(RefVal::True)
            }
        }
        Expr::StringLiteral(span) => {
            let lit = string_literal(ir, *span, ctx);
            let str_ty = ir.types.add(IrType::Id(ctx.symbols.builtins.str_type, TypeRefs::EMPTY));
            let lit_val = ir.build_load(lit,  str_ty);
            let str_eq = ctx.functions.get(ctx.symbols.builtins.str_eq, ctx.symbols, vec![], IrTypes::CREATE_REASON);
            ir.build_call(str_eq, [pat_val, lit_val], bool_ty)
        }
        Expr::Nested(_, inner) => gen_pat(ir, *inner, pat_val, ty, bool_ty, ctx),
        Expr::Unit(_) => Ref::val(RefVal::True),
        Expr::Variable { id, .. } => {
            match ctx.idents[id.idx()] {
                resolve::Ident::Invalid => int!(),
                resolve::Ident::Var(var_id) => {
                    let var = ir.build_decl(ty);
                    ir.build_store(var, pat_val);
                    ctx.var_refs[var_id.idx()] = var;
                }
                resolve::Ident::Global(_) => int!("global in pattern"),
                resolve::Ident::Const(_) => int!("const in pattern"),
            }
            Ref::val(RefVal::True)
        }
        Expr::Hole(_) => Ref::val(RefVal::True),
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

            ir.build_bin_op(BinOp::And, left_check, right_check, bool_ty)
        }
        Expr::Tuple(_, items) => {
            let Some(IrType::Tuple(types)) = ir.types.get_ir_type(ty) else { int!() };
            let mut matches_bool = Ref::val(RefVal::True);
            for (i, (item, item_ty)) in ctx.ast[*items].iter().zip(types.iter()).enumerate() {
                let item_val = ir.build_value(pat_val, i as u32, item_ty);
                let item_matches = gen_pat(ir, *item, item_val, item_ty, bool_ty, ctx);
                matches_bool = ir.build_bin_op(BinOp::And, matches_bool, item_matches, item_ty);
            }
            matches_bool
        }

        Expr::Record { .. } // very useful to match on records
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
            => int!(),
    }
}

fn int_literal<IrTypes: IrTypeTable>(lit: IntLiteral, ty: impl Into<IdxOrTy>, ir: &mut IrBuilder<IrTypes>) -> Ref {
    // TODO: check int type for overflow
    if lit.val <= std::u64::MAX as u128 {
        ir.build_int(lit.val as u64, ty)
    } else {
        ir.build_large_int(lit.val, ty)
    }
}