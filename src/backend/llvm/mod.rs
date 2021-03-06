use llvm::{core::*, prelude::*, LLVMRealPredicate::*, LLVMIntPredicate::*, LLVMModule};
use crate::{dmap::{self, DHashMap}, ir::{self, Type}, types::Primitive, BackendStats};
use std::{ffi, ptr, ops::{Deref, DerefMut}, sync::atomic::Ordering, io::Write, time::Instant};

pub mod output;

pub struct Module(LLVMModuleRef);
impl Module {
    pub fn into_inner(self) -> LLVMModuleRef {
        let ptr = self.0;
        std::mem::forget(self);
        ptr
    }
}
impl Deref for Module {
    type Target = LLVMModule;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.0 }
    }
}
impl DerefMut for Module {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut*self.0 }
    }
}
impl Drop for Module {
    fn drop(&mut self) {
        crate::log!("Disposing Module...");
        unsafe { LLVMDisposeModule(self.0) };
        crate::log!("...disposed!");
    }
}


const FALSE: LLVMBool = 0;
const TRUE: LLVMBool = 1;
const NONE: *const i8 = "\0".as_ptr().cast();

pub unsafe fn module(ctx: LLVMContextRef, module: &ir::Module, print_ir: bool) -> (Module, BackendStats) {
    let start_time = Instant::now();
    // Set up the module
    let module_name = ffi::CString::new(module.name.as_bytes()).unwrap();
    let llvm_module = LLVMModuleCreateWithNameInContext(module_name.as_ptr(), ctx);
    
    let init_time = start_time.elapsed();

    // define types
    let start_time = Instant::now();


    let mut types = module.types.iter()
        .map(|(name, ty)| {
            match ty {
                ir::TypeDef::Struct(def) => {
                    if def.generic_count != 0 { return TypeInstance::Generic(dmap::new()); }
                    let name = ffi::CString::new(name.as_bytes()).unwrap();
                    TypeInstance::Simple(LLVMStructCreateNamed(ctx, name.as_ptr()))
                }
                ir::TypeDef::Enum(def) => {
                    if def.generic_count != 0 {
                        TypeInstance::Generic(dmap::new())
                    } else {
                        TypeInstance::Simple(int_from_variant_count(ctx, def.variants.len()))
                    }
                }
                ir::TypeDef::NotGenerated { .. } => unreachable!()
            }
        })
        .collect::<Vec<_>>();

    for (i, (_, ty)) in module.types.iter().enumerate() {
        let &TypeInstance::Simple(struct_ty) = &types[i] else { continue };
        match ty {
            ir::TypeDef::Struct(def) => {
                    if def.generic_count != 0 { continue }
                    let mut members = def.members.iter()
                        .map(|(_name, ty)| llvm_ty(ctx, module, &mut types, ty))
                        .collect::<Vec<_>>();
                    LLVMStructSetBody(struct_ty, members.as_mut_ptr(), members.len() as u32, FALSE);
            }
            ir::TypeDef::Enum(_) => continue, // nothing to do, just an int right now
            ir::TypeDef::NotGenerated { .. } => unreachable!()
        }
    }

    let type_creation_time = start_time.elapsed();

    // define function headers
    let start_time = Instant::now();

    let funcs = module.funcs.iter()
        .map(|func| {
            let ret = llvm_ty(ctx, module, &mut types, &func.header.return_type);
            let mut params = func.header.params.iter()
                .map(|(_name, ty)| llvm_ty(ctx, module, &mut types, ty))
                .collect::<Vec<_>>();
            
            let varargs = if func.header.varargs {TRUE} else {FALSE};
            let func_ty = LLVMFunctionType(ret, params.as_mut_ptr(), params.len() as u32, varargs);
            let name = ffi::CString::new(func.name.as_bytes()).unwrap();
            (LLVMAddFunction(llvm_module, name.as_ptr(), func_ty), func_ty)
        })
        .collect::<Vec<_>>();

    let func_header_time = start_time.elapsed();
    // set up a builder and build the function bodies
    let start_time = Instant::now();

    let builder = LLVMCreateBuilderInContext(ctx);
    
    let globals = module.globals.iter().map(|(name, ty, val)| {
        add_global(ctx, llvm_module, llvm_ty(ctx, module, &mut types, ty), name, val)
            .unwrap_or(std::ptr::null_mut())
    }).collect::<Vec<_>>();

    for (i, (func, _)) in funcs.iter().enumerate() {
        let ir_func = &module.funcs[i];
        if let Some(ir) = &ir_func.ir {
            build_func(ir_func, module, ir, ctx, builder, *func, &mut types, &funcs, &globals);
        }
    }
    let emit_time = start_time.elapsed();

    if print_ir {
        eprintln!("\n ---------- LLVM IR BEGIN ----------\n");
        LLVMDumpModule(llvm_module);
        eprintln!("\n ---------- LLVM IR END ------------\n");
        
    }
    #[cfg(debug_assertions)]
    llvm::analysis::LLVMVerifyModule(
        llvm_module,
        llvm::analysis::LLVMVerifierFailureAction::LLVMAbortProcessAction,
        std::ptr::null_mut()
    );

    // done building
    LLVMDisposeBuilder(builder);
    (
        Module(llvm_module),
        BackendStats {
            name: "LLVM",
            init: init_time,
            type_creation: type_creation_time,
            func_header_creation: func_header_time,
            emit: emit_time
        }
    )
}

unsafe fn build_func(
    func: &ir::Function,
    module: &ir::Module,
    ir: &ir::FunctionIr,
    ctx: LLVMContextRef,
    builder: LLVMBuilderRef,
    llvm_func: LLVMValueRef,
    types: &mut [TypeInstance],
    funcs: &[(LLVMValueRef, LLVMTypeRef)],
    globals: &[LLVMValueRef],
) {
    crate::log!("-------------------- Building LLVM IR for func {}", func.name);
    let blocks = (0..ir.block_count)
        .map(|_| LLVMAppendBasicBlockInContext(ctx, llvm_func, NONE) )
        .collect::<Vec<_>>();

    let mut instructions = Vec::new();

    let get_ref_and_type_ptr = |instructions: &[LLVMValueRef], r: ir::Ref| -> (LLVMValueRef, Type) {
        if let Some(val) = r.into_val() {
            match val {
                ir::RefVal::True | ir::RefVal::False => (
                    LLVMConstInt(LLVMInt1TypeInContext(ctx), if val == ir::RefVal::True { 1 } else { 0 }, FALSE),
                    Type::Prim(Primitive::Bool)
                ),
                ir::RefVal::Unit => (
                    LLVMGetUndef(LLVMVoidTypeInContext(ctx)),
                    Type::Prim(Primitive::Unit)
                ),
                ir::RefVal::Undef => panic!("Tried to use an undefined IR value. This is an internal compiler error."),
            }
        } else {
            let i = r.into_ref().unwrap() as usize;
            let r = instructions[i];
            debug_assert!(!r.is_null());
            let mut ty = ir.types.get(ir.inst[i].ty).clone();
            if matches!(ir.inst[i].tag, ir::Tag::Decl | ir::Tag::Param | ir::Tag::Member | ir::Tag::Global) {
                ty = Type::Pointer(Box::new(ty));
            }
            (r, ty)
        }
    };
    let get_ref_and_type = |instructions: &[LLVMValueRef], r: ir::Ref| get_ref_and_type_ptr(instructions, r);
    let get_ref = |instructions: &[LLVMValueRef], r: ir::Ref| get_ref_and_type(instructions, r).0;


    let table_ty = |ty: ir::TypeTableIndex, types: &mut [TypeInstance]| {
        let info = ir.types.get(ty);
        llvm_ty(ctx, module, types, info)
    };
    #[derive(Clone, Copy, Debug)]
    enum Numeric { Float(u32), Int(bool, u32) }
    impl Numeric {
        fn float(self) -> bool { matches!(self, Numeric::Float(_)) }
        fn int(self) -> bool { matches!(self, Numeric::Int(_, _)) }
    }
    fn prim_to_num(p: Primitive) -> Numeric {
        if let Some(p) = p.as_int() {
            Numeric::Int(p.is_signed(), p.bit_count())
        } else if let Some(p) = p.as_float() {
            Numeric::Float(p.bit_count())
        } else {
            panic!("Invalid type for int/float operation: {p}")
        }
    }
    let info_to_num = |info: &Type| {
        match info {
            ir::Type::Prim(p) => prim_to_num(*p),
            t => panic!("Invalid type for int/float operation: {t}")
        }
    };
    let float_or_int = |ty: ir::TypeTableIndex| info_to_num(ir.types.get(ty));

    for (i, inst) in ir.inst.iter().enumerate() {
        if crate::LOG.load(Ordering::Relaxed) {
            print!("Generating %{i} = {} ->", inst.display(&ir.extra, &ir.types));
            std::io::stdout().flush().unwrap();
        }
        let &ir::Instruction { tag, data, ty, used: _ } = inst;
        let val: LLVMValueRef = match tag {
            ir::Tag::BlockBegin => {
                LLVMPositionBuilderAtEnd(builder, blocks[data.int32 as usize]);
                ptr::null_mut()
            }
            ir::Tag::Ret => {
                let (r, ty) = get_ref_and_type(&instructions, data.un_op);
                if is_void_type(&ty) {
                    LLVMBuildRetVoid(builder)
                } else {
                    LLVMBuildRet(builder, r)
                }
            }
            ir::Tag::RetUndef => {
                if is_void_type(&func.header.return_type) {
                    LLVMBuildRetVoid(builder)
                } else {
                    let val = LLVMGetUndef(llvm_ty(ctx, module, types, &func.header.return_type));
                    LLVMBuildRet(builder, val)
                }
            }
            ir::Tag::Param => {
                let llvm_ty = llvm_ty(ctx, module, types, &func.header.params[data.int32 as usize].1);
                let param_var = LLVMBuildAlloca(builder, llvm_ty, NONE);
                let val = LLVMGetParam(llvm_func, data.int32);
                LLVMBuildStore(builder, val, param_var);
                param_var
            },
            ir::Tag::Int => LLVMConstInt(table_ty(ty, types), data.int, FALSE),
            ir::Tag::LargeInt => {
                let mut bytes = [0; 16];
                bytes.copy_from_slice(&ir.extra[data.extra as usize .. data.extra as usize + 16]);
                let num = u128::from_le_bytes(bytes);
                let words = [(num >> 64) as u64, (num as u64)];
                LLVMConstIntOfArbitraryPrecision(table_ty(ty, types), 2, words.as_ptr())
            }
            ir::Tag::Float => LLVMConstReal(table_ty(ty, types), data.float),
            ir::Tag::EnumLit => {
                let range = data.extra_len.0 as usize .. data.extra_len.0 as usize + data.extra_len.1 as usize;
                let name = &ir.extra[range];
                let (ty, index) = match &ir.types[ty] {
                    ir::Type::Enum(variants) => {
                        let index = variants.iter()
                            .enumerate()
                            .find(|(_, s)| s.as_bytes() == name)
                            .unwrap_or_else(|| panic!("Missing enum variant {}.", std::str::from_utf8(name).unwrap()))
                            .0;
                        let ty = int_from_variant_count(ctx, variants.len());
                        (ty, index)
                    }
                    ir::Type::Id(id, _) => {
                        let name = std::str::from_utf8(name)
                            .expect("Typecheck error: Internal Error: Enum variant in invalid utf8 encoded");
                        match &module.types[id.idx()].1 {
                            ir::TypeDef::Struct(_) => panic!("Expected enum, found struct type"),
                            ir::TypeDef::Enum(def) => {
                                let index = *def.variants.get(name)
                                    .expect("Typecheck failure: Missing enum variant.");
                                (int_from_variant_count(ctx, def.variants.len()), index as usize)
                            }
                            ir::TypeDef::NotGenerated { .. } => unreachable!()
                        }
                    }
                    _ => panic!("Enum variant not found for non-enum type")
                };
                LLVMConstInt(ty, index as _, FALSE)
            }
            ir::Tag::Decl => {
                if ir.types[ty].is_zero_sized(&module.types, &[]) {
                    ptr::null_mut()
                } else {
                    LLVMBuildAlloca(builder, table_ty(ty, types), NONE)
                }
            }
            ir::Tag::Load => {
                let (val, ty) = get_ref_and_type(&instructions, data.un_op);
                let Type::Pointer(inner) = ty else { panic!("Invalid IR, loading non-pointer type: {ty}"); };
                let pointee_ty = llvm_ty(ctx, module, types, &inner);
                LLVMBuildLoad2(builder, pointee_ty, val, NONE)
            }
            ir::Tag::Store => {
                let (val, ty) = get_ref_and_type(&instructions, data.bin_op.1);
                if ty.is_zero_sized(&module.types, &[]) {
                    ptr::null_mut()
                } else {
                    let ptr = get_ref(&instructions, data.bin_op.0);
                    LLVMBuildStore(builder, val, ptr)
                }
            }
            ir::Tag::String 
                => LLVMBuildGlobalStringPtr(builder, ir.extra.as_ptr().add(data.extra_len.0 as usize).cast(), NONE),
            ir::Tag::Call => {
                let begin = data.extra_len.0 as usize;
                let mut func_id = [0; 8];
                func_id.copy_from_slice(&ir.extra[begin..begin+8]);
                let func_id = u64::from_le_bytes(func_id);
                let (llvm_func, llvm_func_ty) = funcs[func_id as usize];

                let mut r_bytes = [0; 4];
                let mut args = (0..data.extra_len.1 as usize).map(|i| {
                    r_bytes.copy_from_slice(&ir.extra[begin + 8 + 4*i..begin + 8 + 4*(i+1)]);
                    get_ref(&instructions, ir::Ref::from_bytes(r_bytes))
                }).collect::<Vec<_>>();
                LLVMBuildCall2(builder, llvm_func_ty, llvm_func, args.as_mut_ptr(), args.len() as u32, NONE)
            }
            ir::Tag::Neg => {
                let r = get_ref(&instructions, data.un_op);
                if float_or_int(ty).float() {
                    LLVMBuildFNeg(builder, r, NONE)
                } else {
                    LLVMBuildNeg(builder, r, NONE)
                }
            }
            ir::Tag::Not => {
                let r = get_ref(&instructions, data.un_op);
                LLVMBuildNot(builder, r, NONE)
            }
            ir::Tag::Global => {
                globals[data.symbol.idx()]
            }
            ir::Tag::Add | ir::Tag::Sub | ir::Tag::Mul | ir::Tag::Div | ir::Tag::Mod | ir::Tag::Or | ir::Tag::And => {
                let l = get_ref(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                match tag {
                    ir::Tag::Add => if float_or_int(ty).float() {
                        LLVMBuildFAdd(builder, l, r, NONE)
                    } else {
                        LLVMBuildAdd(builder, l, r, NONE)
                    }
                    ir::Tag::Sub => if float_or_int(ty).float() {
                        LLVMBuildFSub(builder, l, r, NONE)
                    } else {
                        LLVMBuildSub(builder, l, r, NONE)
                    }
                    ir::Tag::Mul => if float_or_int(ty).float() {
                        LLVMBuildFMul(builder, l, r, NONE)
                    } else {
                        LLVMBuildMul(builder, l, r, NONE)
                    }
                    ir::Tag::Div => match float_or_int(ty) {
                        Numeric::Float(_) => LLVMBuildFDiv(builder, l, r, NONE),
                        Numeric::Int(false, _) => LLVMBuildUDiv(builder, l, r, NONE),
                        Numeric::Int(true, _) => LLVMBuildSDiv(builder, l, r, NONE),
                    }
                    ir::Tag::Mod => match float_or_int(ty) {
                        Numeric::Float(_) => LLVMBuildFRem(builder, l, r, NONE),
                        Numeric::Int(false, _) => LLVMBuildURem(builder, l, r, NONE),
                        Numeric::Int(true, _) => LLVMBuildSRem(builder, l, r, NONE),
                    }
                    ir::Tag::Or => LLVMBuildOr(builder, l, r, NONE),
                    ir::Tag::And => LLVMBuildAnd(builder, l, r, NONE),
                    _ => unreachable!()
                }       
            }
            ir::Tag::Eq | ir::Tag::Ne => {
                let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                let is_enum_ty = || {
                    if let Type::Id(id, _) = ty {
                        matches!(module.types[id.idx()].1, ir::TypeDef::Enum(_))
                    } else { false }
                };

                if matches!(ty, Type::Enum(_) | Type::Prim(Primitive::Bool)) 
                || is_enum_ty() || info_to_num(&ty).int() {
                    LLVMBuildICmp(builder, if tag == ir::Tag::Eq {LLVMIntEQ} else {LLVMIntNE}, l, r, NONE)
                } else {
                    LLVMBuildFCmp(builder, if tag == ir::Tag::Eq {LLVMRealUEQ} else {LLVMRealUNE}, l, r, NONE)
                }
            }
            // TODO: operator short circuiting
            ir::Tag::LT => {
                let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                match info_to_num(&ty) {
                    Numeric::Float(_) => LLVMBuildFCmp(builder, LLVMRealOLT, l, r, NONE),
                    Numeric::Int(s, _) => LLVMBuildICmp(builder, if s { LLVMIntSLT } else { LLVMIntULT }, l, r, NONE),
                }
            }
            ir::Tag::GT => {
                let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                match info_to_num(&ty) {
                    Numeric::Float(_) => LLVMBuildFCmp(builder, LLVMRealOGT, l, r, NONE),
                    Numeric::Int(s, _) => LLVMBuildICmp(builder, if s { LLVMIntSGT } else { LLVMIntUGT }, l, r, NONE),
                }
            }
            ir::Tag::LE => {
                let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                match info_to_num(&ty) {
                    Numeric::Float(_) => LLVMBuildFCmp(builder, LLVMRealOLE, l, r, NONE),
                    Numeric::Int(s, _) => LLVMBuildICmp(builder, if s { LLVMIntSLE } else { LLVMIntULE }, l, r, NONE),
                }
            }
            ir::Tag::GE => {
                let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                match info_to_num(&ty) {
                    Numeric::Float(_) => LLVMBuildFCmp(builder, LLVMRealOGT, l, r, NONE),
                    Numeric::Int(s, _) => LLVMBuildICmp(builder, if s { LLVMIntSGE } else { LLVMIntUGE }, l, r, NONE),
                }
            }
            ir::Tag::Member => {
                let (r, origin_ty) = get_ref_and_type(&instructions, data.bin_op.0);
                let (idx, idx_ty) = get_ref_and_type(&instructions, data.bin_op.1);
                let Type::Pointer(pointee) = origin_ty else { panic!("Tried to get member of non-pointer") };
                let int_ty = llvm_ty(ctx, module, types, &idx_ty);
                let mut elems = [LLVMConstInt(int_ty, 0, FALSE), idx];
                let pointee_ty = llvm_ty(ctx, module, types, &*pointee);
                LLVMBuildInBoundsGEP2(builder, pointee_ty, r, elems.as_mut_ptr(), elems.len() as _, NONE)
            }
            ir::Tag::Cast => {
                // cast just panics here right now when the cast is invalid because cast checks aren't implemented
                // anywhere before.
                // IR should probably just have different types of casts like in LLVM. 
                // (reinterpret, trunc, extend, float to int, int to float, etc.)
                let (val, origin) = get_ref_and_type(&instructions, data.un_op);
                let target = ir.types.get(ty);
                match target {
                    // pointer to int
                    Type::Prim(Primitive::U64) if matches!(origin, Type::Pointer(_)) => {
                        let llvm_target = llvm_ty(ctx, module, types, target);
                        LLVMBuildPtrToInt(builder, val, llvm_target, NONE)
                    }
                    Type::Prim(target) => {
                        //TODO: enum to int casts
                        match origin {
                            Type::Prim(origin) => {
                                let origin = prim_to_num(origin);
                                let target_num = prim_to_num(*target);
                                let llvm_target = llvm_primitive_ty(ctx, *target);
                                match (origin, target_num) {
                                    (Numeric::Float(a), Numeric::Float(b)) => match a.cmp(&b) {
                                        std::cmp::Ordering::Less 
                                            => LLVMBuildFPExt(builder, val, llvm_target, NONE),
                                        std::cmp::Ordering::Equal => val,
                                        std::cmp::Ordering::Greater 
                                            => LLVMBuildFPTrunc(builder, val, llvm_target, NONE),
                                    },
                                    (Numeric::Float(_a), Numeric::Int(s, _b)) => if s {
                                        LLVMBuildFPToSI(builder, val, llvm_target, NONE)
                                    } else {
                                        LLVMBuildFPToUI(builder, val, llvm_target, NONE)
                                    }
                                    (Numeric::Int(s, _a), Numeric::Float(_b)) => if s {
                                        LLVMBuildSIToFP(builder, val, llvm_target, NONE)
                                    } else {
                                        LLVMBuildUIToFP(builder, val, llvm_target, NONE)
                                    }
                                    (Numeric::Int(s1, a), Numeric::Int(s2, b)) => match a.cmp(&b) {
                                        std::cmp::Ordering::Less => if s2 {
                                            LLVMBuildSExt(builder, val, llvm_target, NONE)
                                        } else {
                                            LLVMBuildZExt(builder, val, llvm_target, NONE)
                                        }
                                        std::cmp::Ordering::Equal => if s1 == s2 { val } else {
                                            LLVMBuildBitCast(builder, val, llvm_target, NONE)
                                        },
                                        std::cmp::Ordering::Greater => LLVMBuildTrunc(builder, val, llvm_target, NONE)
                                    }
                                }
                            }
                            _ => panic!("Invalid cast to primitive")
                        }
                    }
                    Type::Id(_, _) | Type::Array(_) | Type::Tuple(_) => panic!("Invalid cast"),
                    Type::Pointer(_) => {
                        let llvm_target = llvm_ty(ctx, module, types, target);
                        match origin {
                            Type::Pointer(_) => LLVMBuildPointerCast(builder, val, llvm_target, NONE),
                            // int to ptr
                            Type::Prim(Primitive::U64) => LLVMBuildIntToPtr(builder, val, llvm_target, NONE),
                            t => panic!("Can't cast from non-pointer type {t} to pointer")
                        }
                    }
                    Type::Enum(_) => {
                        //TODO: int to enum casts
                        panic!("Enum casts unsupported")
                    }
                    Type::Generic(_) => panic!("Generic casts are invalid for now"),
                    Type::Invalid => unreachable!()
                }
            }
            ir::Tag::AsPointer => get_ref(&instructions, data.un_op),
            ir::Tag::Goto => LLVMBuildBr(builder, blocks[data.int32 as usize]),
            ir::Tag::Branch => {
                let mut bytes = [0; 4];
                let begin = data.branch.1 as usize;
                bytes.copy_from_slice(&ir.extra[begin .. begin+4]);
                let then = u32::from_le_bytes(bytes);
                bytes.copy_from_slice(&ir.extra[begin+4 .. begin+8]);
                let else_ = u32::from_le_bytes(bytes);

                LLVMBuildCondBr(builder, get_ref(&instructions, data.branch.0), blocks[then as usize], blocks[else_ as usize])
            }
            ir::Tag::Phi => {
                if *ir.types.get(ty) == Type::Prim(Primitive::Unit) {
                    LLVMGetUndef(LLVMVoidTypeInContext(ctx))
                } else {
                    let phi = LLVMBuildPhi(builder, table_ty(ty, types), NONE);
                    let begin = data.extra_len.0 as usize;
                    for i in 0..data.extra_len.1 {
                        let c = begin + i as usize * 8;
                        let mut b = [0; 4];
                        b.copy_from_slice(&ir.extra[c..c+4]);
                        let block = u32::from_le_bytes(b);
                        b.copy_from_slice(&ir.extra[c+4..c+8]);
                        let r = ir::Ref::from_bytes(b);
                        let mut block = blocks[block as usize];
                        LLVMAddIncoming(phi, &mut get_ref(&instructions, r), &mut block, 1);
                    }
                    phi
                }
            }
            ir::Tag::Asm => {
                let ir::Data { asm: (extra, str_len, arg_count) } = data;
                let str_bytes = &ir.extra[extra as usize .. extra as usize + str_len as usize];
                
                let expr_base = extra as usize + str_len as usize;
                let mut asm_values = Vec::with_capacity(arg_count as usize);
                let mut asm_types = Vec::with_capacity(arg_count as usize);
                for i in 0..arg_count as usize {
                    let mut arg_bytes = [0; 4];
                    arg_bytes.copy_from_slice(&ir.extra[expr_base + 4*i .. expr_base + 4*(i+1) ]);
                    let (val, ty) = get_ref_and_type(&instructions, ir::Ref::from_bytes(arg_bytes));
                    asm_values.push(val);
                    asm_types.push(llvm_ty(ctx, module, types, &ty));
                }

                inline_asm(std::str::from_utf8_unchecked(str_bytes), ctx, builder, &asm_values, &mut asm_types)
            }
        };
        if val.is_null() {
            crate::log!("null");
        } else {
            let cstr = val_str(val);
            crate::log!("{cstr:?}");
        }

        instructions.push(val);
    }
}

unsafe fn inline_asm(
    asm: &str, ctx: LLVMContextRef, builder: LLVMBuilderRef,
    values: &[LLVMValueRef], types: &mut [LLVMTypeRef]
) -> LLVMValueRef {
    debug_assert!(values.len() == types.len());
    let side_effects = true;
    let align_stack = true;
    let func_ty = LLVMFunctionType(LLVMVoidTypeInContext(ctx), types.as_mut_ptr(), types.len() as _, FALSE);
    println!("----- {:?} -----\n\n", ffi::CStr::from_ptr(LLVMPrintTypeToString(func_ty)));
    let asm = LLVMGetInlineAsm(
        func_ty,
        asm.as_ptr() as *mut i8, asm.len(),
        "\0".as_ptr() as *mut i8, 0,
        llvm_bool(side_effects),
        llvm_bool(align_stack),
        llvm_sys::LLVMInlineAsmDialect::LLVMInlineAsmDialectIntel,
        FALSE
    );
    LLVMBuildCall2(builder, func_ty, asm, values.as_ptr() as *mut LLVMValueRef, values.len() as _, NONE)
}

fn llvm_bool(b: bool) -> LLVMBool {
    match b {
        true => TRUE,
        false => FALSE
    }
}

fn val_str(val: LLVMValueRef) -> ffi::CString {
    unsafe { ffi::CString::from_raw(LLVMPrintValueToString(val)) }
}

unsafe fn llvm_primitive_ty(ctx: LLVMContextRef, p: Primitive) -> LLVMTypeRef {
    use crate::types::Primitive::*;
    match p {
        I8 | U8 => LLVMInt8TypeInContext(ctx),
        I16 | U16 => LLVMInt16TypeInContext(ctx),
        I32 | U32 => LLVMInt32TypeInContext(ctx),
        I64 | U64 => LLVMInt64TypeInContext(ctx),
        I128 | U128 => LLVMInt128TypeInContext(ctx),
        F32 => LLVMFloatTypeInContext(ctx),
        F64 => LLVMDoubleTypeInContext(ctx),
        Bool => LLVMInt1TypeInContext(ctx),
        Unit | Never | Type => LLVMVoidTypeInContext(ctx),
    }
}

unsafe fn llvm_ty(ctx: LLVMContextRef, module: &ir::Module, types: &mut [TypeInstance], ty: &Type) -> LLVMTypeRef {
    llvm_ty_recursive(ctx, module, types, ty, false, &[])
}

unsafe fn int_from_variant_count(ctx: LLVMContextRef, count: usize) -> LLVMTypeRef {
    if count < 2 {
        LLVMVoidTypeInContext(ctx)
    } else {
        let bit_size = (count-1).log2() + 1;
        LLVMIntTypeInContext(ctx, bit_size)
    }
}

unsafe fn llvm_ty_recursive(
    ctx: LLVMContextRef,
    module: &ir::Module,
    types: &mut [TypeInstance],
    ty: &Type,
    pointee: bool,
    generics: &[Type],
) -> LLVMTypeRef {
    match ty {
        Type::Prim(Primitive::Unit) if pointee => llvm_primitive_ty(ctx, Primitive::I8),
        Type::Prim(p) => llvm_primitive_ty(ctx, *p),
        Type::Id(id, generics) => match &mut types[id.idx()] {
            TypeInstance::Simple(simple) => {
                debug_assert_eq!(generics.len(), 0);
                *simple
            }
            TypeInstance::Generic(map) => {
                if let Some(llvm_ty) = map.get(generics) { return *llvm_ty };
                let mut name = format!("t{}[", id.idx());
                
                for (i, ty) in generics.iter().enumerate() {
                    use std::fmt::Write;
                    if i != 0 {
                        name.push_str(", ");
                    }
                    name.write_fmt(format_args!("{ty}")).unwrap();
                }
                name.push(']');
                let name = ffi::CString::new(name).unwrap();
                match &module.types[id.idx()].1 {
                    ir::TypeDef::Struct(def) => {
                        let llvm_struct = LLVMStructCreateNamed(ctx, name.as_ptr());
                        map.insert(generics.clone(), llvm_struct);
                        let mut members = def.members.iter()
                            .map(|(_, ty)| llvm_ty_recursive(ctx, module, types, ty, false, generics))
                            .collect::<Vec<_>>();
                            LLVMStructSetBody(llvm_struct, members.as_mut_ptr(), members.len() as _, FALSE);
                        llvm_struct
                    }
                    ir::TypeDef::Enum(def) => {
                        int_from_variant_count(ctx, def.variants.len())
                    }
                    ir::TypeDef::NotGenerated { .. } => unreachable!()
                }
            }
        }
        Type::Pointer(inner) => {
            LLVMPointerType(llvm_ty_recursive(ctx, module, types, inner, true, generics), 0)
        }
        Type::Array(box (inner, count)) => {
            let elem_ty = llvm_ty_recursive(ctx, module, types, inner, false, generics);
            LLVMArrayType(elem_ty, *count)
        }
        Type::Enum(variants) => {
            int_from_variant_count(ctx, variants.len())
        }
        Type::Tuple(elems) => {
            let mut elem_tys = elems.iter()
                .map(|ty| llvm_ty_recursive(ctx, module, types, ty, false, generics))
                .collect::<Vec<_>>();
            LLVMStructTypeInContext(ctx, elem_tys.as_mut_ptr(), elem_tys.len() as u32, FALSE)
        }
        &Type::Generic(idx) => llvm_ty(ctx, module, types, &generics[idx as usize]),
        Type::Invalid => {
            eprintln!("ERROR: Invalid type reached codegen type");
            llvm_ty_recursive(ctx, module, types, &Type::Prim(Primitive::Unit), pointee, generics)
        }
    }
}

fn is_void_type(ty: &Type) -> bool {
    matches!(ty, Type::Prim(Primitive::Unit | Primitive::Never))
}

enum TypeInstance {
    Simple(LLVMTypeRef),
    Generic(DHashMap<Vec<Type>, LLVMTypeRef>),
}

// returns the constant or None in case of a zero sized type
unsafe fn add_global(
    ctx: LLVMContextRef, module: LLVMModuleRef, ty: LLVMTypeRef, name: &str, val: &Option<ir::ConstVal>
) -> Option<LLVMValueRef> {
    let c_name = ffi::CString::new(name).unwrap();
    let global = LLVMAddGlobal(module, ty, c_name.as_ptr());
    LLVMSetInitializer(global, val.as_ref().map_or_else(|| Some(LLVMGetUndef(ty)), |val| gen_const(ctx, ty, val))?);
    Some(global)
}

unsafe fn gen_const(ctx: LLVMContextRef, ty: LLVMTypeRef, val: &ir::ConstVal) -> Option<LLVMValueRef> {
    Some(match val {
        ir::ConstVal::Invalid => LLVMGetUndef(ty),
        ir::ConstVal::Unit => return None,
        &ir::ConstVal::Int(int) => {
            let unsigned_int = if int < 0 { (-int) as u128 } else { int as u128 };
            LLVMConstInt(ty, u64::try_from(unsigned_int).expect("TODO: large global ints"), llvm_bool(int < 0))
        }
        ir::ConstVal::Float(_float) => todo!("Float globals"),
        ir::ConstVal::String(s) => LLVMConstStringInContext(ctx, s.as_ptr().cast(), s.len() as u32, FALSE),
        ir::ConstVal::EnumVariant(_val) => todo!("static enum values"),
        &ir::ConstVal::Bool(b) => LLVMConstInt(LLVMInt1TypeInContext(ctx), if b {1} else {0}, FALSE),
        ir::ConstVal::Symbol(_) | ir::ConstVal::NotGenerated { .. }
            => unreachable!("This shouldn't reach codegen"),
    })
}