use llvm::{execution_engine, target, core::*, prelude::*, LLVMRealPredicate::*, LLVMIntPredicate::*};
use crate::{ir, irgen::{self, TypeInfo}, types::Primitive};
use std::{mem, ffi, ptr};

const FALSE: LLVMBool = 0;
const TRUE: LLVMBool = 1;
const NONE: *const i8 = "ABC\0".as_ptr() as _;

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
        String => LLVMPointerType(LLVMInt8TypeInContext(ctx), 0),
        Bool => LLVMInt1TypeInContext(ctx),
        Func => todo!(),
        Type => todo!(),
        Unit => LLVMVoidTypeInContext(ctx),
        Never => unreachable!(), // should the never type ever be represented in llvm?
    }
}

unsafe fn llvm_ty(ctx: LLVMContextRef, types: &[LLVMTypeRef], ty: &ir::TypeRef) -> LLVMTypeRef {
    match ty {
        ir::TypeRef::Primitive(p) => llvm_primitive_ty(ctx, *p),
        ir::TypeRef::Resolved(id) => types[id.idx()],
        ir::TypeRef::Invalid => panic!("Invalid types shouldn't reach the codegen stage"),
    }
}

pub unsafe fn module(ctx: LLVMContextRef, module: &ir::Module) {
    // Set up the module
    let module_name = ffi::CString::new(module.name.as_bytes()).unwrap();
    let llvm_module = LLVMModuleCreateWithNameInContext(module_name.as_ptr(), ctx);

    // define types

    let types = (0..module.types.len())
        .map(|_| LLVMStructType(ptr::null_mut(), 0, FALSE))
        .collect::<Vec<_>>();

    for (ty, struct_ty) in module.types.iter().zip(&types) {
        let ir::Type::Struct(struct_) = ty;
        let mut members = struct_.members.iter().map(|(_name, ty)| llvm_ty(ctx, &types, ty)).collect::<Vec<_>>();
        LLVMStructSetBody(*struct_ty, members.as_mut_ptr(), members.len() as u32, FALSE);
    }

    // define function headers

    let funcs = module.funcs.iter()
        .map(|func| {
            let ret = llvm_ty(ctx, &types, &func.header().return_type);
            let params = func.header().params.iter().map(|(_name, ty)| llvm_ty(ctx, &types, ty));

            let (mut params, vararg): (Vec<_>, _) = if let Some((_, vararg)) = &func.header.vararg {
                let vararg_ty = llvm_ty(ctx, &types, vararg);
                (params.chain(std::iter::once(vararg_ty)).collect(), TRUE)
            } else {
                (params.collect(), FALSE)
            };

            let func_ty = LLVMFunctionType(ret, params.as_mut_ptr(), params.len() as u32, vararg);
            let name = ffi::CString::new(func.header().name.as_bytes()).unwrap();
            LLVMAddFunction(llvm_module, name.as_ptr(), func_ty)
        })
        .collect::<Vec<_>>();

    // set up a builder and build the function bodies
    let builder = LLVMCreateBuilderInContext(ctx);
    
    for (i, func) in funcs.iter().enumerate() {
        build_func(&module.funcs[i], ctx, builder, *func, &types, &funcs);
    }
    
    // done building
    LLVMDisposeBuilder(builder);
  
    if crate::LOG.load(std::sync::atomic::Ordering::Relaxed) {
        println!("\n ---------- LLVM IR BEGIN ----------\n");
        LLVMDumpModule(llvm_module);
        println!("\n ---------- LLVM IR END ------------\n");
        
    }

    // build an execution engine
    let mut ee = mem::MaybeUninit::uninit().assume_init();
    let mut out = ptr::null_mut();

    // robust code should check that these calls complete successfully
    // each of these calls is necessary to setup an execution engine which compiles to native
    // code
    execution_engine::LLVMLinkInMCJIT();
    target::LLVM_InitializeNativeTarget();
    target::LLVM_InitializeNativeAsmPrinter();

    // takes ownership of the module
    execution_engine::LLVMCreateExecutionEngineForModule(&mut ee, llvm_module, &mut out);

    let addr = execution_engine::LLVMGetFunctionAddress(ee, "main\0".as_ptr() as _);
    if addr == 0 {
        panic!("Main symbol not found");
    }

    let f: extern "C" fn() -> u64 = mem::transmute(addr);

    let res = f();

    println!("Main function returned {}", res);

    // Clean up the rest.
    execution_engine::LLVMDisposeExecutionEngine(ee);

}


unsafe fn build_func(func: &ir::Function, ctx: LLVMContextRef, builder: LLVMBuilderRef, llvm_func: LLVMValueRef, types: &[LLVMTypeRef], funcs: &[LLVMValueRef]) {
    crate::log!("Building LLVM ir for function {}", func.header().name);
    let zero_i32 = LLVMConstInt(LLVMInt32TypeInContext(ctx), 0, FALSE);
    let blocks = (0..func.block_count).map(|_| LLVMAppendBasicBlockInContext(ctx, llvm_func, NONE) ).collect::<Vec<_>>();

    let mut instructions = Vec::new();

    let get_ref_and_type = |instructions: &[LLVMValueRef], r: ir::Ref| -> (LLVMValueRef, TypeInfo) {
        if let Some(val) = r.into_val() {
            match val {
                ir::RefVal::True | ir::RefVal::False => (
                    LLVMConstInt(LLVMInt1TypeInContext(ctx), if val == ir::RefVal::True { 1 } else { 0 }, FALSE),
                    TypeInfo::Primitive(Primitive::Bool)
                ),
                ir::RefVal::Unit => (LLVMGetUndef(LLVMVoidTypeInContext(ctx)), TypeInfo::Primitive(Primitive::Unit)),
                ir::RefVal::Undef => panic!(),
            }
        } else {
            let i = r.into_ref().unwrap() as usize;
            let r = instructions[i];
            debug_assert!(!r.is_null());
            (r, func.types.get_type(func.ir[i].ty).0)
        }
    };
    let get_ref = |instructions: &[LLVMValueRef], r: ir::Ref| get_ref_and_type(instructions, r).0;

    let table_ty = |ty: ir::TypeTableIndex| {
        let info = func.types.get_type(ty).0;
        let type_ref = match info {
            crate::irgen::TypeInfo::Unknown => panic!("Type must be known during codegen"),
            crate::irgen::TypeInfo::Int => ir::TypeRef::Primitive(Primitive::I32),
            crate::irgen::TypeInfo::Float => ir::TypeRef::Primitive(Primitive::F32),
            crate::irgen::TypeInfo::Func(_) => todo!(),
            crate::irgen::TypeInfo::Type(_) => todo!(),
            crate::irgen::TypeInfo::Primitive(p) => ir::TypeRef::Primitive(p),
            crate::irgen::TypeInfo::Resolved(id) => ir::TypeRef::Resolved(id),
            crate::irgen::TypeInfo::Invalid => panic!("Invalid types shouldn't reach codegen stage"),
        };
        llvm_ty(ctx, types, &type_ref)
    };
    #[derive(Clone, Copy, Debug)]
    enum Numeric { Float(u32), Int(bool, u32) }
    impl Numeric {
        fn float(&self) -> bool { matches!(self, Numeric::Float(_)) }
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
    let info_to_num = |info: TypeInfo| {
        match info {
            irgen::TypeInfo::Int => Numeric::Int(true, 32),
            irgen::TypeInfo::Primitive(p) => prim_to_num(p),
            irgen::TypeInfo::Float => Numeric::Float(32),
            t => panic!("Invalid type for int/float operation: {t}")
        }
    };
    let float_or_int = |ty: ir::TypeTableIndex| info_to_num(func.types.get_type(ty).0);

    for (i, ir::Instruction { tag, data, span: _, ty }) in func.ir.iter().enumerate() {
        let val: LLVMValueRef = match tag {
            ir::Tag::BlockBegin => {
                LLVMPositionBuilderAtEnd(builder, blocks[data.int32 as usize]);
                ptr::null_mut()
            }
            ir::Tag::Ret => {
                let (r, ty) = get_ref_and_type(&instructions, data.un_op);
                if let TypeInfo::Primitive(Primitive::Unit) = ty {
                    LLVMBuildRetVoid(builder)
                } else {
                    LLVMBuildRet(builder, r)
                }
            }
            ir::Tag::Invalid => panic!("Invalid references shouldn't reach codegen stage"),
            ir::Tag::Param => LLVMGetParam(llvm_func, data.int32),
            ir::Tag::Int => LLVMConstInt(table_ty(*ty), data.int, FALSE),
            ir::Tag::LargeInt => {
                let mut bytes = [0; 16];
                bytes.copy_from_slice(&func.extra[data.extra as usize .. data.extra as usize + 16]);
                let num = u128::from_le_bytes(bytes);
                let words = [(num >> 64) as u64, (num as u64)];
                LLVMConstIntOfArbitraryPrecision(table_ty(*ty), 2, words.as_ptr())
            }
            ir::Tag::Float => LLVMConstReal(table_ty(*ty), data.float),
            ir::Tag::Decl => LLVMBuildAlloca(builder, table_ty(*ty), NONE),
            ir::Tag::Load => LLVMBuildLoad(builder, get_ref(&instructions, data.un_op), NONE),
            ir::Tag::Store => LLVMBuildStore(builder, get_ref(&instructions, data.bin_op.1), get_ref(&instructions, data.bin_op.0)),
            ir::Tag::String => LLVMConstStringInContext(
                ctx,
                func.extra.as_ptr().add(data.extra_len.0 as usize) as _,
                data.extra_len.1,
                FALSE  //TODO: null termination?
            ),
            ir::Tag::Call => {
                let begin = data.extra_len.0 as usize;
                let mut func_id = [0; 8];
                func_id.copy_from_slice(&func.extra[begin..begin+8]);
                let func_id = u64::from_le_bytes(func_id);
                let llvm_func = funcs[func_id as usize];

                let mut r_bytes = [0; 4];
                let mut args = (0..data.extra_len.1 as usize).map(|i| {
                    r_bytes.copy_from_slice(&func.extra[begin + 8 + 4*i..begin + 8 + 4*(i+1)]);
                    get_ref(&instructions, ir::Ref::from_bytes(r_bytes))
                }).collect::<Vec<_>>();
                LLVMBuildCall(builder, llvm_func, args.as_mut_ptr(), args.len() as u32, NONE)
            }
            ir::Tag::Neg => {
                let r = get_ref(&instructions, data.un_op);
                if float_or_int(*ty).float() {
                    LLVMBuildFNeg(builder, r, NONE)
                } else {
                    LLVMBuildNeg(builder, r, NONE)
                }
            }
            ir::Tag::Add => {
                let l = get_ref(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                if float_or_int(*ty).float() {
                    LLVMBuildFAdd(builder, l, r, NONE)
                } else {
                    LLVMBuildAdd(builder, l, r, NONE)
                }
            }
            ir::Tag::Sub => {
                let l = get_ref(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                if float_or_int(*ty).float() {
                    LLVMBuildFSub(builder, l, r, NONE)
                } else {
                    LLVMBuildSub(builder, l, r, NONE)
                }
            }
            ir::Tag::Mul => {
                let l = get_ref(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                if float_or_int(*ty).float() {
                    LLVMBuildFMul(builder, l, r, NONE)
                } else {
                    LLVMBuildMul(builder, l, r, NONE)
                }
            }
            ir::Tag::Div => {
                let l = get_ref(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                match float_or_int(*ty) {
                    Numeric::Float(_) => LLVMBuildFDiv(builder, l, r, NONE),
                    Numeric::Int(false, _) => LLVMBuildUDiv(builder, l, r, NONE),
                    Numeric::Int(true, _) => LLVMBuildSDiv(builder, l, r, NONE),
                }
            }
            ir::Tag::Eq => {
                let l = get_ref(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                if float_or_int(*ty).float() {
                    LLVMBuildFCmp(builder, LLVMRealUEQ, l, r, NONE)
                } else {
                    LLVMBuildICmp(builder, LLVMIntEQ, l, r, NONE)
                }
            }
            // TODO: operator short circuiting
            ir::Tag::LT => {
                let l = get_ref(&instructions, dbg!(data.bin_op.0));
                let r = get_ref(&instructions, dbg!(data.bin_op.1));
                
                match float_or_int(*ty) {
                    Numeric::Float(_) => LLVMBuildFCmp(builder, LLVMRealOLT, l, r, NONE),
                    Numeric::Int(s, _) => LLVMBuildICmp(builder, if s { LLVMIntSLT } else { LLVMIntULT }, l, r, NONE),
                }
            }
            ir::Tag::GT => {
                let l = get_ref(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                match float_or_int(*ty) {
                    Numeric::Float(_) => LLVMBuildFCmp(builder, LLVMRealOGT, l, r, NONE),
                    Numeric::Int(s, _) => LLVMBuildICmp(builder, if s { LLVMIntSGT } else { LLVMIntUGT }, l, r, NONE),
                }
            }
            ir::Tag::LE => {
                let l = get_ref(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                match float_or_int(*ty) {
                    Numeric::Float(_) => LLVMBuildFCmp(builder, LLVMRealOLE, l, r, NONE),
                    Numeric::Int(s, _) => LLVMBuildICmp(builder, if s { LLVMIntSLE } else { LLVMIntULE }, l, r, NONE),
                }
            }
            ir::Tag::GE => {
                let l = get_ref(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                match float_or_int(*ty) {
                    Numeric::Float(_) => LLVMBuildFCmp(builder, LLVMRealOGT, l, r, NONE),
                    Numeric::Int(s, _) => LLVMBuildICmp(builder, if s { LLVMIntSGE } else { LLVMIntUGE }, l, r, NONE),
                }
            }
            ir::Tag::Member => {
                let r = get_ref(&instructions, data.member.0);
                let mut elems = [zero_i32, LLVMConstInt(LLVMInt32TypeInContext(ctx), data.member.1 as u64, FALSE)];
                LLVMBuildGEP(builder, r, elems.as_mut_ptr(), 2, NONE)
            }
            ir::Tag::Cast => {
                let (val, ty) = get_ref_and_type(&instructions, data.cast.0);
                let origin = info_to_num(ty);
                let target = prim_to_num(data.cast.1);
                dbg!(origin, target);
                let llvm_target = llvm_primitive_ty(ctx, data.cast.1);
                match (origin, target) {
                    (Numeric::Float(a), Numeric::Float(b)) => match a.cmp(&b) {
                        std::cmp::Ordering::Less => LLVMBuildFPExt(builder, val, llvm_target, NONE),
                        std::cmp::Ordering::Equal => val,
                        std::cmp::Ordering::Greater => LLVMBuildFPTrunc(builder, val, llvm_target, NONE),
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
            ir::Tag::Goto => LLVMBuildBr(builder, blocks[data.int32 as usize]),
            ir::Tag::Branch => {
                let mut bytes = [0; 4];
                let begin = data.branch.1 as usize;
                bytes.copy_from_slice(&func.extra[begin .. begin+4]);
                let then = u32::from_le_bytes(bytes);
                bytes.copy_from_slice(&func.extra[begin+4 .. begin+8]);
                let else_ = u32::from_le_bytes(bytes);

                LLVMBuildCondBr(builder, get_ref(&instructions, data.branch.0), blocks[then as usize], blocks[else_ as usize])
            }
            ir::Tag::Phi => {
                LLVMBuildPhi(builder, table_ty(*ty), NONE)
            }
        };

        let cstr = ffi::CStr::from_ptr(LLVMPrintValueToString(val));
        println!("{i}: {cstr:?}");

        instructions.push(val);
    }
}