use llvm::{core::*, prelude::*, LLVMRealPredicate::*, LLVMIntPredicate::*, LLVMModule};
use crate::{ir::{self, Type}, types::Primitive, BackendStats};
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
        Unit => LLVMVoidTypeInContext(ctx),
        Never => unreachable!(), // should the never type ever be represented in llvm?
    }
}

unsafe fn llvm_ty(ctx: LLVMContextRef, types: &[LLVMTypeRef], ty: &Type) -> LLVMTypeRef {
    llvm_ty_(ctx, types, ty, false)
}

unsafe fn int_from_variant_count(ctx: LLVMContextRef, count: usize) -> LLVMTypeRef {
    if count < 2 {
        LLVMVoidTypeInContext(ctx)
    } else {
        let bit_size = (count-1).log2() + 1;
        LLVMIntTypeInContext(ctx, bit_size)
    }
}

unsafe fn llvm_ty_(ctx: LLVMContextRef, types: &[LLVMTypeRef], ty: &Type, pointee: bool) -> LLVMTypeRef {
    match ty {
        Type::Prim(Primitive::Unit) if pointee => llvm_primitive_ty(ctx, Primitive::I8),
        Type::Prim(p) => llvm_primitive_ty(ctx, *p),
        Type::Id(id) => types[id.idx()],
        Type::Pointer(inner) => {
            LLVMPointerType(llvm_ty_(ctx, types, inner, true), 0)
        }
        Type::Array(box (inner, count)) => {
            let elem_ty = llvm_ty_(ctx, types, inner, false);
            LLVMArrayType(elem_ty, *count)
        }
        Type::Enum(variants) => {
            int_from_variant_count(ctx, variants.len())
        }
        Type::Invalid => {
            eprintln!("ERROR: Invalid type reached codegen type");
            llvm_ty_(ctx, types, &Type::Prim(Primitive::Unit), pointee)
        }
    }
}

pub unsafe fn module(ctx: LLVMContextRef, module: &ir::Module) -> (Module, BackendStats) {
    let start_time = Instant::now();
    // Set up the module
    let module_name = ffi::CString::new(module.name.as_bytes()).unwrap();
    let llvm_module = LLVMModuleCreateWithNameInContext(module_name.as_ptr(), ctx);
    
    let init_time = start_time.elapsed();

    // define types
    let start_time = Instant::now();

    let types = module.types.iter()
        .map(|ty| {
            let ir::TypeDef::Struct(struct_) = ty;
            let name = ffi::CString::new(struct_.name.as_bytes()).unwrap();
            LLVMStructCreateNamed(ctx, name.as_ptr())
        })
        .collect::<Vec<_>>();

    for (ty, struct_ty) in module.types.iter().zip(&types) {
        let ir::TypeDef::Struct(struct_) = ty;
        let mut members = struct_.members.iter().map(|(_name, ty)| llvm_ty(ctx, &types, ty)).collect::<Vec<_>>();
        LLVMStructSetBody(*struct_ty, members.as_mut_ptr(), members.len() as u32, FALSE);
    }

    let type_creation_time = start_time.elapsed();

    // define function headers
    let start_time = Instant::now();

    let funcs = module.funcs.iter()
        .map(|func| {
            let ret = llvm_ty(ctx, &types, &func.header.return_type);
            let mut params = func.header.params.iter().map(|(_name, ty)| llvm_ty(ctx, &types, ty)).collect::<Vec<_>>();
            
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
    
    for (i, (func, _)) in funcs.iter().enumerate() {
        let ir_func = &module.funcs[i];
        if let Some(ir) = &ir_func.ir {
            build_func(ir_func, ir, ctx, builder, *func, &types, &funcs);
        }
    }
    let emit_time = start_time.elapsed();

    if crate::LOG.load(std::sync::atomic::Ordering::Relaxed) {
        println!("\n ---------- LLVM IR BEGIN ----------\n");
        LLVMDumpModule(llvm_module);
        println!("\n ---------- LLVM IR END ------------\n");
        
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
    ir: &ir::FunctionIr,
    ctx: LLVMContextRef,
    builder: LLVMBuilderRef,
    llvm_func: LLVMValueRef,
    types: &[LLVMTypeRef],
    funcs: &[(LLVMValueRef, LLVMTypeRef)]
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
            if matches!(ir.inst[i].tag, ir::Tag::Decl | ir::Tag::Param | ir::Tag::Member) {
                ty = ty.pointer_to();
            }
            (r, ty)
        }
    };
    let get_ref_and_type = |instructions: &[LLVMValueRef], r: ir::Ref| get_ref_and_type_ptr(instructions, r);
    let get_ref = |instructions: &[LLVMValueRef], r: ir::Ref| get_ref_and_type(instructions, r).0;


    let table_ty = |ty: ir::TypeTableIndex| {
        let info = ir.types.get(ty);
        llvm_ty(ctx, types, &info)
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
        let ir::Instruction { tag, data, ty, used: _} = inst;
        let val: LLVMValueRef = match tag {
            ir::Tag::BlockBegin => {
                LLVMPositionBuilderAtEnd(builder, blocks[data.int32 as usize]);
                ptr::null_mut()
            }
            ir::Tag::Ret => {
                let (r, ty) = get_ref_and_type(&instructions, data.un_op);
                if let Type::Prim(Primitive::Unit) = ty {
                    LLVMBuildRetVoid(builder)
                } else {
                    LLVMBuildRet(builder, r)
                }
            }
            ir::Tag::Param => {
                let llvm_ty = llvm_ty(ctx, types, &func.header.params[data.int32 as usize].1);
                let param_var = LLVMBuildAlloca(builder, llvm_ty, NONE);
                let val = LLVMGetParam(llvm_func, data.int32);
                LLVMBuildStore(builder, val, param_var);
                param_var
            },
            ir::Tag::Int => LLVMConstInt(table_ty(*ty), data.int, FALSE),
            ir::Tag::LargeInt => {
                let mut bytes = [0; 16];
                bytes.copy_from_slice(&ir.extra[data.extra as usize .. data.extra as usize + 16]);
                let num = u128::from_le_bytes(bytes);
                let words = [(num >> 64) as u64, (num as u64)];
                LLVMConstIntOfArbitraryPrecision(table_ty(*ty), 2, words.as_ptr())
            }
            ir::Tag::Float => LLVMConstReal(table_ty(*ty), data.float),
            ir::Tag::EnumLit => {
                let range = data.extra_len.0 as usize .. data.extra_len.0 as usize + data.extra_len.1 as usize;
                let name = &ir.extra[range];
                let ir::Type::Enum(variants) = &ir.types[*ty] else { panic!("Enum variant found for non-enum type")};
                let index = variants.iter()
                    .enumerate()
                    .find(|(_, s)| s.as_bytes() == name)
                    .unwrap_or_else(|| panic!("Missing enum variant {}.", std::str::from_utf8(name).unwrap()))
                    .0;
                let ty = int_from_variant_count(ctx, variants.len());
                LLVMConstInt(ty, index as _, FALSE)
            }
            ir::Tag::Decl => LLVMBuildAlloca(builder, table_ty(*ty), NONE),
            ir::Tag::Load => {
                let (val, ty) = get_ref_and_type(&instructions, data.un_op);
                let Type::Pointer(inner) = ty else { panic!("Invalid IR, loading non-pointer type: {ty}"); };
                let pointee_ty = llvm_ty(ctx, types, &inner);
                LLVMBuildLoad2(builder, pointee_ty, val, NONE)
            }
            ir::Tag::Store => LLVMBuildStore(
                builder,
                get_ref(&instructions, data.bin_op.1),
                get_ref(&instructions, data.bin_op.0)
            ),
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
                if float_or_int(*ty).float() {
                    LLVMBuildFNeg(builder, r, NONE)
                } else {
                    LLVMBuildNeg(builder, r, NONE)
                }
            }
            ir::Tag::Not => {
                let r = get_ref(&instructions, data.un_op);
                LLVMBuildNot(builder, r, NONE)
            }
            ir::Tag::Add | ir::Tag::Sub | ir::Tag::Mul | ir::Tag::Div | ir::Tag::Mod | ir::Tag::Or | ir::Tag::And => {
                let l = get_ref(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);
                
                match tag {
                    ir::Tag::Add => if float_or_int(*ty).float() {
                        LLVMBuildFAdd(builder, l, r, NONE)
                    } else {
                        LLVMBuildAdd(builder, l, r, NONE)
                    }
                    ir::Tag::Sub => if float_or_int(*ty).float() {
                        LLVMBuildFSub(builder, l, r, NONE)
                    } else {
                        LLVMBuildSub(builder, l, r, NONE)
                    }
                    ir::Tag::Mul => if float_or_int(*ty).float() {
                        LLVMBuildFMul(builder, l, r, NONE)
                    } else {
                        LLVMBuildMul(builder, l, r, NONE)
                    }
                    ir::Tag::Div => match float_or_int(*ty) {
                        Numeric::Float(_) => LLVMBuildFDiv(builder, l, r, NONE),
                        Numeric::Int(false, _) => LLVMBuildUDiv(builder, l, r, NONE),
                        Numeric::Int(true, _) => LLVMBuildSDiv(builder, l, r, NONE),
                    }
                    ir::Tag::Mod => match float_or_int(*ty) {
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
                
                if matches!(ty, Type::Enum(_) | Type::Prim(Primitive::Bool)) || info_to_num(&ty).int() {
                    LLVMBuildICmp(builder, if *tag == ir::Tag::Eq {LLVMIntEQ} else {LLVMIntNE}, l, r, NONE)
                } else {
                    LLVMBuildFCmp(builder, if *tag == ir::Tag::Eq {LLVMRealUEQ} else {LLVMRealUNE}, l, r, NONE)
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
                let int_ty = llvm_ty(ctx, &types, &idx_ty);
                let mut elems = [LLVMConstInt(int_ty, 0, FALSE), idx];
                let pointee_ty = llvm_ty(ctx, types, &*pointee);
                LLVMBuildInBoundsGEP2(builder, pointee_ty, r, elems.as_mut_ptr(), elems.len() as _, NONE)
            }
            ir::Tag::Cast => {
                // cast just panics here right now when the cast is invalid because cast checks aren't implemented
                // anywhere before.
                // IR should probably just have different types of casts like in LLVM. 
                // (reinterpret, trunc, extend, float to int, int to float, etc.)
                let (val, origin) = get_ref_and_type(&instructions, data.un_op);
                let target = ir.types.get(*ty);
                match target {
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
                    Type::Id(_) | Type::Array(_) => panic!("Invalid cast"),
                    Type::Pointer(_) => {
                        let llvm_target = llvm_ty(ctx, types, &target);
                        match origin {
                            Type::Pointer(_) => LLVMBuildPointerCast(builder, val, llvm_target, NONE),
                            t => panic!("Can't cast from non-pointer type {t} to pointer")
                        }
                    }
                    Type::Enum(_variants) => {
                        //TODO: int to enum casts
                        panic!("Enum casts unsupported")
                    }
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
                if *ir.types.get(*ty) == Type::Prim(Primitive::Unit) {
                    LLVMGetUndef(LLVMVoidTypeInContext(ctx))
                } else {
                    let phi = LLVMBuildPhi(builder, table_ty(*ty), NONE);
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