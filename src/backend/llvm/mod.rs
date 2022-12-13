use llvm::{core::*, prelude::*, LLVMRealPredicate::*, LLVMIntPredicate::*, LLVMModule};
use crate::{
    dmap::{self, DHashMap},
    types::{Primitive, Layout},
    BackendStats,
    ir::{self, types::{IrType, TypeRef}, Tag}, 
    resolve::{types::{ResolvedTypeDef, Type},
    const_val::ConstVal, self},
    backend::llvm::types::Numeric
};
use std::{ffi, ptr, ops::{Deref, DerefMut}, sync::atomic::Ordering, io::Write, time::Instant};

pub mod output;
mod types;

use types::*;

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
        .map(|(_, ty)| {
            match ty {
                ResolvedTypeDef::Struct(def) => {
                    if def.generic_count() != 0 { return TypeInstance::Generic(dmap::new()); }
                    let (ty, offsets) = struct_ty(ctx, def, module, &[]);
                    TypeInstance::Simple(ty, offsets)
                }
                ResolvedTypeDef::Enum(def) => {
                    // TODO: enums with data
                    if def.generic_count == 0 {
                        TypeInstance::Simple(int_from_variant_count(ctx, def.variants.len()), vec![])
                    } else {
                        TypeInstance::Generic(dmap::new())
                    }
                }
            }
        })
        .collect::<Vec<_>>();

    let type_creation_time = start_time.elapsed();

    // define function headers
    let start_time = Instant::now();

    let funcs = module.funcs.iter().enumerate()
        .map(|(i, func)| {
            let ir_func = &module.funcs[i];
            let (ret, mut params) = if ir_func.ir.is_some() {
                let ret = llvm_global_ty(ctx, &func.return_type, module, &mut types);
                let params = func.params.iter()
                    .map(|(_name, ty)| llvm_global_ty(ctx, ty, module, &mut types))
                    .collect::<Vec<_>>();
                (ret, params)
            } else {
                let ret = llvm_global_ty(ctx, &func.return_type, module, &mut types);
                let params = func.params.iter()
                    .map(|(_name, ty)| llvm_global_ty(ctx, ty, module, &mut types))
                    .collect::<Vec<_>>();
                (ret, params)
            };
            
            
            let varargs = llvm_bool(func.varargs);
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
        add_global(ctx, llvm_module, llvm_global_ty(ctx, ty, module, &mut types), name, val)
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
    let blocks = ir.blocks.iter()
        .map(|_| LLVMAppendBasicBlockInContext(ctx, llvm_func, NONE) )
        .collect::<Vec<_>>();

    let mut instructions = Vec::new();

    let get_ref_and_type_ptr = |instructions: &[LLVMValueRef], r: ir::Ref| -> (Option<LLVMValueRef>, IrType) {
        if let Some(val) = r.into_val() {
            match val {
                ir::RefVal::True | ir::RefVal::False => (
                    Some(LLVMConstInt(LLVMInt1TypeInContext(ctx), (val == ir::RefVal::True) as _, FALSE)),
                    IrType::Primitive(Primitive::Bool)
                ),
                ir::RefVal::Unit => (
                    None,
                    IrType::Primitive(Primitive::Unit)
                ),
                ir::RefVal::Undef => panic!("Tried to use an undefined IR value. This is an internal compiler error."),
            }
        } else {
            let i = r.into_ref().unwrap() as usize;
            let tag = ir.inst[i].tag;
            debug_assert!(!tag.is_untyped(), "Tried to get type of untyped instruction {tag:?}");
            debug_assert!(tag.is_usable(), "Tried to get value of unusable instruction {tag:?}");
            
            let r = instructions[i];
            let ty = ir.types[ir.inst[i].ty];
            ((r != ptr::null_mut()).then_some(r), ty)
        }
    };
    let get_ref_and_type = |instructions: &[LLVMValueRef], r: ir::Ref| get_ref_and_type_ptr(instructions, r);
    let get_ref = |instructions: &[LLVMValueRef], r: ir::Ref| {
        if let Some(val) = r.into_val() {
            match val {
                ir::RefVal::True | ir::RefVal::False =>
                    Some(LLVMConstInt(LLVMInt1TypeInContext(ctx), (val == ir::RefVal::True) as _, FALSE)),
                ir::RefVal::Unit => None,
                ir::RefVal::Undef => panic!("Tried to use an undefined IR value. This is an internal compiler error."),
            }
        } else {
            let i = r.into_ref().unwrap() as usize;
            debug_assert!(ir.inst[i].tag.is_usable());
            let r = instructions[i];
            
            (!r.is_null()).then_some(r)
        }
    };


    let table_ty = |ty: TypeRef, types: &mut [TypeInstance]| {
        let info = ir.types[ty];
        llvm_ty(ctx, module, &ir.types, types, info)
    };
    
    let info_to_num = |info: IrType| {
        match info {
            IrType::Primitive(p) => Numeric::from(p),
            t => panic!("Invalid type for int/float operation: {t:?}")
        }
    };
    let float_or_int = |ty: TypeRef| info_to_num(ir.types[ty]);

    for (i, inst) in ir.inst.iter().enumerate() {
        if crate::LOG.load(Ordering::Relaxed) {
            print!("Generating %{i} = {:?} ->", inst);
            std::io::stdout().flush().unwrap();
        }
        let &ir::Instruction { tag, data, ty, used: _ } = inst;
        let val: LLVMValueRef = match tag {
            ir::Tag::BlockBegin => {
                LLVMPositionBuilderAtEnd(builder, blocks[data.int32 as usize]);
                ptr::null_mut()
            }
            ir::Tag::Ret => {
                let (r, _) = get_ref_and_type(&instructions, data.un_op);
                if let Some(r) = r {
                    LLVMBuildRet(builder, r)
                } else {
                    LLVMBuildRetVoid(builder)
                }
            }
            ir::Tag::RetUndef => {
                if is_resolved_void_type(&func.return_type) {
                    LLVMBuildRetVoid(builder)
                } else {
                    let val = LLVMGetUndef(llvm_global_ty(ctx, &func.return_type, module, types));
                    LLVMBuildRet(builder, val)
                }
            }
            ir::Tag::Param => {
                let layout = func.params[data.int32 as usize].1.layout(|id| &module.types[id.idx()].1, &[]);
                let llvm_ty = llvm_global_ty(ctx, &func.params[data.int32 as usize].1, module, types);
                let param_var = LLVMBuildAlloca(builder, llvm_ty, NONE);
                LLVMSetAlignment(param_var, layout.alignment as _);
                let val = LLVMGetParam(llvm_func, data.int32);
                LLVMBuildStore(builder, val, param_var);
                param_var
            }
            ir::Tag::Uninit => {
                let llvm_ty = llvm_ty(ctx, module, &ir.types, types, ir.types[inst.ty]);
                LLVMGetUndef(llvm_ty)
            }
            ir::Tag::Int => LLVMConstInt(table_ty(ty, types), data.int, FALSE),
            ir::Tag::LargeInt => {
                let mut bytes = [0; 16];
                bytes.copy_from_slice(&ir.extra[data.extra as usize .. data.extra as usize + 16]);
                let num = u128::from_le_bytes(bytes);
                let words = [(num >> 64) as u64, (num as u64)];
                LLVMConstIntOfArbitraryPrecision(table_ty(ty, types), 2, words.as_ptr())
            }
            ir::Tag::Float => LLVMConstReal(table_ty(ty, types), data.float),
            ir::Tag::Func
            | ir::Tag::TraitFunc
            | ir::Tag::Type
            | ir::Tag::Trait
            | ir::Tag::LocalType
            | ir::Tag::Module
            => ptr::null_mut(), // should never be used in runtime code
            ir::Tag::Decl => {
                let layout = ir.types[data.ty].layout(&ir.types, |id| &module.types[id.idx()].1);
                if layout.size == 0 {
                    ptr::null_mut()
                } else {
                    let ptr = LLVMBuildAlloca(builder, table_ty(data.ty, types), NONE);
                    LLVMSetAlignment(ptr, layout.alignment as u32);
                    ptr
                }
            }
            ir::Tag::Load => {
                let (val, ty) = get_ref_and_type(&instructions, data.un_op);
                if let Some(val) = val {
                    let IrType::Ptr(inner) = ty else {
                        panic!("Invalid IR, loading non-pointer type: {ty:?}, ref: {:?}", data.un_op);
                    };
                    let pointee_ty = llvm_ty(ctx, module, &ir.types, types, ir.types[inner]);
                    LLVMBuildLoad2(builder, pointee_ty, val, NONE)
                } else {
                    ptr::null_mut()
                }
            }
            ir::Tag::Store => {
                let (val, _) = get_ref_and_type(&instructions, data.bin_op.1);
                if let Some(val) = val {
                    if let Some(ptr) = get_ref(&instructions, data.bin_op.0) {
                        LLVMBuildStore(builder, val, ptr);
                    }
                }
                ptr::null_mut()
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
                let mut args = (0..data.extra_len.1 as usize).filter_map(|i| {
                    r_bytes.copy_from_slice(&ir.extra[begin + 8 + 4*i..begin + 8 + 4*(i+1)]);
                    get_ref(&instructions, ir::Ref::from_bytes(r_bytes))
                }).collect::<Vec<_>>();
                LLVMBuildCall2(builder, llvm_func_ty, llvm_func, args.as_mut_ptr(), args.len() as u32, NONE)
            }
            ir::Tag::Neg => {
                if let Some(r) = get_ref(&instructions, data.un_op) {
                    if float_or_int(ty).float() {
                        LLVMBuildFNeg(builder, r, NONE)
                    } else {
                        LLVMBuildNeg(builder, r, NONE)
                    }
                } else {
                    ptr::null_mut()
                }
            }
            ir::Tag::Not => {
                get_ref(&instructions, data.un_op).map_or(ptr::null_mut(), |r| LLVMBuildNot(builder, r, NONE))
            }
            ir::Tag::Global => {
                globals[data.global_symbol.idx()]
            }
            ir::Tag::Add | ir::Tag::Sub | ir::Tag::Mul | ir::Tag::Div | ir::Tag::Mod | ir::Tag::Or | ir::Tag::And => {
                // can unwrap here because these operations don't support zero-sized types:
                let l = get_ref(&instructions, data.bin_op.0).unwrap();
                let r = get_ref(&instructions, data.bin_op.1).unwrap();
                
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
            ir::Tag::Eq | ir::Tag::NE => {
                let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                let r = get_ref(&instructions, data.bin_op.1);

                if let (Some(l), Some(r)) = (l, r) {
                    let is_enum_ty = || {
                        if let IrType::Id(id, _) = ty {
                            matches!(module.types[id.idx()].1, ResolvedTypeDef::Enum(_))
                        } else { false }
                    };
    
                    if matches!(ty, IrType::Primitive(Primitive::Bool)) 
                    || is_enum_ty() || info_to_num(ty).int() {
                        LLVMBuildICmp(builder, if tag == ir::Tag::Eq {LLVMIntEQ} else {LLVMIntNE}, l, r, NONE)
                    } else {
                        LLVMBuildFCmp(builder, if tag == ir::Tag::Eq {LLVMRealUEQ} else {LLVMRealUNE}, l, r, NONE)
                    }
                } else {
                    ptr::null_mut()
                }
            }
            // TODO: operator short circuiting
            ir::Tag::LT => {
                let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                let l = l.unwrap();
                let r = get_ref(&instructions, data.bin_op.1).unwrap();
                
                match info_to_num(ty) {
                    Numeric::Float(_) => LLVMBuildFCmp(builder, LLVMRealOLT, l, r, NONE),
                    Numeric::Int(s, _) => LLVMBuildICmp(builder, if s { LLVMIntSLT } else { LLVMIntULT }, l, r, NONE),
                }
            }
            ir::Tag::GT => {
                let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                let l = l.unwrap();
                let r = get_ref(&instructions, data.bin_op.1).unwrap();
                
                match info_to_num(ty) {
                    Numeric::Float(_) => LLVMBuildFCmp(builder, LLVMRealOGT, l, r, NONE),
                    Numeric::Int(s, _) => LLVMBuildICmp(builder, if s { LLVMIntSGT } else { LLVMIntUGT }, l, r, NONE),
                }
            }
            ir::Tag::LE => {
                let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                let l = l.unwrap();
                let r = get_ref(&instructions, data.bin_op.1).unwrap();
                
                match info_to_num(ty) {
                    Numeric::Float(_) => LLVMBuildFCmp(builder, LLVMRealOLE, l, r, NONE),
                    Numeric::Int(s, _) => LLVMBuildICmp(builder, if s { LLVMIntSLE } else { LLVMIntULE }, l, r, NONE),
                }
            }
            ir::Tag::GE => {
                let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                let l = l.unwrap();
                let r = get_ref(&instructions, data.bin_op.1).unwrap();
                
                match info_to_num(ty) {
                    Numeric::Float(_) => LLVMBuildFCmp(builder, LLVMRealOGT, l, r, NONE),
                    Numeric::Int(s, _) => LLVMBuildICmp(builder, if s { LLVMIntSGE } else { LLVMIntUGE }, l, r, NONE),
                }
            }
            ir::Tag::Member => {
                let (r, origin_ty) = get_ref_and_type(&instructions, data.bin_op.0);
                if let Some(r) = r {     
                    let IrType::Ptr(pointee) = origin_ty else {
                        panic!("Tried to get member of non-pointer type {origin_ty:?}")
                    };

                    let (idx, idx_ty) = match ir.types[pointee] {
                        IrType::Id(id, generics) => {
                            let inst = ir.inst[data.bin_op.1.into_ref().unwrap() as usize];
                            assert_eq!(inst.tag, Tag::Int);
                            let member = inst.data.int;

                            let generics: Vec<_> = generics.iter()
                                .map(|ty| ir.types[ty].as_resolved_type(&ir.types).unwrap())
                                .collect();
                            let (_, offsets) = get_id_ty(id, &generics, ctx, module, types);
                            
                            let ty = LLVMInt32TypeInContext(ctx);
                            (LLVMConstInt(ty, offsets[member as usize] as u64, FALSE), ty)
                        }
                        IrType::Tuple(members) => {
                            let inst = ir.inst[data.bin_op.1.into_ref().unwrap() as usize];
                            assert_eq!(inst.tag, Tag::Int);
                            let member = inst.data.int;

                            // calculate layout of all members before the one is accessed
                            // to find out the offset of the indexed element
                            let mut layout = Layout::EMPTY;
                            for i in 0..member {
                                layout.accumulate(
                                    ir.types[members.nth(i as _)]
                                        .layout(&ir.types, |id| &module.types[id.idx()].1)
                                );
                            }
                            let ty = LLVMInt32TypeInContext(ctx);
                            (LLVMConstInt(ty, layout.size, FALSE), ty)
                        }
                        _ => {
                            let (idx, idx_ty) = get_ref_and_type(&instructions, data.bin_op.1);
                            (idx.unwrap(), llvm_ty(ctx, module, &ir.types, types, idx_ty))
                        }
                    };

                    let mut elems = [LLVMConstInt(idx_ty, 0, FALSE), idx];
                    let pointee_ty = llvm_ty(ctx, module, &ir.types, types, ir.types[pointee]);
                    LLVMBuildInBoundsGEP2(builder, pointee_ty, r, elems.as_mut_ptr(), elems.len() as _, NONE)
                } else {
                    std::ptr::null_mut()
                }
            }
            ir::Tag::Value => {
                if let Some(r) = get_ref(&instructions,  data.ref_int.0) {
                    LLVMBuildExtractValue(builder, r, data.ref_int.1, NONE)
                } else {
                    ptr::null_mut()
                }
            }
            ir::Tag::Cast => {
                // cast just panics here right now when the cast is invalid because cast checks aren't implemented
                // anywhere before.
                // IR should probably just have different types of casts like in LLVM. 
                // (reinterpret, trunc, extend, float to int, int to float, etc.)
                let (val, origin) = get_ref_and_type(&instructions, data.un_op);
                let val = val.unwrap(); // casts from zero assumed to be impossible
                let target = ir.types[ty];
                cast(val, origin, target, builder, ctx, module, ir, types)
            }
            ir::Tag::Goto => {
                let block_inst = ir.inst[ir.blocks[data.int32 as usize] as usize];
                debug_assert_eq!(block_inst.tag, ir::Tag::BlockBegin);
                LLVMBuildBr(builder, blocks[block_inst.data.int32 as usize])
            }
            ir::Tag::Branch => {
                let mut bytes = [0; 4];
                let begin = data.ref_int.1 as usize;
                bytes.copy_from_slice(&ir.extra[begin .. begin+4]);
                let then = u32::from_le_bytes(bytes);
                bytes.copy_from_slice(&ir.extra[begin+4 .. begin+8]);
                let else_ = u32::from_le_bytes(bytes);


                let cond = get_ref(&instructions, data.ref_int.0).unwrap();

                LLVMBuildCondBr(builder, cond, blocks[then as usize], blocks[else_ as usize])
            }
            ir::Tag::Phi => {
                let layout = ir.types[ty].layout(&ir.types, |id| &module.types[id.idx()].1);
                if layout.size == 0 {
                    ptr::null_mut()
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
                        LLVMAddIncoming(phi, &mut get_ref(&instructions, r).unwrap(), &mut block, 1);
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
                    let val = val.unwrap(); // TODO: this might actually be zero-sized
                    asm_values.push(val);
                    asm_types.push(llvm_ty(ctx, module, &ir.types, types, ty));
                }

                inline_asm(std::str::from_utf8_unchecked(str_bytes), ctx, builder, &asm_values, &mut asm_types)
            }
        };
        if crate::LOG.load(Ordering::Relaxed) {
            if val.is_null() {
                println!("null");
            } else {
                let cstr = val_str(val);
                println!("{cstr:?}");
            }
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
    if b { TRUE } else { FALSE }
}

fn val_str(val: LLVMValueRef) -> ffi::CString {
    unsafe { ffi::CString::from_raw(LLVMPrintValueToString(val)) }
}

unsafe fn cast(val: LLVMValueRef, origin: IrType, target: IrType, builder: LLVMBuilderRef, ctx: LLVMContextRef, module: &ir::Module, ir: &ir::FunctionIr, types: &mut [TypeInstance]) -> LLVMValueRef {
    match target {
        // pointer to int
        IrType::Primitive(Primitive::U64) if matches!(origin, IrType::Ptr(_)) => {
            let llvm_target = llvm_ty(ctx, module, &ir.types, types, target);
            LLVMBuildPtrToInt(builder, val, llvm_target, NONE)
        }
        IrType::Primitive(target) => {
            //TODO: enum to int casts
            match origin {
                IrType::Primitive(origin) => {
                    let origin = Numeric::from(origin);
                    let target_num = Numeric::from(target);
                    let llvm_target = llvm_primitive_ty(ctx, target);
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
        IrType::Id(_, _) | IrType::Array(_, _) | IrType::Tuple(_) => panic!("Invalid cast"),
        IrType::Ptr(_) => {
            let llvm_target = llvm_ty(ctx, module, &ir.types, types, target);
            match origin {
                IrType::Ptr(_) => LLVMBuildPointerCast(builder, val, llvm_target, NONE),
                // int to ptr
                IrType::Primitive(Primitive::U64) => LLVMBuildIntToPtr(builder, val, llvm_target, NONE),
                t => panic!("Can't cast from non-pointer type {t:?} to pointer")
            }
        }
        IrType::Ref(_) => unreachable!()
    }
}

fn is_resolved_void_type(ty: &Type) -> bool {
    matches!(ty, resolve::types::Type::Prim(Primitive::Unit | Primitive::Never))
}

enum TypeInstance {
    Simple(LLVMTypeRef, Vec<u32>),
    Generic(DHashMap<Vec<Type>, (LLVMTypeRef, Vec<u32>)>),
}

// returns the constant or None in case of a zero sized type
unsafe fn add_global(
    ctx: LLVMContextRef, module: LLVMModuleRef, ty: LLVMTypeRef, name: &str, val: &Option<ConstVal>
) -> Option<LLVMValueRef> {
    let c_name = ffi::CString::new(name).unwrap();
    let global = LLVMAddGlobal(module, ty, c_name.as_ptr());
    LLVMSetInitializer(global, val.as_ref().map_or_else(|| Some(LLVMGetUndef(ty)), |val| gen_const(ctx, ty, val))?);
    Some(global)
}

unsafe fn gen_const(ctx: LLVMContextRef, ty: LLVMTypeRef, val: &ConstVal) -> Option<LLVMValueRef> {
    Some(match val {
        ConstVal::Invalid => LLVMGetUndef(ty),
        ConstVal::Unit => return None,
        &ConstVal::Int(_, int) => {
            let unsigned_int = if int < 0 { (-int) as u128 } else { int as u128 };
            LLVMConstInt(ty, u64::try_from(unsigned_int).expect("TODO: large global ints"), llvm_bool(int < 0))
        }
        ConstVal::Float(_, _float) => todo!("Float globals"),
        ConstVal::String(s) => LLVMConstStringInContext(ctx, s.as_ptr().cast(), s.len() as u32, FALSE),
        ConstVal::EnumVariant(_val) => todo!("static enum values"),
        &ConstVal::Bool(b) => LLVMConstInt(LLVMInt1TypeInContext(ctx), b as _, FALSE),
    })
}
