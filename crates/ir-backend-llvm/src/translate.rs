use std::{collections::VecDeque, ffi::CString, io::Write, ptr};

use ir::{BlockIndex, ConstValue, IrType, IrTypes, TypeRefs};
use llvm_sys::{
    core::{
        self, LLVMAddFunction, LLVMAddGlobal, LLVMAddIncoming, LLVMBuildAdd, LLVMBuildAlloca,
        LLVMBuildAnd, LLVMBuildBr, LLVMBuildCall2, LLVMBuildCondBr, LLVMBuildExtractValue,
        LLVMBuildFAdd, LLVMBuildFCmp, LLVMBuildFDiv, LLVMBuildFMul, LLVMBuildFNeg, LLVMBuildFRem,
        LLVMBuildFSub, LLVMBuildGlobalStringPtr, LLVMBuildICmp, LLVMBuildInBoundsGEP2,
        LLVMBuildIntCast2, LLVMBuildLoad2, LLVMBuildMul, LLVMBuildNeg, LLVMBuildNot, LLVMBuildOr,
        LLVMBuildPhi, LLVMBuildRet, LLVMBuildRetVoid, LLVMBuildSDiv, LLVMBuildSRem, LLVMBuildStore,
        LLVMBuildSub, LLVMBuildUDiv, LLVMBuildURem, LLVMConstInt, LLVMConstIntOfArbitraryPrecision,
        LLVMConstReal, LLVMFunctionType, LLVMGetEnumAttributeKindForName, LLVMGetParam,
        LLVMGetUndef, LLVMInt1TypeInContext, LLVMInt32TypeInContext, LLVMInt8TypeInContext,
        LLVMPointerTypeInContext, LLVMPositionBuilderAtEnd, LLVMPrintValueToString,
        LLVMSetInitializer, LLVMVoidTypeInContext,
    },
    prelude::{LLVMBuilderRef, LLVMContextRef, LLVMModuleRef, LLVMTypeRef, LLVMValueRef},
    LLVMIntPredicate, LLVMRealPredicate,
};

use crate::{llvm_bool, Error, FALSE, NONE};

pub unsafe fn add_function(
    ctx: LLVMContextRef,
    llvm_module: LLVMModuleRef,
    function: &ir::Function,
    attribs: &Attribs,
) -> Result<(LLVMValueRef, LLVMTypeRef), Error> {
    let return_ty = llvm_ty(ctx, function.return_type, &function.types)
        .unwrap_or_else(|| LLVMVoidTypeInContext(ctx));
    let mut params: Vec<_> = function
        .params
        .iter()
        .filter_map(|ty| llvm_ty(ctx, function.types[ty], &function.types))
        .collect();
    let llvm_func_ty = LLVMFunctionType(
        return_ty,
        params.as_mut_ptr(),
        params.len() as _,
        llvm_bool(function.varargs),
    );
    let name = CString::from_vec_with_nul(
        // HACK: temporary prefix until proper name mangling is implemented
        if function.ir.is_some() && function.name != "main" && function.name != "_start" {
            format!("__eye__{}\0", function.name).into_bytes()
        } else {
            format!("{}\0", function.name).into_bytes()
        },
    )
    .map_err(|_| Error::NulByte)?;
    let llvm_func = LLVMAddFunction(llvm_module, name.as_ptr(), llvm_func_ty);
    // TODO: noreturn attribute in ir
    if false {
        let noreturn = core::LLVMCreateEnumAttribute(ctx, attribs.noreturn, 0);
        core::LLVMAddAttributeAtIndex(llvm_func, -1i32 as u32, noreturn);
    }
    Ok((llvm_func, llvm_func_ty))
}

pub unsafe fn add_global(
    ctx: LLVMContextRef,
    llvm_module: LLVMModuleRef,
    name: &str,
    types: &IrTypes,
    ty: IrType,
    value: &ConstValue,
) -> Result<LLVMValueRef, Error> {
    let Some(ty) = llvm_ty(ctx, ty, &types) else {
        return Ok(ptr::null_mut());
    };
    let name = CString::new(name.to_owned()).map_err(|_| Error::NulByte)?;
    let global = LLVMAddGlobal(llvm_module, ty, name.as_ptr());
    let val = const_val(value, ty).unwrap_or_else(|| LLVMGetUndef(ty));
    LLVMSetInitializer(global, val);
    Ok(global)
}

pub unsafe fn function(
    ctx: LLVMContextRef,
    llvm_funcs: &[(LLVMValueRef, LLVMTypeRef)],
    globals: &[LLVMValueRef],
    llvm_func: LLVMValueRef,
    builder: LLVMBuilderRef,
    function: &ir::Function,
    log: bool,
) -> Result<(), Error> {
    if let Some(ir) = &function.ir {
        build_func(
            function, llvm_funcs, globals, ir, ctx, builder, llvm_func, log,
        );
    }
    Ok(())
}

pub struct Attribs {
    noreturn: u32,
}
impl Attribs {
    pub fn lookup() -> Self {
        fn l(s: &str) -> u32 {
            unsafe { LLVMGetEnumAttributeKindForName(s.as_ptr().cast(), s.len()) }
        }
        Self {
            noreturn: l("noreturn"),
        }
    }
}

/// Converts an ir type to it's corresponding llvm type. Returns `None` if the type was zero-sized
unsafe fn llvm_ty(ctx: LLVMContextRef, ty: IrType, types: &IrTypes) -> Option<LLVMTypeRef> {
    use IrType as T;
    match ty {
        T::I8 | T::U8 => Some(core::LLVMInt8TypeInContext(ctx)),
        T::I16 | T::U16 => Some(core::LLVMInt16TypeInContext(ctx)),
        T::I32 | T::U32 => Some(core::LLVMInt32TypeInContext(ctx)),
        T::I64 | T::U64 => Some(core::LLVMInt64TypeInContext(ctx)),
        T::I128 | T::U128 => Some(core::LLVMInt128TypeInContext(ctx)),
        T::F32 => Some(core::LLVMFloatTypeInContext(ctx)),
        T::F64 => Some(core::LLVMDoubleTypeInContext(ctx)),
        T::U1 => Some(core::LLVMInt1TypeInContext(ctx)),
        T::Unit => None,
        T::Ptr => Some(core::LLVMPointerTypeInContext(ctx, 0)),
        T::Array(elem, size) => Some(core::LLVMArrayType2(
            llvm_ty(ctx, types[elem], types)?,
            size as u64,
        )),
        T::Tuple(elems) => {
            if elems.count == 0 {
                return None;
            }
            let mut types = elems
                .iter()
                .map(|ty| llvm_ty(ctx, types[ty], types))
                .collect::<Option<Vec<_>>>()?;
            Some(core::LLVMStructTypeInContext(
                ctx,
                types.as_mut_ptr(),
                elems.len() as _,
                FALSE,
            ))
        }
    }
}

unsafe fn build_func(
    func: &ir::Function,
    llvm_funcs: &[(LLVMValueRef, LLVMTypeRef)],
    globals: &[LLVMValueRef],
    ir: &ir::FunctionIr,
    ctx: LLVMContextRef,
    builder: LLVMBuilderRef,
    llvm_func: LLVMValueRef,
    log: bool,
) {
    if log {
        println!("Translating function {} to LLVM IR", func.name);
    }

    let mut instructions = vec![ptr::null_mut(); ir.inst.len()];

    // create an LLVM block for each block while also creating a Phi node for each incoming block arg.
    let blocks: Vec<_> = ir
        .blocks()
        .map(|block| {
            let llvm_block = core::LLVMAppendBasicBlockInContext(ctx, llvm_func, NONE);

            let block_args = ir.get_block_args(block);
            LLVMPositionBuilderAtEnd(builder, llvm_block);
            for (i, arg) in block_args.iter().enumerate() {
                if block == ir::BlockIndex::ENTRY {
                    instructions[arg as usize] = LLVMGetParam(llvm_func, i as _);
                } else {
                    let arg_ty = ir.get_ref_ty(ir::Ref::index(arg), &func.types);
                    if let Some(ty) = llvm_ty(ctx, arg_ty, &func.types) {
                        instructions[arg as usize] = LLVMBuildPhi(builder, ty, NONE);
                    }
                }
            }
            llvm_block
        })
        .collect();

    let block_graph = ir::BlockGraph::calculate(ir);

    let i1 = LLVMInt1TypeInContext(ctx);

    let get_ref_and_type_ptr =
        |instructions: &[LLVMValueRef], r: ir::Ref| -> (Option<LLVMValueRef>, IrType) {
            if let Some(val) = r.into_val() {
                match val {
                    ir::RefVal::True | ir::RefVal::False => (
                        Some(LLVMConstInt(i1, (val == ir::RefVal::True) as _, FALSE)),
                        IrType::U1,
                    ),
                    ir::RefVal::Unit => (None, IrType::Unit),
                    ir::RefVal::Undef => panic!(
                        "Tried to use an undefined IR value. This is an internal compiler error."
                    ),
                }
            } else {
                let i = r.into_ref().unwrap() as usize;
                let tag = ir.inst[i].tag;
                debug_assert!(
                    tag.is_usable(),
                    "Tried to get value of unusable instruction {tag:?}"
                );

                let r = instructions[i];
                let ty = func.types[ir.inst[i].ty];
                ((!r.is_null()).then_some(r), ty)
            }
        };
    let get_ref_and_type =
        |instructions: &[LLVMValueRef], r: ir::Ref| get_ref_and_type_ptr(instructions, r);
    let get_ref = |instructions: &[LLVMValueRef], r: ir::Ref| {
        if let Some(val) = r.into_val() {
            match val {
                ir::RefVal::True | ir::RefVal::False => Some(LLVMConstInt(
                    LLVMInt1TypeInContext(ctx),
                    (val == ir::RefVal::True) as _,
                    FALSE,
                )),
                ir::RefVal::Unit => None,
                ir::RefVal::Undef => panic!(
                    "Tried to use an undefined IR value. This is an internal compiler error."
                ),
            }
        } else {
            let i = r.into_ref().unwrap() as usize;
            debug_assert!(ir.inst[i].tag.is_usable());
            let r = instructions[i];

            (!r.is_null()).then_some(r)
        }
    };

    let table_ty = |ty: ir::TypeRef| llvm_ty(ctx, func.types[ty], &func.types);

    let mut queued_blocks = vec![false; ir.blocks().len()];
    let mut block_queue = VecDeque::from([BlockIndex::ENTRY]);
    queued_blocks[BlockIndex::ENTRY.idx() as usize] = true;

    for block in block_graph.postorder().iter().copied().rev() {
        let llvm_block = blocks[block.idx() as usize];

        let mut handle_successor = |ir: &ir::FunctionIr,
                                    instructions: &[LLVMValueRef],
                                    successor: ir::BlockIndex,
                                    extra_idx: usize| {
            for (block_arg_idx, extra_idx) in ir
                .get_block_args(successor)
                .iter()
                .zip((extra_idx..).step_by(4))
            {
                let r = ir::Ref::from_bytes(ir.extra[extra_idx..extra_idx + 4].try_into().unwrap());
                if let Some(mut llvm_val) = get_ref(&instructions, r) {
                    let phi = instructions[block_arg_idx as usize];
                    if !phi.is_null() {
                        let mut block = llvm_block;
                        LLVMAddIncoming(phi, &mut llvm_val, &mut block, 1);
                    }
                }
            }
            if !queued_blocks[successor.idx() as usize] {
                queued_blocks[successor.idx() as usize] = true;
                block_queue.push_back(successor);
            }
        };

        LLVMPositionBuilderAtEnd(builder, llvm_block);
        for (i, inst) in ir.get_block(block) {
            if log {
                print!("Generating %{i} = {:?} ->", inst);
                std::io::stdout().flush().unwrap();
            }
            let ir::Instruction { tag, data, ty } = inst;
            let val: LLVMValueRef = match tag {
                ir::Tag::Nothing => ptr::null_mut(),
                ir::Tag::BlockArg => unreachable!(),
                ir::Tag::Ret => {
                    let value = data.un_op;
                    if value == ir::Ref::UNDEF {
                        if let Some(ty) = llvm_ty(ctx, func.return_type, &func.types) {
                            let val = LLVMGetUndef(ty);
                            LLVMBuildRet(builder, val)
                        } else {
                            LLVMBuildRetVoid(builder)
                        }
                    } else {
                        let (r, ty) = get_ref_and_type(&instructions, data.un_op);
                        if let Some(r) = r.and_then(|r| (!matches!(ty, IrType::Unit)).then_some(r))
                        {
                            LLVMBuildRet(builder, r)
                        } else {
                            LLVMBuildRetVoid(builder)
                        }
                    }
                }
                ir::Tag::Global => globals[data.global.0 as usize],
                ir::Tag::Int => LLVMConstInt(table_ty(ty).unwrap(), data.int, FALSE),
                ir::Tag::LargeInt => {
                    let mut bytes = [0; 16];
                    bytes.copy_from_slice(&ir.extra[data.extra as usize..data.extra as usize + 16]);
                    let num = u128::from_le_bytes(bytes);
                    let words = [(num >> 64) as u64, (num as u64)];
                    LLVMConstIntOfArbitraryPrecision(table_ty(ty).unwrap(), 2, words.as_ptr())
                }
                ir::Tag::Float => LLVMConstReal(table_ty(ty).unwrap(), data.float),
                ir::Tag::Decl => {
                    if let Some(ty) = table_ty(data.ty) {
                        let ptr = LLVMBuildAlloca(builder, ty, NONE);
                        ptr
                    } else {
                        // return a null pointer if a declaration has a zero-sized type
                        core::LLVMConstPointerNull(LLVMPointerTypeInContext(ctx, 0))
                    }
                }
                ir::Tag::Load => {
                    let val = get_ref(&instructions, data.un_op);
                    if let Some(pointee_ty) = llvm_ty(ctx, func.types[ty], &func.types) {
                        let val = val.unwrap();
                        let loaded = LLVMBuildLoad2(builder, pointee_ty, val, NONE);
                        loaded
                    } else {
                        ptr::null_mut()
                    }
                }
                ir::Tag::Store => {
                    let (ptr, val) = data.bin_op();
                    let (val, ty) = get_ref_and_type(&instructions, val);
                    if !func.types.is_zero_sized(ty) {
                        let ptr = get_ref(&instructions, ptr).unwrap();
                        LLVMBuildStore(builder, val.unwrap(), ptr);
                    }
                    ptr::null_mut()
                }
                ir::Tag::String => LLVMBuildGlobalStringPtr(
                    builder,
                    ir.extra.as_ptr().add(data.extra_len.0 as usize).cast(),
                    NONE,
                ),
                ir::Tag::Call => {
                    let begin = data.extra_len.0 as usize;
                    let mut func_id = [0; 8];
                    func_id.copy_from_slice(&ir.extra[begin..begin + 8]);
                    let func_id = u64::from_le_bytes(func_id);
                    let (llvm_func, llvm_func_ty) = llvm_funcs[func_id as usize];

                    let mut r_bytes = [0; 4];
                    let mut args = (0..data.extra_len.1 as usize)
                        .filter_map(|i| {
                            r_bytes.copy_from_slice(
                                &ir.extra[begin + 8 + 4 * i..begin + 8 + 4 * (i + 1)],
                            );
                            get_ref(&instructions, ir::Ref::from_bytes(r_bytes))
                        })
                        .collect::<Vec<_>>();
                    LLVMBuildCall2(
                        builder,
                        llvm_func_ty,
                        llvm_func,
                        args.as_mut_ptr(),
                        args.len() as u32,
                        NONE,
                    )
                }
                ir::Tag::FunctionPtr => {
                    let func_id = data.function();
                    let (llvm_func, _) = llvm_funcs[func_id.0 as usize];
                    llvm_func
                }
                ir::Tag::CallPtr => {
                    let (func_ref, arg_types, args) = data.call_ptr(&ir.extra);
                    let llvm_func = get_ref(&instructions, func_ref).unwrap();
                    let mut args: Vec<_> =
                        args.filter_map(|arg| get_ref(&instructions, arg)).collect();
                    let return_ty = llvm_ty(ctx, func.types[ty], &func.types)
                        .unwrap_or_else(|| LLVMVoidTypeInContext(ctx));
                    let mut param_types: Vec<_> = arg_types
                        .iter()
                        .filter_map(|ty| llvm_ty(ctx, func.types[ty], &func.types))
                        .collect();
                    debug_assert_eq!(args.len(), param_types.len());
                    let func_ty = LLVMFunctionType(
                        return_ty,
                        param_types.as_mut_ptr(),
                        param_types.len() as u32,
                        FALSE,
                    );
                    LLVMBuildCall2(
                        builder,
                        func_ty,
                        llvm_func,
                        args.as_mut_ptr(),
                        args.len() as u32,
                        NONE,
                    )
                }
                ir::Tag::Neg => {
                    let r = get_ref(&instructions, data.un_op).unwrap();
                    match func.types[ty] {
                        t if t.is_int() => LLVMBuildNeg(builder, r, NONE),
                        t if t.is_float() => LLVMBuildFNeg(builder, r, NONE),
                        _ => panic!("invalid type for neg"),
                    }
                }
                ir::Tag::Not => {
                    let r = get_ref(&instructions, data.un_op).unwrap();
                    LLVMBuildNot(builder, r, NONE)
                }
                ir::Tag::Add
                | ir::Tag::Sub
                | ir::Tag::Mul
                | ir::Tag::Div
                | ir::Tag::Rem
                | ir::Tag::Or
                | ir::Tag::And => {
                    // can unwrap here because these operations don't support zero-sized types:
                    let l = get_ref(&instructions, data.bin_op.0).unwrap();
                    let r = get_ref(&instructions, data.bin_op.1).unwrap();

                    match tag {
                        ir::Tag::Add => match func.types[ty] {
                            t if t.is_int() => LLVMBuildAdd(builder, l, r, NONE),
                            t if t.is_float() => LLVMBuildFAdd(builder, l, r, NONE),
                            _ => panic!("invalid type for add"),
                        },
                        ir::Tag::Sub => match func.types[ty] {
                            t if t.is_int() => LLVMBuildSub(builder, l, r, NONE),
                            t if t.is_float() => LLVMBuildFSub(builder, l, r, NONE),
                            _ => panic!("invalid type for sub"),
                        },
                        ir::Tag::Mul => match func.types[ty] {
                            t if t.is_int() => LLVMBuildMul(builder, l, r, NONE),
                            t if t.is_float() => LLVMBuildFMul(builder, l, r, NONE),
                            _ => panic!("invalid type for mul"),
                        },
                        ir::Tag::Div => match func.types[ty] {
                            t if t.is_unsigned_int() => LLVMBuildUDiv(builder, l, r, NONE),
                            t if t.is_signed_int() => LLVMBuildSDiv(builder, l, r, NONE),
                            t if t.is_float() => LLVMBuildFDiv(builder, l, r, NONE),
                            _ => panic!("invalid type for div"),
                        },
                        ir::Tag::Rem => match func.types[ty] {
                            t if t.is_unsigned_int() => LLVMBuildURem(builder, l, r, NONE),
                            t if t.is_signed_int() => LLVMBuildSRem(builder, l, r, NONE),
                            t if t.is_float() => LLVMBuildFRem(builder, l, r, NONE),
                            _ => panic!("invalid type for mod"),
                        },
                        ir::Tag::Or => LLVMBuildOr(builder, l, r, NONE),
                        ir::Tag::And => LLVMBuildAnd(builder, l, r, NONE),
                        _ => unreachable!(),
                    }
                }
                ir::Tag::Eq | ir::Tag::NE => {
                    let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                    let r = get_ref(&instructions, data.bin_op.1);

                    if let (Some(l), Some(r)) = (l, r) {
                        match ty {
                            t if t.is_int() => {
                                let pred = if tag == ir::Tag::Eq {
                                    LLVMIntPredicate::LLVMIntEQ
                                } else {
                                    LLVMIntPredicate::LLVMIntNE
                                };
                                LLVMBuildICmp(builder, pred, l, r, NONE)
                            }
                            t if t.is_float() => {
                                let pred = if tag == ir::Tag::Eq {
                                    LLVMRealPredicate::LLVMRealUEQ
                                } else {
                                    LLVMRealPredicate::LLVMRealUNE
                                };
                                LLVMBuildFCmp(builder, pred, l, r, NONE)
                            }
                            IrType::Ptr => {
                                let pred = if tag == ir::Tag::Eq {
                                    LLVMIntPredicate::LLVMIntEQ
                                } else {
                                    LLVMIntPredicate::LLVMIntNE
                                };
                                LLVMBuildICmp(builder, pred, l, r, NONE)
                            }
                            t => panic!("invalid type for eq/ne: {t:?}"),
                        }
                    } else {
                        ptr::null_mut()
                    }
                }
                ir::Tag::LT => {
                    let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                    let l = l.unwrap();
                    let r = get_ref(&instructions, data.bin_op.1).unwrap();
                    match ty {
                        t if t.is_unsigned_int() => {
                            LLVMBuildICmp(builder, LLVMIntPredicate::LLVMIntULT, l, r, NONE)
                        }
                        t if t.is_signed_int() => {
                            LLVMBuildICmp(builder, LLVMIntPredicate::LLVMIntSLT, l, r, NONE)
                        }
                        t if t.is_float() => {
                            LLVMBuildFCmp(builder, LLVMRealPredicate::LLVMRealOLT, l, r, NONE)
                        }
                        IrType::Ptr => {
                            LLVMBuildICmp(builder, LLVMIntPredicate::LLVMIntULT, l, r, NONE)
                        }
                        t => panic!("invalid type for lt {t:?}"),
                    }
                }
                ir::Tag::GT => {
                    let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                    let l = l.unwrap();
                    let r = get_ref(&instructions, data.bin_op.1).unwrap();
                    match ty {
                        t if t.is_unsigned_int() => {
                            LLVMBuildICmp(builder, LLVMIntPredicate::LLVMIntUGT, l, r, NONE)
                        }
                        t if t.is_signed_int() => {
                            LLVMBuildICmp(builder, LLVMIntPredicate::LLVMIntSGT, l, r, NONE)
                        }
                        t if t.is_float() => {
                            LLVMBuildFCmp(builder, LLVMRealPredicate::LLVMRealOGT, l, r, NONE)
                        }
                        IrType::Ptr => {
                            LLVMBuildICmp(builder, LLVMIntPredicate::LLVMIntUGT, l, r, NONE)
                        }
                        t => panic!("invalid type for gt {t:?}"),
                    }
                }
                ir::Tag::LE => {
                    let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                    let l = l.unwrap();
                    let r = get_ref(&instructions, data.bin_op.1).unwrap();
                    match ty {
                        t if t.is_unsigned_int() => {
                            LLVMBuildICmp(builder, LLVMIntPredicate::LLVMIntULE, l, r, NONE)
                        }
                        t if t.is_signed_int() => {
                            LLVMBuildICmp(builder, LLVMIntPredicate::LLVMIntSLE, l, r, NONE)
                        }
                        t if t.is_float() => {
                            LLVMBuildFCmp(builder, LLVMRealPredicate::LLVMRealOLE, l, r, NONE)
                        }
                        IrType::Ptr => {
                            LLVMBuildICmp(builder, LLVMIntPredicate::LLVMIntULE, l, r, NONE)
                        }
                        t => panic!("invalid type for le: {t:?}"),
                    }
                }
                ir::Tag::GE => {
                    let (l, ty) = get_ref_and_type(&instructions, data.bin_op.0);
                    let l = l.unwrap();
                    let r = get_ref(&instructions, data.bin_op.1).unwrap();
                    match ty {
                        t if t.is_unsigned_int() => {
                            LLVMBuildICmp(builder, LLVMIntPredicate::LLVMIntUGE, l, r, NONE)
                        }
                        t if t.is_signed_int() => {
                            LLVMBuildICmp(builder, LLVMIntPredicate::LLVMIntSGE, l, r, NONE)
                        }
                        t if t.is_float() => {
                            LLVMBuildFCmp(builder, LLVMRealPredicate::LLVMRealOGE, l, r, NONE)
                        }
                        IrType::Ptr => {
                            LLVMBuildICmp(builder, LLVMIntPredicate::LLVMIntUGE, l, r, NONE)
                        }
                        t => panic!("invalid type for ge: {t:?}"),
                    }
                }
                ir::Tag::Xor => {
                    let (l, r) = inst.data.bin_op();
                    core::LLVMBuildXor(
                        builder,
                        get_ref(&instructions, l).unwrap(),
                        get_ref(&instructions, r).unwrap(),
                        NONE,
                    )
                }
                ir::Tag::Rol | ir::Tag::Ror => {
                    todo!("implement Rol/Ror")
                    /*
                    let (l, r) = inst.data.bin_op();
                    llvm_sys::core::LLVMGetIntrinsicDeclaration(llvm_module, , , )
                    core::LLVMBuildXor(
                        builder,
                        get_ref(&instructions, l).unwrap(),
                        get_ref(&instructions, r).unwrap(),
                        NONE,
                    )
                    */
                }
                ir::Tag::MemberPtr => {
                    let (ptr, extra_idx) = data.ref_int;
                    let i = extra_idx as usize;
                    let elem_types = TypeRefs::from_bytes(ir.extra[i..i + 8].try_into().unwrap());
                    let elem_idx = u32::from_le_bytes(ir.extra[i + 8..i + 12].try_into().unwrap());

                    let offset = ir::offset_in_tuple(elem_types, elem_idx, &func.types);

                    let i8_ty = LLVMInt8TypeInContext(ctx);
                    if let Some(llvm_ptr) = get_ref(&instructions, ptr) {
                        let mut offset = LLVMConstInt(LLVMInt32TypeInContext(ctx), offset, FALSE);
                        LLVMBuildInBoundsGEP2(builder, i8_ty, llvm_ptr, &mut offset, 1, NONE)
                    } else {
                        ptr::null_mut()
                    }
                }
                ir::Tag::MemberValue => {
                    let (ptr, idx) = data.ref_int;
                    if let Some(val) = get_ref(&instructions, ptr) {
                        // extract_value_from_byte_array(ctx, builder, &func.types, val, elem_types, idx)
                        LLVMBuildExtractValue(builder, val, idx, NONE)
                    } else {
                        ptr::null_mut()
                    }
                    /*
                    if let (Some(r), r_ty) = get_ref_and_type(&instructions,  data.ref_int.0) {
                    match r_ty {
                    IrType::Id(id, generics) => {
                    let generics: Vec<_> = generics.iter()
                    .map(|ty| ir.types[ty].as_resolved_type(&ir.types))
                    .collect();
                    let (_, offsets) = get_id_ty(id, &generics, ctx, module, types);
                    let OffsetsRef::Struct(offsets) = offsets else { panic!("invalid argument for Value") };
                    let offset = offsets[data.ref_int.1 as usize];
                    extract_value_from_byte_array(ctx, module, types, builder, &ir.types, r, r_ty,
                    offset, ir.types[ty])
                    }
                    IrType::Tuple(elems) => {
                    // TODO: cache offsets
                    let mut layout = Layout::EMPTY;
                    for elem in elems.iter().take(data.ref_int.1 as usize) {
                    layout.accumulate(ir.types[elem].layout(&ir.types, |id| &module.types[id.idx()].1));
                    println!("{layout:?}");
                    }
                    let elem_align = ir.types[elems.nth(data.ref_int.1)]
                    .layout(&ir.types, |id| &module.types[id.idx()].1)
                    .alignment;
                    let offset = Layout::align(layout.size, elem_align) as u32;
                    extract_value_from_byte_array(ctx, module, types, builder, &ir.types, r, r_ty,
                    offset, ir.types[ty])

                    }
                    IrType::Primitive(_) | IrType::Ptr(_) | IrType::Enum(_)
                    => panic!("invalid argument for Value"),
                    IrType::Array(_, _) => {
                    LLVMBuildExtractValue(builder, r, data.ref_int.1, NONE)
                    }
                    IrType::Const(_) => panic!("invalid const type in LLVM backend"),
                    IrType::Ref(_) => unreachable!(),
                    }
                    } else {
                    ptr::null_mut()
                    }
                    */
                }
                ir::Tag::InsertMember => {
                    let (tuple, idx, member) = data.ref_int_ref(&ir.extra);
                    let tuple = if tuple == ir::Ref::UNDEF {
                        llvm_ty(ctx, func.types[ty], &func.types).map(|ty| LLVMGetUndef(ty))
                    } else {
                        get_ref(&instructions, tuple)
                    };
                    if let Some((tuple, member)) = tuple.and_then(|tuple| {
                        get_ref(&instructions, member).map(|member| (tuple, member))
                    }) {
                        core::LLVMBuildInsertValue(builder, tuple, member, idx, NONE)
                    } else {
                        ptr::null_mut()
                    }
                }
                ir::Tag::ArrayIndex => {
                    let (array_ptr, extra_idx) = data.ref_int;
                    let i = extra_idx as usize;
                    let elem_ty = ir::TypeRef::from_bytes(ir.extra[i..i + 4].try_into().unwrap());
                    let index_ref = ir::Ref::from_bytes(ir.extra[i + 4..i + 8].try_into().unwrap());

                    let ptr = get_ref(&instructions, array_ptr).unwrap();
                    let ty = llvm_ty(ctx, func.types[elem_ty], &func.types).unwrap();
                    let mut indices = [get_ref(&instructions, index_ref).unwrap()];
                    LLVMBuildInBoundsGEP2(
                        builder,
                        ty,
                        ptr,
                        indices.as_mut_ptr(),
                        indices.len() as _,
                        NONE,
                    )
                }
                ir::Tag::CastInt => {
                    let val = get_ref(&instructions, data.un_op);
                    // there are no zero-sized integers so unwraps are fine
                    let val = val.unwrap();
                    let to_ty = func.types[ty];
                    let signed = to_ty.is_signed_int();
                    let target_ty = llvm_ty(ctx, to_ty, &func.types).unwrap();
                    LLVMBuildIntCast2(builder, val, target_ty, llvm_bool(signed), NONE)
                }
                ir::Tag::CastFloat => {
                    let (val, from_ty) = get_ref_and_type(&instructions, data.un_op);
                    // there are no zero-sized floats so unwraps are fine
                    let val = val.unwrap();
                    let to_ty = func.types[ty];
                    let target_ty = llvm_ty(ctx, to_ty, &func.types).unwrap();
                    match (from_ty, to_ty) {
                        (IrType::F32, IrType::F64) => {
                            core::LLVMBuildFPExt(builder, val, target_ty, NONE)
                        }
                        (IrType::F64, IrType::F32) => {
                            core::LLVMBuildFPTrunc(builder, val, target_ty, NONE)
                        }
                        _ => panic!("invalid types for CastFloat"),
                    }
                }
                ir::Tag::CastIntToFloat => {
                    let (val, from_ty) = get_ref_and_type(&instructions, data.un_op);
                    // there are no zero-sized ints/floats so unwraps are fine
                    let val = val.unwrap();
                    let to_ty = func.types[ty];
                    let target_ty = llvm_ty(ctx, to_ty, &func.types).unwrap();
                    if from_ty.is_unsigned_int() {
                        core::LLVMBuildUIToFP(builder, val, target_ty, NONE)
                    } else {
                        core::LLVMBuildSIToFP(builder, val, target_ty, NONE)
                    }
                }
                ir::Tag::CastFloatToInt => {
                    // there are no zero-sized ints/floats so unwraps are fine
                    let val = get_ref(&instructions, data.un_op).unwrap();
                    let to_ty = func.types[ty];
                    let target_ty = llvm_ty(ctx, func.types[ty], &func.types).unwrap();
                    if to_ty.is_unsigned_int() {
                        core::LLVMBuildFPToUI(builder, val, target_ty, NONE)
                    } else {
                        core::LLVMBuildFPToSI(builder, val, target_ty, NONE)
                    }
                }
                ir::Tag::Goto => {
                    let (block, extra_idx) = data.goto();
                    handle_successor(ir, &instructions, block, extra_idx);
                    LLVMBuildBr(builder, blocks[block.idx() as usize])
                }
                ir::Tag::Branch => {
                    let (r, a, b, extra_idx) = data.branch(&ir.extra);
                    // TODO block_args
                    let cond = get_ref(&instructions, r).unwrap();
                    handle_successor(ir, &instructions, a, extra_idx);
                    handle_successor(
                        ir,
                        &instructions,
                        a,
                        extra_idx + 4 * ir.get_block_args(a).count(),
                    );

                    LLVMBuildCondBr(
                        builder,
                        cond,
                        blocks[a.idx() as usize],
                        blocks[b.idx() as usize],
                    )
                }
                /*
                ir::Tag::Phi => {
                    if let Some(ty) = table_ty(ty) {
                        let phi = LLVMBuildPhi(builder, ty, NONE);
                        for (block, r) in inst.data.phi(&ir.extra) {
                            let mut block = blocks[block.idx() as usize];
                            LLVMAddIncoming(
                                phi,
                                &mut get_ref(&instructions, r).unwrap(),
                                &mut block,
                                1,
                            );
                        }
                        phi
                    } else {
                        ptr::null_mut()
                    }
                }
                */
                ir::Tag::IntToPtr => {
                    // no zero-sized integers so unwrapping is fine
                    let val = get_ref(&instructions, data.un_op).unwrap();
                    core::LLVMBuildIntToPtr(builder, val, LLVMPointerTypeInContext(ctx, 0), NONE)
                }
                ir::Tag::PtrToInt => {
                    // no zero-sized integers so unwrapping is fine
                    let val = get_ref(&instructions, data.un_op).unwrap();
                    let ty = llvm_ty(ctx, func.types[ty], &func.types).unwrap();
                    core::LLVMBuildPtrToInt(builder, val, ty, NONE)
                }
                ir::Tag::Asm => {
                    let ir::Data {
                        asm: (extra, str_len, arg_count),
                    } = data;
                    let _str_bytes = &ir.extra[extra as usize..extra as usize + str_len as usize];

                    let expr_base = extra as usize + str_len as usize;
                    let mut asm_values = Vec::with_capacity(arg_count as usize);
                    let mut asm_types = Vec::with_capacity(arg_count as usize);
                    for i in 0..arg_count as usize {
                        let mut arg_bytes = [0; 4];
                        arg_bytes
                            .copy_from_slice(&ir.extra[expr_base + 4 * i..expr_base + 4 * (i + 1)]);
                        let (val, ty) =
                            get_ref_and_type(&instructions, ir::Ref::from_bytes(arg_bytes));
                        let val = val.unwrap(); // TODO: this might actually be zero-sized
                        asm_values.push(val);
                        asm_types.push(llvm_ty(ctx, ty, &func.types));
                    }

                    // inline_asm(std::str::from_utf8_unchecked(str_bytes), ctx, builder, &asm_values, &mut asm_types)
                    todo!("reimplement inline_asm")
                }
            };
            if log {
                if val.is_null() {
                    println!("null");
                } else {
                    let cstr = val_str(val);
                    println!("{cstr:?}");
                }
            }
            instructions[i as usize] = val;
        }
    }
}

unsafe fn const_val(val: &ir::ConstValue, ty: LLVMTypeRef) -> Option<LLVMValueRef> {
    Some(match val {
        ConstValue::Undefined | ConstValue::Unit => return None,
        &ConstValue::Int(int) => LLVMConstInt(ty, int as u64, FALSE),
        &ConstValue::Float(val) => LLVMConstReal(ty, val),
    })
}

fn val_str(val: LLVMValueRef) -> CString {
    unsafe { CString::from_raw(LLVMPrintValueToString(val)) }
}

/*
unsafe fn extract_value_from_byte_array(
    ctx: LLVMContextRef,
    builder: LLVMBuilderRef,
    ir_types: &IrTypes,
    r: LLVMValueRef,
    elem_types: TypeRefs,
    index: u32,
) -> LLVMValueRef {
    let elem_ty = elem_types.nth(index);
    let Some(llvm_elem_ty) = llvm_ty(ctx, ir_types[elem_ty], ir_types) else {
        return ptr::null_mut();
    };
    let mut layout = Layout::EMPTY;
    for elem_ty in elem_types.iter().take(index as usize) {
        let elem_layout = ir::type_layout(ir_types[elem_ty], ir_types);
        layout.accumulate(elem_layout);
    }
    let elem_layout = ir::type_layout(ir_types[elem_ty], ir_types);
    layout.align_for(elem_layout.align);
    let offset = layout.align;
    layout.accumulate(elem_layout);
    // accumulate rest of element types
    for elem_ty in elem_types.iter().skip(index as usize + 1) {
        let elem_layout = ir::type_layout(ir_types[elem_ty], ir_types);
        layout.accumulate(elem_layout);
    }

    let i8_ty = LLVMInt8TypeInContext(ctx);
    let before = LLVMArrayType2(i8_ty, offset.get());
    let after_bytes = layout.size - offset.get() - elem_layout.size;
    let ty = if after_bytes != 0 {
        let after = LLVMArrayType2(i8_ty, after_bytes);
        let mut ty = [before, llvm_elem_ty, after];
        LLVMStructTypeInContext(ctx, ty.as_mut_ptr(), ty.len() as _, FALSE)
    } else {
        let mut ty = [before, llvm_elem_ty];
        LLVMStructTypeInContext(ctx, ty.as_mut_ptr(), ty.len() as _, FALSE)
    };

    let cast_val = LLVMBuildBitCast(builder, r, ty, NONE);
    LLVMSetAlignment(cast_val, layout.align.get() as _);

    LLVMBuildExtractValue(builder, cast_val, 1, NONE)
}
*/
