use std::{ffi::CString, io::Write, ptr};

use ir::{IrType, IrTypes, TypeRefs};
use llvm_sys::{
    core::{
        self, LLVMAddFunction, LLVMAddIncoming, LLVMBuildAdd, LLVMBuildAlloca, LLVMBuildAnd,
        LLVMBuildBr, LLVMBuildCall2, LLVMBuildCondBr, LLVMBuildExtractValue, LLVMBuildFAdd,
        LLVMBuildFCmp, LLVMBuildFDiv, LLVMBuildFMul, LLVMBuildFNeg, LLVMBuildFRem, LLVMBuildFSub,
        LLVMBuildGlobalStringPtr, LLVMBuildICmp, LLVMBuildInBoundsGEP2, LLVMBuildIntCast2,
        LLVMBuildLoad2, LLVMBuildMul, LLVMBuildNeg, LLVMBuildNot, LLVMBuildOr, LLVMBuildPhi,
        LLVMBuildRet, LLVMBuildRetVoid, LLVMBuildSDiv, LLVMBuildSRem, LLVMBuildStore, LLVMBuildSub,
        LLVMBuildUDiv, LLVMBuildURem, LLVMConstInt, LLVMConstIntOfArbitraryPrecision,
        LLVMConstReal, LLVMFunctionType, LLVMGetParam, LLVMGetUndef, LLVMInt1TypeInContext,
        LLVMInt32TypeInContext, LLVMInt8TypeInContext, LLVMPointerTypeInContext,
        LLVMPositionBuilderAtEnd, LLVMPrintValueToString, LLVMVoidTypeInContext,
    },
    prelude::{LLVMBuilderRef, LLVMContextRef, LLVMModuleRef, LLVMTypeRef, LLVMValueRef},
    LLVMIntPredicate, LLVMRealPredicate,
};

use crate::{llvm_bool, Error, FALSE, NONE};

pub unsafe fn add_function(
    ctx: LLVMContextRef,
    llvm_module: LLVMModuleRef,
    function: &ir::Function,
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

    let name =
        CString::new(function.name.clone()).map_err(|nul| Error::FunctionNameNulByte(nul))?;
    let llvm_func = LLVMAddFunction(llvm_module, name.as_ptr(), llvm_func_ty);
    Ok((llvm_func, llvm_func_ty))
}

pub unsafe fn function(
    ctx: LLVMContextRef,
    llvm_funcs: &[(LLVMValueRef, LLVMTypeRef)],
    llvm_func: LLVMValueRef,
    builder: LLVMBuilderRef,
    function: &ir::Function,
    log: bool,
) -> Result<(), Error> {
    if let Some(ir) = &function.ir {
        build_func(function, llvm_funcs, ir, ctx, builder, llvm_func, log);
    }
    Ok(())
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
        T::Const(_) => panic!("const type in llvm backend found"),
    }
}

unsafe fn build_func(
    func: &ir::Function,
    llvm_funcs: &[(LLVMValueRef, LLVMTypeRef)],
    ir: &ir::FunctionIr,
    ctx: LLVMContextRef,
    builder: LLVMBuilderRef,
    llvm_func: LLVMValueRef,
    log: bool,
    /*
    types: &mut [TypeInstance],
    funcs: &[(LLVMValueRef, LLVMTypeRef)],
    globals: &[LLVMValueRef],
    */
) {
    eprintln!("----- building func {}", func.name);
    let blocks: Vec<_> = (0..ir.blocks.len())
        .map(|_| core::LLVMAppendBasicBlockInContext(ctx, llvm_func, NONE))
        .collect();

    let mut instructions = Vec::with_capacity(ir.inst.len());

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

    for (i, inst) in ir.inst.iter().enumerate() {
        if log {
            print!("Generating %{i} = {:?} ->", inst);
            std::io::stdout().flush().unwrap();
        }
        let &ir::Instruction {
            tag,
            data,
            ty,
            used: _,
        } = inst;
        let val: LLVMValueRef = match tag {
            ir::Tag::BlockBegin => {
                LLVMPositionBuilderAtEnd(builder, blocks[data.int32 as usize]);
                ptr::null_mut()
            }
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
                    let r = get_ref(&instructions, data.un_op);
                    if let Some(r) = r {
                        LLVMBuildRet(builder, r)
                    } else {
                        LLVMBuildRetVoid(builder)
                    }
                }
            }
            ir::Tag::Param => {
                if let Some(_) = table_ty(func.params.nth(data.int32)) {
                    LLVMGetParam(llvm_func, data.int32)
                } else {
                    ptr::null_mut()
                }
            }
            ir::Tag::Uninit => table_ty(inst.ty).map_or(ptr::null_mut(), |ty| LLVMGetUndef(ty)),
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
                    ptr::null_mut()
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
                let val = get_ref(&instructions, data.bin_op.1);
                if let Some(val) = val {
                    if let Some(ptr) = get_ref(&instructions, data.bin_op.0) {
                        eprintln!("BUILDING STORE {val:?} {:?}", data.bin_op);
                        LLVMBuildStore(builder, val, ptr);
                    }
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
                        r_bytes
                            .copy_from_slice(&ir.extra[begin + 8 + 4 * i..begin + 8 + 4 * (i + 1)]);
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
            | ir::Tag::Mod
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
                    ir::Tag::Mod => match func.types[ty] {
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
                            let tag = if tag == ir::Tag::Eq {
                                LLVMIntPredicate::LLVMIntEQ
                            } else {
                                LLVMIntPredicate::LLVMIntNE
                            };
                            LLVMBuildICmp(builder, tag, l, r, NONE)
                        }
                        t if t.is_float() => {
                            let tag = if tag == ir::Tag::Eq {
                                LLVMRealPredicate::LLVMRealUEQ
                            } else {
                                LLVMRealPredicate::LLVMRealUNE
                            };
                            LLVMBuildFCmp(builder, tag, l, r, NONE)
                        }
                        _ => panic!("invalid type for eq/ne"),
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
                    _ => panic!("invalid type for lt"),
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
                    _ => panic!("invalid type for gt"),
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
                    _ => panic!("invalid type for le"),
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
                    _ => panic!("invalid type for le"),
                }
            }
            ir::Tag::MemberPtr => {
                let (ptr, extra_idx) = data.ref_int;
                let i = extra_idx as usize;
                let elem_types = TypeRefs::from_bytes(ir.extra[i..i + 8].try_into().unwrap());
                let elem_idx = u32::from_le_bytes(ir.extra[i + 8..i + 12].try_into().unwrap());

                let offset = ir::offset_in_tuple(elem_types, elem_idx, &func.types);

                let i8_ty = LLVMInt8TypeInContext(ctx);
                // it's a pointer, we can always unwrap
                let llvm_ptr = get_ref(&instructions, ptr).unwrap();
                let mut offset = LLVMConstInt(LLVMInt32TypeInContext(ctx), offset, FALSE);
                LLVMBuildInBoundsGEP2(builder, i8_ty, llvm_ptr, &mut offset, 1, NONE)
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
                let block_inst = ir.inst[ir.blocks[data.int32 as usize] as usize];
                debug_assert_eq!(block_inst.tag, ir::Tag::BlockBegin);
                LLVMBuildBr(builder, blocks[block_inst.data.int32 as usize])
            }
            ir::Tag::Branch => {
                let mut bytes = [0; 4];
                let begin = data.ref_int.1 as usize;
                bytes.copy_from_slice(&ir.extra[begin..begin + 4]);
                let then = u32::from_le_bytes(bytes);
                bytes.copy_from_slice(&ir.extra[begin + 4..begin + 8]);
                let else_ = u32::from_le_bytes(bytes);

                let cond = get_ref(&instructions, data.ref_int.0).unwrap();

                LLVMBuildCondBr(builder, cond, blocks[then as usize], blocks[else_ as usize])
            }
            ir::Tag::Phi => {
                if let Some(ty) = table_ty(ty) {
                    let phi = LLVMBuildPhi(builder, ty, NONE);
                    let begin = data.extra_len.0 as usize;
                    for i in 0..data.extra_len.1 {
                        let c = begin + i as usize * 8;
                        let mut b = [0; 4];
                        b.copy_from_slice(&ir.extra[c..c + 4]);
                        let block = u32::from_le_bytes(b);
                        b.copy_from_slice(&ir.extra[c + 4..c + 8]);
                        let r = ir::Ref::from_bytes(b);
                        let mut block = blocks[block as usize];
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
                    let (val, ty) = get_ref_and_type(&instructions, ir::Ref::from_bytes(arg_bytes));
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
        instructions.push(val);
    }
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
