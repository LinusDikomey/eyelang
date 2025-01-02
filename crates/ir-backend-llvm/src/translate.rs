use std::{collections::VecDeque, ffi::CString, io::Write, ptr};

use ir2::{
    dialect::Primitive, Argument, BlockId, BlockTarget, Environment, ModuleId, Ref, Type, TypeId,
    Types,
};
use llvm_sys::{
    core::{
        self, LLVMAddFunction, LLVMAddGlobal, LLVMAddIncoming, LLVMBuildAdd, LLVMBuildAlloca,
        LLVMBuildAnd, LLVMBuildBr, LLVMBuildCall2, LLVMBuildCondBr, LLVMBuildExtractValue,
        LLVMBuildFAdd, LLVMBuildFCmp, LLVMBuildFDiv, LLVMBuildFMul, LLVMBuildFRem, LLVMBuildFSub,
        LLVMBuildICmp, LLVMBuildInBoundsGEP2, LLVMBuildIntCast2, LLVMBuildLoad2, LLVMBuildMul,
        LLVMBuildNeg, LLVMBuildOr, LLVMBuildPhi, LLVMBuildRet, LLVMBuildRetVoid, LLVMBuildSDiv,
        LLVMBuildSRem, LLVMBuildStore, LLVMBuildSub, LLVMBuildUDiv, LLVMBuildURem, LLVMConstInt,
        LLVMConstReal, LLVMFunctionType, LLVMGetEnumAttributeKindForName, LLVMGetParam,
        LLVMGetUndef, LLVMInt1TypeInContext, LLVMInt32TypeInContext, LLVMInt8TypeInContext,
        LLVMPointerTypeInContext, LLVMPositionBuilderAtEnd, LLVMPrintValueToString,
        LLVMSetInitializer, LLVMVoidTypeInContext,
    },
    prelude::{LLVMBuilderRef, LLVMContextRef, LLVMModuleRef, LLVMTypeRef, LLVMValueRef},
    LLVMIntPredicate, LLVMRealPredicate,
};

use crate::{llvm_bool, Dialects, Error, Intrinsics, FALSE, NONE};

pub unsafe fn add_function(
    ctx: LLVMContextRef,
    llvm_module: LLVMModuleRef,
    function: &ir2::Function,
    attribs: &Attribs,
) -> Result<(LLVMValueRef, LLVMTypeRef), Error> {
    let return_ty = llvm_ty(
        ctx,
        function.types()[function
            .return_type()
            .expect("function needs explicit return type to be lowered")],
        function.types(),
    )
    .unwrap_or_else(|| LLVMVoidTypeInContext(ctx));
    let mut params: Vec<_> = function
        .params()
        .iter()
        .filter_map(|param| {
            let &ir2::Parameter::RefOf(ty) = param else {
                panic!("invalid parameter kind {param:?}")
            };
            llvm_ty(ctx, function.types()[ty], function.types())
        })
        .collect();
    let llvm_func_ty = LLVMFunctionType(
        return_ty,
        params.as_mut_ptr(),
        params.len() as _,
        llvm_bool(function.varargs()),
    );
    let name = CString::from_vec_with_nul(
        // HACK: temporary prefix until proper name mangling is implemented
        if function.ir().is_some()
            && function.name.as_ref() != "main"
            && function.name.as_ref() != "_start"
        {
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

pub fn add_global(
    ctx: LLVMContextRef,
    llvm_module: LLVMModuleRef,
    global: &ir2::Global,
) -> Result<LLVMValueRef, Error> {
    let ty = unsafe {
        core::LLVMArrayType2(
            LLVMInt8TypeInContext(ctx),
            global.value.len().try_into().unwrap(),
        )
    };
    let name = CString::new(global.name.as_bytes()).map_err(|_| Error::NulByte)?;
    let llvm_global = unsafe { LLVMAddGlobal(llvm_module, ty, name.as_ptr()) };
    unsafe {
        let value = core::LLVMConstStringInContext2(
            ctx,
            global.value.as_ptr().cast(),
            global.value.len(),
            1,
        );
        LLVMSetInitializer(llvm_global, value);
        core::LLVMSetAlignment(
            llvm_global,
            global.align.try_into().expect("align too large for llvm"),
        );
        if global.readonly {
            core::LLVMSetGlobalConstant(llvm_global, 1);
        }
    }
    Ok(llvm_global)
}

pub unsafe fn function(
    env: &Environment,
    module_id: ModuleId,
    ctx: LLVMContextRef,
    dialects: &Dialects,
    llvm_module: LLVMModuleRef,
    llvm_funcs: &[(LLVMValueRef, LLVMTypeRef)],
    globals: &[LLVMValueRef],
    llvm_func: LLVMValueRef,
    builder: LLVMBuilderRef,
    function: &ir2::Function,
    intrinsics: &Intrinsics,
    log: bool,
) -> Result<(), Error> {
    if let Some(ir) = function.ir() {
        build_func(
            env,
            module_id,
            function,
            dialects,
            llvm_module,
            llvm_funcs,
            globals,
            ir,
            ctx,
            builder,
            llvm_func,
            intrinsics,
            log,
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
unsafe fn llvm_ty(ctx: LLVMContextRef, ty: Type, types: &Types) -> Option<LLVMTypeRef> {
    match ty {
        Type::Primitive(id) => match Primitive::try_from(id).unwrap() {
            Primitive::Unit => None,
            Primitive::I1 => Some(core::LLVMInt1TypeInContext(ctx)),
            Primitive::I8 | Primitive::U8 => Some(core::LLVMInt8TypeInContext(ctx)),
            Primitive::I16 | Primitive::U16 => Some(core::LLVMInt16TypeInContext(ctx)),
            Primitive::I32 | Primitive::U32 => Some(core::LLVMInt32TypeInContext(ctx)),
            Primitive::I64 | Primitive::U64 => Some(core::LLVMInt64TypeInContext(ctx)),
            Primitive::I128 | Primitive::U128 => Some(core::LLVMInt128TypeInContext(ctx)),
            Primitive::F32 => Some(core::LLVMFloatTypeInContext(ctx)),
            Primitive::F64 => Some(core::LLVMDoubleTypeInContext(ctx)),
            Primitive::Ptr => Some(core::LLVMPointerTypeInContext(ctx, 0)),
        },
        Type::Array(elem, size) => Some(core::LLVMArrayType2(
            llvm_ty(ctx, types[elem], types)?,
            size as u64,
        )),
        Type::Tuple(elems) => {
            if elems.count() == 0 {
                return None;
            }
            let mut types = elems
                .iter()
                .map(|ty| llvm_ty(ctx, types[ty], types))
                .collect::<Option<Vec<_>>>()?;
            Some(core::LLVMStructTypeInContext(
                ctx,
                types.as_mut_ptr(),
                elems.count() as _,
                FALSE,
            ))
        }
    }
}

unsafe fn build_func(
    env: &Environment,
    module: ModuleId,
    func: &ir2::Function,
    dialects: &Dialects,
    llvm_module: LLVMModuleRef,
    llvm_funcs: &[(LLVMValueRef, LLVMTypeRef)],
    globals: &[LLVMValueRef],
    ir: &ir2::FunctionIr,
    ctx: LLVMContextRef,
    builder: LLVMBuilderRef,
    llvm_func: LLVMValueRef,
    intrinsics: &Intrinsics,
    log: bool,
) {
    if log {
        println!("Translating function {} to LLVM IR", func.name);
    }

    let types = func.types();

    let mut instructions = vec![ptr::null_mut(); ir.inst_count() as usize];

    // create an LLVM block for each block while also creating a Phi node for each incoming block arg.
    let blocks: Vec<_> = ir
        .block_ids()
        .map(|block| {
            let llvm_block = core::LLVMAppendBasicBlockInContext(ctx, llvm_func, NONE);

            let block_args = ir.get_block_args(block);
            LLVMPositionBuilderAtEnd(builder, llvm_block);
            for (i, arg) in block_args.enumerate() {
                if block == ir2::BlockId::ENTRY {
                    instructions[arg.idx()] = LLVMGetParam(llvm_func, i as _);
                } else {
                    let arg_ty = types[ir.get_ref_ty(arg)];
                    if let Some(ty) = llvm_ty(ctx, arg_ty, types) {
                        instructions[arg.idx()] = LLVMBuildPhi(builder, ty, NONE);
                    }
                }
            }
            llvm_block
        })
        .collect();

    let block_graph = ir2::BlockGraph::calculate(ir, env);

    let i1 = LLVMInt1TypeInContext(ctx);

    let get_ref_and_type_ptr =
        |instructions: &[LLVMValueRef], r: Ref| -> (Option<LLVMValueRef>, Type) {
            match r {
                Ref::UNIT => (None, Type::Primitive(Primitive::Unit.id())),
                Ref::TRUE => (None, Type::Primitive(Primitive::I1.id())),
                Ref::FALSE => (None, Type::Primitive(Primitive::I1.id())),
                _ => {
                    let inst = ir.get_inst(r);

                    let r = instructions[r.idx()];
                    let ty = types[inst.ty()];
                    ((!r.is_null()).then_some(r), ty)
                }
            }
        };
    let get_ref_and_type =
        |instructions: &[LLVMValueRef], r: Ref| get_ref_and_type_ptr(instructions, r);
    let get_ref = |instructions: &[LLVMValueRef], r: Ref| match r {
        Ref::UNIT => None,
        Ref::TRUE => Some(LLVMConstInt(i1, 1, 0)),
        Ref::FALSE => Some(LLVMConstInt(i1, 0, 0)),
        _ => {
            let r = instructions[r.idx()];
            (!r.is_null()).then_some(r)
        }
    };

    let table_ty = |ty: TypeId| llvm_ty(ctx, types[ty], types);

    let mut queued_blocks = vec![false; ir.block_ids().len()];
    let mut block_queue = VecDeque::from([BlockId::ENTRY]);
    queued_blocks[BlockId::ENTRY.idx()] = true;

    for block in block_graph.postorder().iter().copied().rev() {
        let llvm_block = blocks[block.idx()];

        let mut handle_successor =
            |ir: &ir2::FunctionIr, instructions: &[LLVMValueRef], successor: BlockTarget| {
                for (block_arg_ref, &r) in ir.get_block_args(successor.0).zip(successor.1.iter()) {
                    if let Some(mut llvm_val) = get_ref(instructions, r) {
                        let phi = instructions[block_arg_ref.idx()];
                        if !phi.is_null() {
                            let mut block = llvm_block;
                            LLVMAddIncoming(phi, &mut llvm_val, &mut block, 1);
                        }
                    }
                }
                if !queued_blocks[successor.0.idx()] {
                    queued_blocks[successor.0.idx()] = true;
                    block_queue.push_back(successor.0);
                }
            };

        LLVMPositionBuilderAtEnd(builder, llvm_block);
        for (i, inst) in ir.get_block(block) {
            if log {
                print!("Generating %{i:?} = {:?} ->", inst);
                std::io::stdout().flush().unwrap();
            }
            let val: LLVMValueRef = if let Some(inst) = inst.as_module(ir2::BUILTIN) {
                match inst.op() {
                    ir2::Builtin::Nothing => ptr::null_mut(),
                    ir2::Builtin::BlockArg => unreachable!(),
                    ir2::Builtin::Undef => llvm_ty(ctx, types[inst.ty()], types)
                        .map(|ty| LLVMGetUndef(ty))
                        .unwrap_or(ptr::null_mut()),
                }
            } else if let Some(inst) = inst.as_module(dialects.arith) {
                use ir2::dialect::Arith as I;
                let mut args = inst.args(ir.blocks(), ir.extra());
                let un_op = || {
                    let mut args = ir.args(&inst);
                    match (args.next(), args.next()) {
                        (Some(Argument::Ref(a)), None) => a,
                        _ => unreachable!("un_op expected"),
                    }
                };
                let bin_op = || {
                    let mut args = ir.args(&inst);
                    match (args.next(), args.next(), args.next()) {
                        (Some(Argument::Ref(a)), Some(Argument::Ref(b)), None) => (a, b),
                        _ => unreachable!("bin_op expected"),
                    }
                };
                let comparison = |builder: LLVMBuilderRef,
                                  instructions: &[LLVMValueRef],
                                  (a, b): (Ref, Ref),
                                  preds: (
                    LLVMIntPredicate,
                    LLVMIntPredicate,
                    LLVMRealPredicate,
                )| {
                    let (l, ty) = get_ref_and_type(instructions, a);
                    let l = l.unwrap();
                    let r = get_ref(instructions, b).unwrap();
                    match ty {
                        t if is_unsigned_int(t) => LLVMBuildICmp(builder, preds.0, l, r, NONE),
                        t if is_signed_int(t) => LLVMBuildICmp(builder, preds.1, l, r, NONE),
                        t if is_float(t) => LLVMBuildFCmp(builder, preds.2, l, r, NONE),
                        Type::Primitive(p) if p == Primitive::Ptr.id() => {
                            LLVMBuildICmp(builder, preds.0, l, r, NONE)
                        }
                        t => panic!("invalid type for lt {t:?}"),
                    }
                };
                match inst.op() {
                    I::Int => {
                        let Some(Argument::Int(int)) = args.next() else {
                            unreachable!()
                        };
                        LLVMConstInt(table_ty(inst.ty()).unwrap(), int, FALSE)
                    }
                    I::Float => {
                        let [Argument::Float(float)] = ir.args_n(&inst) else {
                            unreachable!()
                        };
                        LLVMConstReal(table_ty(inst.ty()).unwrap(), float)
                    }
                    I::Neg => {
                        let r = get_ref(&instructions, un_op()).unwrap();
                        match types[inst.ty()] {
                            Type::Primitive(p) => match Primitive::try_from(p).unwrap() {
                                p if p.is_int() => LLVMBuildNeg(builder, r, NONE),
                                p if p.is_float() => LLVMBuildNeg(builder, r, NONE),
                                _ => panic!("invalid primitive for neg"),
                            },
                            _ => panic!("invalid type for neg"),
                        }
                    }
                    I::Add | I::Sub | I::Mul | I::Div | I::Rem | I::Or | I::And => {
                        let (l, r) = bin_op();
                        let l = get_ref(&instructions, l).unwrap();
                        let r = get_ref(&instructions, r).unwrap();

                        match inst.op() {
                            I::Add => match types[inst.ty()] {
                                t if is_int(t) => LLVMBuildAdd(builder, l, r, NONE),
                                t if is_float(t) => LLVMBuildFAdd(builder, l, r, NONE),
                                _ => panic!("invalid type for add"),
                            },
                            I::Sub => match types[inst.ty()] {
                                t if is_int(t) => LLVMBuildSub(builder, l, r, NONE),
                                t if is_float(t) => LLVMBuildFSub(builder, l, r, NONE),
                                _ => panic!("invalid type for sub"),
                            },
                            I::Mul => match types[inst.ty()] {
                                t if is_int(t) => LLVMBuildMul(builder, l, r, NONE),
                                t if is_float(t) => LLVMBuildFMul(builder, l, r, NONE),
                                _ => panic!("invalid type for mul"),
                            },
                            I::Div => match types[inst.ty()] {
                                t if is_unsigned_int(t) => LLVMBuildUDiv(builder, l, r, NONE),
                                t if is_signed_int(t) => LLVMBuildSDiv(builder, l, r, NONE),
                                t if is_float(t) => LLVMBuildFDiv(builder, l, r, NONE),
                                _ => panic!("invalid type for udiv"),
                            },
                            I::Rem => match types[inst.ty()] {
                                t if is_unsigned_int(t) => LLVMBuildURem(builder, l, r, NONE),
                                t if is_signed_int(t) => LLVMBuildSRem(builder, l, r, NONE),
                                t if is_float(t) => LLVMBuildFRem(builder, l, r, NONE),
                                _ => panic!("invalid type for urem"),
                            },
                            I::Or => LLVMBuildOr(builder, l, r, NONE),
                            I::And => LLVMBuildAnd(builder, l, r, NONE),
                            _ => unreachable!(),
                        }
                    }
                    I::Eq | I::NE => {
                        let is_eq = inst.op() == I::Eq;
                        let (a, b) = bin_op();
                        let (l, ty) = get_ref_and_type(&instructions, a);
                        let r = get_ref(&instructions, b);

                        if let (Some(l), Some(r)) = (l, r) {
                            match ty {
                                t if is_int(t) => {
                                    let pred = if is_eq {
                                        LLVMIntPredicate::LLVMIntEQ
                                    } else {
                                        LLVMIntPredicate::LLVMIntNE
                                    };
                                    LLVMBuildICmp(builder, pred, l, r, NONE)
                                }
                                t if is_float(t) => {
                                    let pred = if is_eq {
                                        LLVMRealPredicate::LLVMRealUEQ
                                    } else {
                                        LLVMRealPredicate::LLVMRealUNE
                                    };
                                    LLVMBuildFCmp(builder, pred, l, r, NONE)
                                }
                                Type::Primitive(p) if p == Primitive::Ptr.id() => {
                                    let pred = if is_eq {
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
                    I::LT => comparison(
                        builder,
                        &instructions,
                        bin_op(),
                        (
                            LLVMIntPredicate::LLVMIntULT,
                            LLVMIntPredicate::LLVMIntSLT,
                            LLVMRealPredicate::LLVMRealOLT,
                        ),
                    ),
                    I::GT => comparison(
                        builder,
                        &instructions,
                        bin_op(),
                        (
                            LLVMIntPredicate::LLVMIntUGT,
                            LLVMIntPredicate::LLVMIntSGT,
                            LLVMRealPredicate::LLVMRealOGT,
                        ),
                    ),
                    I::LE => comparison(
                        builder,
                        &instructions,
                        bin_op(),
                        (
                            LLVMIntPredicate::LLVMIntULE,
                            LLVMIntPredicate::LLVMIntSLE,
                            LLVMRealPredicate::LLVMRealOLE,
                        ),
                    ),
                    I::GE => comparison(
                        builder,
                        &instructions,
                        bin_op(),
                        (
                            LLVMIntPredicate::LLVMIntUGE,
                            LLVMIntPredicate::LLVMIntSGE,
                            LLVMRealPredicate::LLVMRealOGE,
                        ),
                    ),
                    I::Xor => {
                        let (l, r) = bin_op();
                        core::LLVMBuildXor(
                            builder,
                            get_ref(&instructions, l).unwrap(),
                            get_ref(&instructions, r).unwrap(),
                            NONE,
                        )
                    }
                    I::Rol | I::Ror => {
                        let (l, r) = bin_op();
                        let ((Some(l), l_ty), Some(r)) = (
                            get_ref_and_type(&instructions, l),
                            get_ref(&instructions, r),
                        ) else {
                            panic!("invalid types for rol/ror")
                        };
                        let l_ty = llvm_ty(ctx, l_ty, types).unwrap();
                        let mut fshl_args = [l_ty];
                        let intrinsic = if inst.op() == I::Rol {
                            intrinsics.fshl
                        } else {
                            intrinsics.fshr
                        };
                        let function = core::LLVMGetIntrinsicDeclaration(
                            llvm_module,
                            intrinsic,
                            fshl_args.as_mut_ptr(),
                            fshl_args.len(),
                        );
                        let ty = core::LLVMIntrinsicGetType(
                            ctx,
                            intrinsics.fshl,
                            fshl_args.as_mut_ptr(),
                            fshl_args.len(),
                        );
                        let mut args = [l, l, r];
                        LLVMBuildCall2(
                            builder,
                            ty,
                            function,
                            args.as_mut_ptr(),
                            args.len() as u32,
                            NONE,
                        )
                    }
                    I::CastInt => {
                        let val = get_ref(&instructions, un_op());
                        // there are no zero-sized integers so unwraps are fine
                        let val = val.unwrap();
                        let to_ty = types[inst.ty()];
                        let signed = is_signed_int(to_ty);
                        let target_ty = llvm_ty(ctx, to_ty, types).unwrap();
                        LLVMBuildIntCast2(builder, val, target_ty, llvm_bool(signed), NONE)
                    }
                    I::CastFloat => {
                        let (val, from_ty) = get_ref_and_type(&instructions, un_op());
                        // there are no zero-sized floats so unwraps are fine
                        let val = val.unwrap();
                        let to_ty = types[inst.ty()];
                        let target_ty = llvm_ty(ctx, to_ty, types).unwrap();
                        let (Type::Primitive(from_ty), Type::Primitive(to_ty)) = (from_ty, to_ty)
                        else {
                            panic!()
                        };
                        let from_ty = Primitive::try_from(from_ty).unwrap();
                        let to_ty = Primitive::try_from(to_ty).unwrap();
                        match (from_ty, to_ty) {
                            (Primitive::F32, Primitive::F64) => {
                                core::LLVMBuildFPExt(builder, val, target_ty, NONE)
                            }
                            (Primitive::F64, Primitive::F32) => {
                                core::LLVMBuildFPTrunc(builder, val, target_ty, NONE)
                            }
                            _ => panic!("invalid types for CastFloat"),
                        }
                    }
                    I::CastIntToFloat => {
                        let (val, from_ty) = get_ref_and_type(&instructions, un_op());
                        // there are no zero-sized ints/floats so unwraps are fine
                        let val = val.unwrap();
                        let to_ty = types[inst.ty()];
                        let target_ty = llvm_ty(ctx, to_ty, types).unwrap();
                        if is_unsigned_int(from_ty) {
                            core::LLVMBuildUIToFP(builder, val, target_ty, NONE)
                        } else {
                            core::LLVMBuildSIToFP(builder, val, target_ty, NONE)
                        }
                    }
                    I::CastFloatToInt => {
                        // there are no zero-sized ints/floats so unwraps are fine
                        let val = get_ref(&instructions, un_op()).unwrap();
                        let to_ty = types[inst.ty()];
                        let target_ty = llvm_ty(ctx, to_ty, types).unwrap();
                        if is_unsigned_int(to_ty) {
                            core::LLVMBuildFPToUI(builder, val, target_ty, NONE)
                        } else {
                            core::LLVMBuildFPToSI(builder, val, target_ty, NONE)
                        }
                    }
                }
            } else if let Some(inst) = inst.as_module(dialects.cf) {
                let mut args = ir.args(&inst);
                use ir2::dialect::Cf as I;
                match inst.op() {
                    I::Goto => {
                        let Some(Argument::BlockTarget(target)) = args.next() else {
                            unreachable!()
                        };
                        handle_successor(ir, &instructions, target);
                        LLVMBuildBr(builder, blocks[target.0.idx()])
                    }
                    I::Branch => {
                        let (cond, on_true, on_false) = match [
                            args.next(),
                            args.next(),
                            args.next(),
                        ] {
                            [Some(Argument::Ref(cond)), Some(Argument::BlockTarget(on_true)), Some(Argument::BlockTarget(on_false))] => {
                                (cond, on_true, on_false)
                            }
                            _ => unreachable!(),
                        };
                        let cond = get_ref(&instructions, cond).unwrap();
                        handle_successor(ir, &instructions, on_true);
                        handle_successor(ir, &instructions, on_false);
                        LLVMBuildCondBr(
                            builder,
                            cond,
                            blocks[on_true.0.idx()],
                            blocks[on_false.0.idx()],
                        )
                    }
                    I::Ret => {
                        let Some(Argument::Ref(value)) = args.next() else {
                            unreachable!()
                        };
                        /*if value == ir::Ref::UNDEF {
                            if let Some(ty) = llvm_ty(ctx, func.return_type, types) {
                                let val = LLVMGetUndef(ty);
                                LLVMBuildRet(builder, val)
                            } else {
                                LLVMBuildRetVoid(builder)
                            }
                        } else {*/
                        let (r, ty) = get_ref_and_type(&instructions, value);

                        if let Some(r) =
                            r.and_then(|r| llvm_ty(ctx, ty, types).is_some().then_some(r))
                        {
                            LLVMBuildRet(builder, r)
                        } else {
                            LLVMBuildRetVoid(builder)
                        }
                        //}
                    }
                }
            } else if let Some(inst) = inst.as_module(dialects.mem) {
                use ir2::dialect::Mem as I;
                match inst.op() {
                    I::Decl => {
                        let [Argument::TypeId(ty)] = ir.args_n(&inst) else {
                            unreachable!()
                        };
                        if let Some(ty) = table_ty(ty) {
                            LLVMBuildAlloca(builder, ty, NONE)
                        } else {
                            // return a null pointer if a declaration has a zero-sized type
                            core::LLVMConstPointerNull(LLVMPointerTypeInContext(ctx, 0))
                        }
                    }
                    I::Load => {
                        let [Argument::Ref(r)] = ir.args_n(&inst) else {
                            unreachable!()
                        };
                        let val = get_ref(&instructions, r);
                        if let Some(pointee_ty) = llvm_ty(ctx, types[inst.ty()], types) {
                            let val = val.unwrap();
                            LLVMBuildLoad2(builder, pointee_ty, val, NONE)
                        } else {
                            ptr::null_mut()
                        }
                    }
                    I::Store => {
                        let [Argument::Ref(ptr), Argument::Ref(val)] = ir.args_n(&inst) else {
                            unreachable!()
                        };
                        let (val, ty) = get_ref_and_type(&instructions, val);
                        if !types.is_zero_sized(ty, env.primitives()) {
                            let ptr = get_ref(&instructions, ptr).unwrap();
                            LLVMBuildStore(builder, val.unwrap(), ptr);
                        }
                        ptr::null_mut()
                    }
                    I::MemberPtr => {
                        let [Argument::Ref(ptr), Argument::TypeId(tuple), Argument::Int(idx)] =
                            ir.args_n(&inst)
                        else {
                            unreachable!()
                        };
                        let Type::Tuple(elem_types) = types[tuple] else {
                            panic!()
                        };
                        let offset = ir2::offset_in_tuple(
                            elem_types,
                            idx.try_into().unwrap(),
                            types,
                            env.primitives(),
                        );

                        let i8_ty = LLVMInt8TypeInContext(ctx);
                        if let Some(llvm_ptr) = get_ref(&instructions, ptr) {
                            let mut offset =
                                LLVMConstInt(LLVMInt32TypeInContext(ctx), offset, FALSE);
                            LLVMBuildInBoundsGEP2(builder, i8_ty, llvm_ptr, &mut offset, 1, NONE)
                        } else {
                            ptr::null_mut()
                        }
                    }
                    I::IntToPtr => {
                        let [Argument::Ref(int)] = ir.args_n(&inst) else {
                            unreachable!()
                        };
                        // no zero-sized integers so unwrapping is fine
                        let val = get_ref(&instructions, int).unwrap();
                        core::LLVMBuildIntToPtr(
                            builder,
                            val,
                            LLVMPointerTypeInContext(ctx, 0),
                            NONE,
                        )
                    }
                    I::PtrToInt => {
                        let [Argument::Ref(ptr)] = ir.args_n(&inst) else {
                            unreachable!()
                        };
                        // no zero-sized integers so unwrapping is fine
                        let val = get_ref(&instructions, ptr).unwrap();
                        let ty = llvm_ty(ctx, types[inst.ty()], types).unwrap();
                        core::LLVMBuildPtrToInt(builder, val, ty, NONE)
                    }
                    I::FunctionPtr => {
                        let [Argument::FunctionId(func_id)] = ir.args_n(&inst) else {
                            unreachable!()
                        };
                        if func_id.module != module {
                            panic!("unsupported: can't take function pointer of function in different module")
                        }
                        let (llvm_func, _) = llvm_funcs[func_id.function.idx()];
                        llvm_func
                    }
                    I::Global => {
                        let [Argument::GlobalId(id)] = ir.args_n(&inst) else {
                            unreachable!()
                        };
                        if id.module != module {
                            panic!("unsupported: can't take global in in different module")
                        }
                        globals[id.idx as usize]
                    }
                    I::ArrayIndex => {
                        let [Argument::Ref(array_ptr), Argument::TypeId(elem_ty), Argument::Ref(idx)] =
                            ir.args_n(&inst)
                        else {
                            unreachable!()
                        };
                        let ptr = get_ref(&instructions, array_ptr).unwrap();
                        let ty = llvm_ty(ctx, func[elem_ty], func.types()).unwrap();
                        let mut indices = [get_ref(&instructions, idx).unwrap()];
                        LLVMBuildInBoundsGEP2(
                            builder,
                            ty,
                            ptr,
                            indices.as_mut_ptr(),
                            indices.len() as _,
                            NONE,
                        )
                    }
                }
            } else if let Some(inst) = inst.as_module(dialects.tuple) {
                use ir2::dialect::Tuple as I;
                match inst.op() {
                    I::MemberValue => {
                        let [Argument::Ref(tuple), Argument::Int(mut idx)] = ir.args_n(&inst)
                        else {
                            panic!()
                        };
                        if let (Some(val), tuple_ty) = get_ref_and_type(&instructions, tuple) {
                            let Type::Tuple(ids) = tuple_ty else { panic!() };
                            for ty in ids.iter().take(idx as usize) {
                                if types.is_zero_sized(types[ty], env.primitives()) {
                                    idx -= 1;
                                }
                            }
                            LLVMBuildExtractValue(builder, val, idx.try_into().unwrap(), NONE)
                        } else {
                            ptr::null_mut()
                        }
                    }
                    I::InsertMember => {
                        let [Argument::Ref(tuple), Argument::Int(mut idx), Argument::Ref(member)] =
                            ir.args_n(&inst)
                        else {
                            panic!()
                        };
                        let (tuple, tuple_ty) = get_ref_and_type(&instructions, tuple);
                        if let Some((tuple, member)) = tuple.and_then(|tuple| {
                            get_ref(&instructions, member).map(|member| (tuple, member))
                        }) {
                            let Type::Tuple(ids) = tuple_ty else { panic!() };
                            for ty in ids.iter().take(idx as usize) {
                                if types.is_zero_sized(types[ty], env.primitives()) {
                                    idx -= 1;
                                }
                            }
                            core::LLVMBuildInsertValue(
                                builder,
                                tuple,
                                member,
                                idx.try_into().unwrap(),
                                NONE,
                            )
                        } else {
                            ptr::null_mut()
                        }
                    }
                }
            } else if inst.module() == module {
                let (llvm_func, llvm_func_ty) = llvm_funcs[inst.function().idx()];
                let inst_func = &env[inst.module()][inst.function()];
                let args = inst.args(
                    inst_func.params(),
                    inst_func.varargs(),
                    ir.blocks(),
                    ir.extra(),
                );
                let mut args: Vec<_> = args
                    .filter_map(|arg| {
                        let Argument::Ref(r) = arg else {
                            unreachable!()
                        };
                        get_ref(&instructions, r)
                    })
                    .collect();
                LLVMBuildCall2(
                    builder,
                    llvm_func_ty,
                    llvm_func,
                    args.as_mut_ptr(),
                    args.len() as u32,
                    NONE,
                )
            } else {
                panic!("unknown module")
            };
            /*
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
                    bytes.copy_from_slice(
                        &ir.extra()[data.extra as usize..data.extra as usize + 16],
                    );
                    let num = u128::from_le_bytes(bytes);
                    let words = [(num >> 64) as u64, (num as u64)];
                    LLVMConstIntOfArbitraryPrecision(table_ty(ty).unwrap(), 2, words.as_ptr())
                }
                ir::Tag::Float => LLVMConstReal(table_ty(ty).unwrap(), data.float),
                ir::Tag::Decl => {
                    if let Some(ty) = table_ty(data.ty) {
                        LLVMBuildAlloca(builder, ty, NONE)
                    } else {
                        // return a null pointer if a declaration has a zero-sized type
                        core::LLVMConstPointerNull(LLVMPointerTypeInContext(ctx, 0))
                    }
                }
                ir::Tag::Load => {
                    let val = get_ref(&instructions, data.un_op);
                    if let Some(pointee_ty) = llvm_ty(ctx, func.types[ty], &func.types) {
                        let val = val.unwrap();
                        LLVMBuildLoad2(builder, pointee_ty, val, NONE)
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
                ir::Tag::Rol => {
                    let (l, r) = inst.data.bin_op();
                    let ((Some(l), l_ty), Some(r)) = (
                        get_ref_and_type(&instructions, l),
                        get_ref(&instructions, r),
                    ) else {
                        panic!("invalid types for rol/ror")
                    };
                    let l_ty = llvm_ty(ctx, l_ty, &func.types).unwrap();
                    let mut fshl_args = [l_ty];
                    let fshl = core::LLVMGetIntrinsicDeclaration(
                        llvm_module,
                        intrinsics.fshl,
                        fshl_args.as_mut_ptr(),
                        fshl_args.len(),
                    );
                    let ty = core::LLVMIntrinsicGetType(
                        ctx,
                        intrinsics.fshl,
                        fshl_args.as_mut_ptr(),
                        fshl_args.len(),
                    );
                    let mut args = [l, l, r];
                    LLVMBuildCall2(
                        builder,
                        ty,
                        fshl,
                        args.as_mut_ptr(),
                        args.len() as u32,
                        NONE,
                    )
                }

                ir::Tag::Ror => todo!(),
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
                        b,
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
            */
            if log {
                if val.is_null() {
                    println!("null");
                } else {
                    let cstr = val_str(val);
                    println!("{cstr:?}");
                }
            }
            instructions[i.idx()] = val;
        }
    }
}

fn is_int(t: Type) -> bool {
    match t {
        Type::Primitive(p) => Primitive::try_from(p).unwrap().is_int(),
        _ => false,
    }
}

fn is_signed_int(t: Type) -> bool {
    matches!(t, Type::Primitive(p) if Primitive::try_from(p).unwrap().is_signed_int())
}

fn is_unsigned_int(t: Type) -> bool {
    matches!(t, Type::Primitive(p) if Primitive::try_from(p).unwrap().is_unsigned_int())
}

fn is_float(t: Type) -> bool {
    match t {
        Type::Primitive(p) => Primitive::try_from(p).unwrap().is_float(),
        _ => false,
    }
}

/*
unsafe fn const_val(val: &ir::ConstValue, ty: LLVMTypeRef) -> Option<LLVMValueRef> {
    Some(match val {
        ConstValue::Undefined | ConstValue::Unit => return None,
        &ConstValue::Int(int) => LLVMConstInt(ty, int as u64, FALSE),
        &ConstValue::Float(val) => LLVMConstReal(ty, val),
    })
}
*/

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
