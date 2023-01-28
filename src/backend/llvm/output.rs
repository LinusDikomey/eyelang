use std::{ffi::{CStr, CString}, mem, ptr};

use llvm::{execution_engine, target, target_machine};

use super::TRUE;


pub unsafe fn emit_bitcode(target: Option<&CStr>, module: super::Module, out: &str) {
    let target_triple = if let Some(triple) = target {
        triple.as_ptr()
    } else {
        target_machine::LLVMGetDefaultTargetTriple()
    };

    target::LLVM_InitializeAllTargetInfos();
    target::LLVM_InitializeNativeTarget();
    //target::LLVM_InitializeAllTargets();
    //target::LLVM_InitializeAllTargetMCs();
    //target::LLVM_InitializeAllAsmParsers();
    //target::LLVM_InitializeAllAsmPrinters();
    target::LLVM_InitializeNativeAsmPrinter();

    let mut target: target_machine::LLVMTargetRef = ptr::null_mut();
    let mut error: *mut i8 = ptr::null_mut();
    if target_machine::LLVMGetTargetFromTriple(target_triple, &mut target, &mut error) != 0 {
        panic!("Failed to set target triple: {:?}", CStr::from_ptr(error));
    }
    let cpu = "generic\0";
    let features = "\0";
    let opt_level = target_machine::LLVMCodeGenOptLevel::LLVMCodeGenLevelNone;

    let machine = target_machine::LLVMCreateTargetMachine(
        target,
        target_triple, cpu.as_ptr().cast(),
        features.as_ptr().cast(),
        opt_level,
        target_machine::LLVMRelocMode::LLVMRelocDefault,
        target_machine::LLVMCodeModel::LLVMCodeModelDefault
    );

    let file_type = target_machine::LLVMCodeGenFileType::LLVMObjectFile;
    // takes ownership of the module
    let out_cstr = CString::new(out).expect("Invalid object file name");
    let err = target_machine::LLVMTargetMachineEmitToFile(
        machine,
        module.into_inner(),
        out_cstr.as_ptr() as _,
        file_type,
        &mut error
    );
    if err == TRUE {
        panic!("Failed to emit object file: {:?}", CStr::from_ptr(error));
    }
}

pub unsafe fn run_jit(module: super::Module) -> i64 {
    // build an execution engine
    let mut ee = mem::MaybeUninit::uninit();
    let mut out = ptr::null_mut();

    // robust code should check that these calls complete successfully
    // each of these calls is necessary to setup an execution engine which compiles to native
    // code
    execution_engine::LLVMLinkInMCJIT();
    target::LLVM_InitializeNativeTarget();
    target::LLVM_InitializeNativeAsmPrinter();

    // takes ownership of the module
    execution_engine::LLVMCreateExecutionEngineForModule(ee.as_mut_ptr(), module.into_inner(), &mut out);
    let ee = ee.assume_init();
    
    let addr = execution_engine::LLVMGetFunctionAddress(ee, "main\0".as_ptr().cast());
    if addr == 0 {
        panic!("Main symbol not found");
    }

    let f: extern "C" fn() -> i64 = mem::transmute(addr);

    let res = f();
    
    execution_engine::LLVMDisposeExecutionEngine(ee);
    res
}
