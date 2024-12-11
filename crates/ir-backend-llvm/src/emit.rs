use std::{ffi::CStr, ptr};

use llvm::{prelude::LLVMModuleRef, target_machine};
use llvm_sys as llvm;

use crate::{Error, NONE};

pub unsafe fn emit(
    module: LLVMModuleRef,
    target_triple: *const i8,
    out_file: *const i8,
) -> Result<(), Error> {
    let mut error = ptr::null_mut();
    let target_machine = unsafe {
        use llvm::target;
        target::LLVM_InitializeAllTargetInfos();
        //target::LLVM_InitializeNativeTarget();
        target::LLVM_InitializeAllTargets();
        //target::LLVM_InitializeNativeAsmPrinter();
        target::LLVM_InitializeAllAsmParsers();
        target::LLVM_InitializeAllAsmPrinters();
        target::LLVM_InitializeAllTargetMCs();
        let mut target = ptr::null_mut();
        if target_machine::LLVMGetTargetFromTriple(target_triple, &mut target, &mut error) != 0 {
            let msg = CStr::from_ptr(error).to_string_lossy().into_owned();
            return Err(Error::InvalidTarget(msg));
        }

        let opt_level = target_machine::LLVMCodeGenOptLevel::LLVMCodeGenLevelNone;

        target_machine::LLVMCreateTargetMachine(
            target,
            target_triple,
            c"generic".as_ptr(), // cpu
            NONE,                // features
            opt_level,
            target_machine::LLVMRelocMode::LLVMRelocDefault,
            target_machine::LLVMCodeModel::LLVMCodeModelDefault,
        )
    };

    let file_type = target_machine::LLVMCodeGenFileType::LLVMObjectFile;

    if target_machine::LLVMTargetMachineEmitToFile(
        target_machine,
        module,
        out_file as _,
        file_type,
        &mut error,
    ) != 0
    {
        let msg = CStr::from_ptr(error).to_string_lossy().into_owned();
        return Err(Error::EmitFailed(msg));
    }
    Ok(())
}

pub fn list_targets() -> Vec<String> {
    use llvm_sys::{target, target_machine};
    unsafe { target::LLVM_InitializeAllTargetInfos() };
    let mut target = unsafe { target_machine::LLVMGetFirstTarget() };
    let mut targets = Vec::new();
    while !target.is_null() {
        let s = unsafe { CStr::from_ptr(target_machine::LLVMGetTargetName(target)) };
        targets.push(s.to_str().unwrap().to_owned());
        target = unsafe { target_machine::LLVMGetNextTarget(target) };
    }
    targets
}
