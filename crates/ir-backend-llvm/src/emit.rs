use std::{ptr, ffi::CStr};

use llvm_sys as llvm;
use llvm::{prelude::LLVMModuleRef, target_machine};

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
        target::LLVM_InitializeNativeTarget();
        target::LLVM_InitializeNativeAsmPrinter();
        let mut target = ptr::null_mut();
        if target_machine::LLVMGetTargetFromTriple(target_triple, &mut target, &mut error) != 0 {
            let msg = CStr::from_ptr(error).to_string_lossy().into_owned();
            return Err(Error::InvalidTarget(msg));
        }

        let opt_level = target_machine::LLVMCodeGenOptLevel::LLVMCodeGenLevelNone;

        target_machine::LLVMCreateTargetMachine(
            target,
            target_triple,
            "generic\0".as_ptr().cast(), // cpu
            NONE, // features
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
    ) != 0 {
        let msg = CStr::from_ptr(error).to_string_lossy().into_owned();
        return Err(Error::EmitFailed(msg));
    }
    Ok(())
}
