use std::{
    ffi::{CStr, CString, NulError},
    path::Path,
};

use llvm::{
    core::{self, LLVMModuleCreateWithNameInContext},
    prelude::{LLVMBool, LLVMContextRef, LLVMModuleRef},
    target_machine,
};
use llvm_sys as llvm;

mod emit;
mod translate;

#[derive(Debug)]
pub enum Error {
    InvalidTarget(String),
    InvalidOutFile,
    FunctionNameNulByte(NulError),
    EmitFailed(String),
}

pub struct Backend {
    log: bool,
    context: LLVMContextRef,
}

const NONE: *const i8 = "\0".as_ptr().cast();
const FALSE: LLVMBool = 0;
const TRUE: LLVMBool = 1;

fn llvm_bool(b: bool) -> LLVMBool {
    if b {
        TRUE
    } else {
        FALSE
    }
}

impl Backend {
    pub fn new() -> Self {
        let context = unsafe { llvm::core::LLVMContextCreate() };

        Self {
            log: false,
            context,
        }
    }

    pub fn enable_logging(&mut self) {
        self.log = true;
    }

    pub fn emit_module(
        &self,
        module: &ir::Module,
        target: Option<&CStr>,
        out_file: &Path,
    ) -> Result<(), Error> {
        let llvm_module: LLVMModuleRef =
            unsafe { LLVMModuleCreateWithNameInContext("main\0".as_ptr().cast(), self.context) };
        let builder = unsafe { core::LLVMCreateBuilderInContext(self.context) };
        let llvm_funcs = module
            .funcs
            .iter()
            .map(|func| unsafe {
                translate::add_function(self.context, llvm_module, builder, func, module, self.log)
            })
            .collect::<Result<Vec<_>, _>>()?;

        for (func, (llvm_func, _)) in module.funcs.iter().zip(llvm_funcs.iter().copied()) {
            unsafe {
                translate::function(
                    self.context,
                    &llvm_funcs,
                    llvm_func,
                    builder,
                    func,
                    self.log,
                )?
            };
        }

        let target_triple = target.map_or_else(
            || unsafe { target_machine::LLVMGetDefaultTargetTriple() as *const i8 },
            |target| target.as_ptr(),
        );
        let out_cstr = CString::new(out_file.as_os_str().as_encoded_bytes().to_vec())
            .map_err(|_| Error::InvalidOutFile)?;
        unsafe { emit::emit(llvm_module, target_triple, out_cstr.as_ptr(), self.log)? };

        Ok(())
    }
}
