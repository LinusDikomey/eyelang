use std::{
    ffi::{CStr, CString},
    path::Path,
};

use ir2::ModuleOf;
use llvm::{
    core::{self, LLVMModuleCreateWithNameInContext},
    prelude::{LLVMBool, LLVMContextRef, LLVMModuleRef},
    target_machine,
};
use llvm_sys as llvm;

mod emit;
mod translate;

pub use emit::list_targets;
use translate::Attribs;

#[derive(Debug)]
pub enum Error {
    InvalidTarget(String),
    InvalidOutFile,
    NulByte,
    EmitFailed(String),
}

pub struct Backend {
    log: bool,
    context: LLVMContextRef,
    attribs: Attribs,
    intrinsics: Intrinsics,
}

const NONE: *const i8 = c"".as_ptr().cast();
const FALSE: LLVMBool = 0;
const TRUE: LLVMBool = 1;

fn llvm_bool(b: bool) -> LLVMBool {
    if b {
        TRUE
    } else {
        FALSE
    }
}
impl Default for Backend {
    fn default() -> Self {
        let context = unsafe { llvm::core::LLVMContextCreate() };
        let attribs = Attribs::lookup();

        Self {
            log: false,
            context,
            attribs,
            intrinsics: Intrinsics::lookup(),
        }
    }
}
impl Backend {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn enable_logging(&mut self) {
        self.log = true;
    }

    pub fn emit_module(
        &self,
        env: &ir2::Environment,
        module: &ir2::Module,
        print_ir: bool,
        target: Option<&CStr>,
        out_file: &Path,
    ) -> Result<(), Error> {
        let llvm_module: LLVMModuleRef =
            unsafe { LLVMModuleCreateWithNameInContext(c"main".as_ptr(), self.context) };
        let builder = unsafe { core::LLVMCreateBuilderInContext(self.context) };
        let llvm_funcs = module
            .functions()
            .iter()
            .map(|func| unsafe {
                translate::add_function(self.context, llvm_module, func, &self.attribs)
            })
            .collect::<Result<Vec<_>, _>>()?;

        let dialects = Dialects {
            arith: env.get_dialect_module().unwrap(),
            tuple: env.get_dialect_module().unwrap(),
            mem: env.get_dialect_module().unwrap(),
            cf: env.get_dialect_module().unwrap(),
        };
        // TODO: reimplement globals
        /*let llvm_globals = module
        .globals()
        .iter()
        .map(|global| unsafe {
            translate::add_global(
                self.context,
                llvm_module,
                global.name(),
                &global.types,
                global.ty,
                &global.value,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
        */

        for (func, (llvm_func, _)) in module.functions().iter().zip(llvm_funcs.iter().copied()) {
            unsafe {
                translate::function(
                    env,
                    self.context,
                    &dialects,
                    llvm_module,
                    &llvm_funcs,
                    &[], // TODO: globals
                    llvm_func,
                    builder,
                    func,
                    &self.intrinsics,
                    self.log,
                )?
            };
        }

        if print_ir {
            eprintln!("\n ---------- LLVM IR BEGIN ----------\n");
            unsafe { core::LLVMDumpModule(llvm_module) };
            eprintln!("\n ---------- LLVM IR END ------------\n");
        }

        #[cfg(debug_assertions)]
        {
            let mut msg = std::ptr::null_mut();
            let action = llvm::analysis::LLVMVerifierFailureAction::LLVMAbortProcessAction;
            let invalid =
                unsafe { llvm::analysis::LLVMVerifyModule(llvm_module, action, &mut msg) };
            if invalid == TRUE {
                let s = unsafe { CStr::from_ptr(msg) };
                eprintln!("Verification of LLVM module failed: {s:?}");
            }
        }

        let target_triple = target.map_or_else(
            || unsafe { target_machine::LLVMGetDefaultTargetTriple() as *const i8 },
            |target| target.as_ptr(),
        );
        let out_cstr = CString::new(out_file.as_os_str().as_encoded_bytes().to_vec())
            .map_err(|_| Error::InvalidOutFile)?;
        unsafe { emit::emit(llvm_module, target_triple, out_cstr.as_ptr())? };

        Ok(())
    }
}

struct Dialects {
    arith: ModuleOf<ir2::dialect::Arith>,
    tuple: ModuleOf<ir2::dialect::Tuple>,
    mem: ModuleOf<ir2::dialect::Mem>,
    cf: ModuleOf<ir2::dialect::Cf>,
}

struct Intrinsics {
    fshl: u32,
}
impl Intrinsics {
    fn lookup() -> Self {
        let lookup =
            |s: &CStr| unsafe { core::LLVMLookupIntrinsicID(s.as_ptr(), s.to_bytes().len() as _) };
        Self {
            fshl: lookup(c"llvm.fshl"),
        }
    }
}
