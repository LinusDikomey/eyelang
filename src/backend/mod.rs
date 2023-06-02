/// Emits C code
pub mod c;

#[cfg(feature = "llvm-backend")]
/// Uses the LLVM library to emit LLVM IR
pub mod llvm;

//pub mod x86;
