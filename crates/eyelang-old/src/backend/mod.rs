/// Emits C code
pub mod c;

/// General abstractions for generating machine code code
pub mod machine_code;

#[cfg(feature = "llvm-backend")]
/// Uses the LLVM library to emit LLVM IR
pub mod llvm;

pub mod x86_64;
