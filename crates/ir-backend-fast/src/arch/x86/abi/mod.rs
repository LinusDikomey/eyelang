use ir::mc::Abi;

use crate::arch::x86::X86;

mod systemv;

pub fn get_target_abi() -> &'static dyn Abi<X86> {
    // TODO: decide abi based on target
    &systemv::SystemV
}
