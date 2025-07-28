use std::{fmt, ops};

use ir::{
    Usage,
    mc::{Abi, McInst, Register},
};

ir::mc::registers! { Reg RegisterBits
    GP64 => rax rbx rcx rdx rbp rsi rdi rsp;
    GP32 => eax ebx ecx edx ebp esi edi esp;
    GP16 => ax  bx  cx  dx  bp  si  di  sp;
    GP8 =>  al  bl  cl  dl  bpl sil dil spl;
    GP8 =>  ah  bh  ch  dh;
    GP64 => r8  r9  r10  r11  r12  r13  r14  r15;
    GP32 => r8d r9d r10d r11d r12d r13d r14d r15d;
    GP16 => r8w r9w r10w r11w r12w r13w r14w r15w;
    GP8 => r8b r9b r10b r11b r12b r13b r14b r15b;
    Flags => eflags;
}

pub const TMP_REGISTER: Reg = Reg::r15;
pub const PREOCCUPIED_REGISTERS: RegisterBits =
    RegisterBits(Reg::rbp.bit().0 | Reg::rsp.bit().0 | TMP_REGISTER.bit().0);

impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_str())
    }
}
impl Reg {
    pub const fn bit(self) -> RegisterBits {
        use Reg::*;
        let bit_index = match self {
            rax | eax | ax | ah | al => 0,
            rbx | ebx | bx | bh | bl => 1,
            rcx | ecx | cx | ch | cl => 2,
            rdx | edx | dx | dh | dl => 3,
            rbp | ebp | bp | bpl => 4,
            rsi | esi | si | sil => 5,
            rdi | edi | di | dil => 6,
            rsp | esp | sp | spl => 7,
            r8 | r8d | r8w | r8b => 8,
            r9 | r9d | r9w | r9b => 9,
            r10 | r10d | r10w | r10b => 10,
            r11 | r11d | r11w | r11b => 11,
            r12 | r12d | r12w | r12b => 12,
            r13 | r13d | r13w | r13b => 13,
            r14 | r14d | r14w | r14b => 14,
            r15 | r15d | r15w | r15b => 15,
            eflags => 16,
        };
        RegisterBits(1 << bit_index)
    }

    pub const UNIQUE_BITS: [Self; 17] = [
        Self::rax,
        Self::rbx,
        Self::rcx,
        Self::rdx,
        Self::rbp,
        Self::rsi,
        Self::rdi,
        Self::rsp,
        Self::r8,
        Self::r9,
        Self::r10,
        Self::r11,
        Self::r12,
        Self::r13,
        Self::r14,
        Self::r15,
        Self::eflags,
    ];
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RegisterBits(u32);
impl ops::Not for RegisterBits {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}
impl ops::BitAnd for RegisterBits {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}
impl ops::BitOr for RegisterBits {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}
impl RegisterBits {
    pub const fn new() -> Self {
        Self(0)
    }

    const fn all() -> Self {
        Self(0x0001FFFF)
    }

    fn get(&self, r: Reg) -> bool {
        self.0 & r.bit().0 != 0
    }

    fn set(&mut self, r: Reg, set: bool) {
        let bit = r.bit();
        if set {
            self.0 |= bit.0;
        } else {
            self.0 &= !bit.0;
        }
    }
}

ir::instructions! {
    X86 "x86" X86Insts

    push_r64 reg: MCReg(Usage::Use);
    pop_r64 reg: MCReg(Usage::Def);

    mov_ri8 to: MCReg(Usage::Def) i: Int32;
    mov_ri16 to: MCReg(Usage::Def) i: Int32;
    mov_ri32 to: MCReg(Usage::Def) i: Int32;
    mov_ri64 to: MCReg(Usage::Def) i: Int32;

    mov_rr32 to: MCReg(Usage::Def) from: MCReg(Usage::Use);
    mov_rr64 to: MCReg(Usage::Def) from: MCReg(Usage::Use);

    mov_rm8  to: MCReg(Usage::Def) from: MCReg(Usage::Use) offset: Int32;
    mov_rm16 to: MCReg(Usage::Def) from: MCReg(Usage::Use) offset: Int32;
    mov_rm32 to: MCReg(Usage::Def) from: MCReg(Usage::Use) offset: Int32;
    mov_rm64 to: MCReg(Usage::Def) from: MCReg(Usage::Use) offset: Int32;

    mov_mr8  to: MCReg(Usage::Use) offset: Int32 from: MCReg(Usage::Use);
    mov_mr16 to: MCReg(Usage::Use) offset: Int32 from: MCReg(Usage::Use);
    mov_mr32 to: MCReg(Usage::Use) offset: Int32 from: MCReg(Usage::Use);
    mov_mr64 to: MCReg(Usage::Use) offset: Int32 from: MCReg(Usage::Use);

    ret0 !terminator;
    ret64 !terminator;
    ret128 !terminator;


    jmp addr: BlockId !terminator;
    jl addr: BlockId;

    cmp_rr32 a: MCReg(Usage::Use) b: MCReg(Usage::Use);

    add_rr8 a: MCReg(Usage::DefUse) b: MCReg(Usage::DefUse);
    add_rr16 a: MCReg(Usage::DefUse) b: MCReg(Usage::DefUse);
    add_rr32 a: MCReg(Usage::DefUse) b: MCReg(Usage::DefUse);
    add_rr64 a: MCReg(Usage::DefUse) b: MCReg(Usage::DefUse);

    add_ri64 reg: MCReg(Usage::DefUse) imm: Int32;

    sub_rr8 a: MCReg(Usage::DefUse) b: MCReg(Usage::DefUse);
    sub_rr16 a: MCReg(Usage::DefUse) b: MCReg(Usage::DefUse);
    sub_rr32 a: MCReg(Usage::DefUse) b: MCReg(Usage::DefUse);
    sub_rr64 a: MCReg(Usage::DefUse) b: MCReg(Usage::DefUse);

    sub_ri64 reg: MCReg(Usage::DefUse) imm: Int32;


    neg_r8 a: MCReg(Usage::DefUse);
    neg_r32 a: MCReg(Usage::DefUse);
    neg_r64 a: MCReg(Usage::DefUse);

    lea_rm32 to: MCReg(Usage::Def) addr: MCReg(Usage::Use) offset: Int32;
    lea_rm64 to: MCReg(Usage::Def) addr: MCReg(Usage::Use) offset: Int32;

    call_function function: FunctionId;
}
impl McInst for X86 {
    type Reg = Reg;
    fn implicit_def(&self, abi: &'static dyn Abi<Self>) -> RegisterBits {
        match self {
            Self::push_r64 | Self::pop_r64 => Reg::rsp.bit(),
            Self::cmp_rr32 => Reg::eflags.bit(),
            Self::add_rr8 | Self::add_rr16 | Self::add_rr32 | Self::add_rr64 => Reg::eflags.bit(),
            Self::sub_rr8 | Self::sub_rr16 | Self::sub_rr32 | Self::sub_rr64 => Reg::eflags.bit(),
            Self::call_function => abi.caller_saved(),
            _ => Reg::NO_BITS,
        }
    }

    fn implicit_use(&self, abi: &'static dyn Abi<Self>) -> RegisterBits {
        match self {
            Self::push_r64 | Self::pop_r64 => Reg::rsp.bit(),
            Self::jl => Reg::eflags.bit(),
            Self::ret64 => abi.return_regs(1),
            Self::ret128 => abi.return_regs(2),
            _ => Reg::NO_BITS,
        }
    }
}
impl X86 {
    pub fn is_ret(&self) -> bool {
        matches!(self, Self::ret0 | Self::ret64 | Self::ret128)
    }
}
