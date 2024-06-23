use std::{fmt, ops};

use ir::mc::{Operand, Register as _, VReg};

ir::mc::registers! { Register RegisterBits
        S8 => rax rbx rcx rdx rbp rsi rdi rsp;
        S4 => eax ebx ecx edx ebp esi edi esp;
        S2 =>  ax  bx  cx  dx  bp  si  di  sp;
        S1 =>  ah  bh  ch  dh;
        S1 =>  al  bl  cl  dl bpl sil dil spl;
        S8 => r8  r9  r10  r11  r12  r13  r14  r15;
        S4 => r8d r9d r10d r11d r12d r13d r14d r15d;
        S2 => r8w r9w r10w r11w r12w r13w r14w r15w;
        S1 => r8b r9b r10b r11b r12b r13b r14b r15b;
}
impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_str())
    }
}
impl Register {
    pub const fn bit(self) -> u16 {
        use Register::*;
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
        };
        1 << bit_index
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
pub struct RegisterBits(u16);
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
impl RegisterBits {
    const fn new() -> Self {
        Self(0)
    }

    const fn all() -> Self {
        Self(u16::MAX)
    }

    fn get(&self, r: Register) -> bool {
        self.0 & r.bit() != 0
    }

    fn set(&mut self, r: Register, set: bool) {
        let bit = r.bit();
        if set {
            self.0 |= bit;
        } else {
            self.0 &= !bit;
        }
    }
}

ir::mc::inst! { Inst Register
    addrr32 Reg: DefUse, Reg: Use;
    addri32 Reg: DefUse, Imm: Use;
    movrr32 Reg: Def, Reg: Use;
    movri32 Reg: Def, Imm: Use;
    call Func: Use; // TODO: clobbered and implicit regs, how to solve different number of args
    ret32 !implicit eax;
}

#[derive(Clone, Copy)]
pub enum MCValue {
    None,
    Undef,
    Imm(u64),
    Register(MCReg),
}

#[derive(Clone, Copy)]
pub enum MCReg {
    Register(Register),
    Virtual(VReg),
}
impl MCReg {
    pub fn op(self) -> Operand<Register> {
        match self {
            MCReg::Register(r) => Operand::Reg(r),
            MCReg::Virtual(r) => Operand::VReg(r),
        }
    }
}
