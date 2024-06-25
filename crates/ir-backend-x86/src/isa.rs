use std::{fmt, ops};

use ir::mc::Register as _;

ir::mc::registers! { Reg RegisterBits
    S64 => rax rbx rcx rdx rbp rsi rdi rsp;
    S32 => eax ebx ecx edx ebp esi edi esp;
    S16 =>  ax  bx  cx  dx  bp  si  di  sp;
    S8 =>  ah  bh  ch  dh;
    S8 =>  al  bl  cl  dl bpl sil dil spl;
    S64 => r8  r9  r10  r11  r12  r13  r14  r15;
    S32 => r8d r9d r10d r11d r12d r13d r14d r15d;
    S16 => r8w r9w r10w r11w r12w r13w r14w r15w;
    S8 => r8b r9b r10b r11b r12b r13b r14b r15b;
    S1 => eflags;
}
impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_str())
    }
}
impl Reg {
    pub const fn bit(self) -> u32 {
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
        1 << bit_index
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
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
impl RegisterBits {
    const fn new() -> Self {
        Self(0)
    }

    const fn all() -> Self {
        Self(0x0001FFFF)
    }

    fn get(&self, r: Reg) -> bool {
        self.0 & r.bit() != 0
    }

    fn set(&mut self, r: Reg, set: bool) {
        let bit = r.bit();
        if set {
            self.0 |= bit;
        } else {
            self.0 &= !bit;
        }
    }
}

ir::mc::inst! { Inst Reg
    addrr32 Reg: DefUse, Reg: Use           !implicit_def eflags;
    addri32 Reg: DefUse, Imm: Use           !implicit_def eflags;
    addri64 Reg: DefUse, Imm: Use           !implicit_def eflags;
    addrm32 Reg: DefUse, Reg: Use, Imm: Use !implicit_def eflags;

    subri64 Reg: DefUse, Imm: Use;

    movrr32 Reg: Def, Reg: Use;
    movrr64 Reg: Def, Reg: Use;

    movri32 Reg: Def, Imm: Use;
    movrm32 Reg: Def, Reg: Use, Imm: Use;
    movmr32 Reg: Use, Imm: Use, Reg: Use;
    movmi32 Reg: Use, Imm: Use, Imm: Use;


    call    Fun: Use; // TODO: clobbered and implicit regs, how to solve different number of args
    push64  Reg: Use;
    pop64   Reg: Def;

    // we differentiate between different return value sizes to properly model implicit register
    // dependencies
    ret0;
    ret32 !implicit eax;

    cmpri8  Reg: Use, Imm: Use !implicit_def eflags;
    cmprr32 Reg: Use, Reg: Use !implicit_def eflags;
    cmpri32 Reg: Use, Imm: Use !implicit_def eflags;
    jmp Blk: Use;
    je Blk: Use !implicit eflags;

    setz8  Reg: Def !implicit eflags;
    setnz8 Reg: Def !implicit eflags;
    setl8  Reg: Def !implicit eflags;
    setle8 Reg: Def !implicit eflags;
    setg8  Reg: Def !implicit eflags;
    setge8 Reg: Def !implicit eflags;
}
