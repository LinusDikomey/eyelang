use ir::mc::{MachineIR, OpType, Operand, SizeClass};

use crate::machine_ir::{Inst, Register};

pub fn write(ir: &MachineIR<Inst>, text: &mut Vec<u8>) {
    #[cold]
    fn op_error(expected: &'static str, found: Operand<Register>) -> ! {
        panic!("invalid instruction operand, expected {expected} but found value {found:?}")
    }
    for inst in &ir.insts {
        let rr = || {
            let a = Operand::decode(inst.ops[0], OpType::Reg);
            let b = Operand::decode(inst.ops[1], OpType::Reg);
            let Operand::Reg(a) = a else {
                op_error("Register", a)
            };
            let Operand::Reg(b) = b else {
                op_error("Register", b)
            };
            (a, b)
        };
        let ri = || {
            let a = Operand::decode(inst.ops[0], OpType::Reg);
            let b = Operand::decode(inst.ops[1], OpType::Imm);
            let Operand::Reg(a) = a else {
                op_error("Register", a)
            };
            let Operand::Imm(b) = b else {
                op_error("Immediate", b)
            };
            (a, b)
        };
        match inst.inst {
            Inst::addrr32 => {
                let (a, b) = rr();
                let modrm = encode_modrm_rr(a, b);
                if modrm.rex != 0 {
                    text.push(modrm.rex);
                }
                text.extend([0x01, modrm.modrm]);
            }
            Inst::addri32 => {
                let (a, b) = ri();
                let modrm = encode_modrm_ri(a);
                if modrm.rex != 0 {
                    text.push(modrm.rex);
                }
                if b <= u8::MAX as u64 {
                    text.extend([0x83, modrm.modrm, b as u8]);
                } else {
                    todo!("handle larger immediate values")
                }
            }
            Inst::movrr32 => {
                let (a, b) = rr();
                if a != b {
                    let modrm = encode_modrm_rr(a, b);
                    if modrm.rex != 0 {
                        text.push(modrm.rex);
                    }
                    text.extend([0x89, modrm.modrm]);
                }
            }
            Inst::movri32 => {
                let (a, b) = ri();
                let modrm = encode_modrm_ri(a);
                if modrm.rex != 0 {
                    text.push(modrm.rex);
                }
                if b <= u32::MAX as u64 {
                    let [b0, b1, b2, b3] = (b as u32).to_le_bytes();
                    let (r, b) = encode_modrm_reg(a, &mut false, &mut false);
                    if b {
                        // REX byte
                        text.push(0b0100_0001);
                    }
                    text.extend([0xB8 + r, modrm.modrm, b0, b1, b2, b3]);
                } else {
                    todo!("handle larger immediate values")
                }
            }
            Inst::call => todo!(),
            Inst::ret32 => {
                text.push(0xc3);
            }
        }
    }
}

struct Modrm {
    rex: u8,
    modrm: u8,
}
#[rustfmt::skip]
fn encode_modrm_reg(r: Register, wide: &mut bool, mod_: &mut bool) -> (u8, bool) {
    use Register::*;
    let mut b = false;
    if r.size() == SizeClass::S8 { *wide = true; }

    let modrm = match r {
        rax | eax => 0b_000,
        rcx | ecx => 0b_001,
        rdx | edx => 0b_010,
        rbx | ebx => 0b_011,
        rsp | esp => { *mod_ = true; 0b_100 }
        rsi | esi => 0b_110,
        rdi | edi => 0b_111,
        r8  | r8d => { b = true; 0b_000 }
        r9  | r9d => { b = true; 0b_001 }
        r10  | r10d => { b = true; 0b_010 }
        r11  | r11d => { b = true; 0b_011 }
        r12  | r12d => { *mod_ = true; b = true; 0b_100 }
        r13  | r13d => { *mod_ = true; b = true; 0b_101 }
        r14  | r14d => { b = true; 0b_110 }
        r15  | r15d => { b = true; 0b_111 }
        reg => todo!("encode {reg:?}"),
    };
    (modrm, b)
}
fn encode_modrm_rr(reg_a: Register, reg_b: Register) -> Modrm {
    let mut mod_ = false;
    let mut w = false;
    let (modrm_a, r) = encode_modrm_reg(reg_a, &mut w, &mut mod_);
    let (modrm_b, b) = encode_modrm_reg(reg_b, &mut w, &mut mod_);
    let rex = if w || r || b {
        0b_0100_0000 | ((w as u8) << 3) | ((r as u8) << 2) | ((b as u8) << 0)
    } else {
        0
    };
    Modrm {
        rex,
        modrm: modrm_a | modrm_b << 3 | if true { 0b1100_0000 } else { 0 },
    }
}

fn encode_modrm_ri(reg: Register) -> Modrm {
    let mut mod_ = false;
    let mut w = false;
    let (modrm_a, r) = encode_modrm_reg(reg, &mut w, &mut mod_);
    let rex = if w || r {
        0b_0100_0000 | ((w as u8) << 3) | ((r as u8) << 2)
    } else {
        0
    };
    Modrm {
        rex,
        modrm: modrm_a | if true { 0b1100_0000 } else { 0 },
    }
}
