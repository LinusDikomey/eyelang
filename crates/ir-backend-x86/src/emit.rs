use ir::mc::{MachineIR, OpType, Operand};

use crate::machine_ir::{Inst, Register};

pub fn write(ir: &MachineIR<Inst>, text: &mut Vec<u8>) {
    #[cold]
    fn op_error(expected: &'static str, found: Operand<Register>) -> ! {
        panic!("invalid instruction operand, expected {expected} but found value {found:?}")
    }
    for inst in &ir.insts {
        let r = |a: u64| {
            let a = Operand::decode(a, OpType::Reg);
            let Operand::Reg(a) = a else {
                op_error("Register", a)
            };
            a
        };
        let m = |a: u64, b: u64| {
            let a = Operand::decode(a, OpType::Reg);
            let Operand::Reg(a) = a else {
                op_error("Register", a)
            };
            (a, OffsetClass::from_imm(b as i64))
        };

        let rr = || (r(inst.ops[0]), r(inst.ops[1]));
        let ri = || (r(inst.ops[0]), inst.ops[1]);
        let rm = || (r(inst.ops[0]), m(inst.ops[1], inst.ops[2]));
        let mr = || (m(inst.ops[0], inst.ops[1]), r(inst.ops[2]));
        let mi = || (m(inst.ops[0], inst.ops[1]), inst.ops[2]);

        match inst.inst {
            Inst::addrr32 => {
                let (a, b) = rr();
                let modrm = encode_modrm_rr(a, b, false);
                if modrm.rex != 0 {
                    text.push(modrm.rex);
                }
                text.extend([0x01, modrm.modrm]);
            }
            Inst::addrm32 => {
                let (r, (ptr, off)) = rm();
                let modrm = encode_modrm_rm(r, ptr, off, false);
                if modrm.rex != 0 {
                    text.push(modrm.rex);
                }
                text.extend([0x03, modrm.modrm]);
                off.write(text);
            }
            Inst::addri32 => {
                let (a, b) = ri();
                let modrm = encode_modrm_ri(a, false);
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
                    let modrm = encode_modrm_rr(a, b, false);
                    if modrm.rex != 0 {
                        text.push(modrm.rex);
                    }
                    text.extend([0x89, modrm.modrm]);
                }
            }
            Inst::movri32 => {
                let (a, b) = ri();
                let modrm = encode_modrm_ri(a, false);
                if modrm.rex != 0 {
                    text.push(modrm.rex);
                }
                if b <= u32::MAX as u64 {
                    let [b0, b1, b2, b3] = (b as u32).to_le_bytes();
                    let (r, b) = encode_modrm_reg(a);
                    if b {
                        // REX byte
                        text.push(0b0100_0001);
                    }
                    text.extend([0xB8 + r, modrm.modrm, b0, b1, b2, b3]);
                } else {
                    todo!("handle larger immediate values")
                }
            }
            Inst::movrm32 => {
                let (r, (ptr, off)) = rm();
                let modrm = encode_modrm_rm(r, ptr, off, false);
                if modrm.rex != 0 {
                    text.push(modrm.rex);
                }
                text.extend([0x8b, modrm.modrm]);
                off.write(text);
            }
            Inst::movmr32 => {
                let ((ptr, off), r) = mr();
                let modrm = encode_modrm_mr(ptr, off, r, false);
                if modrm.rex != 0 {
                    text.push(modrm.rex);
                }
                text.extend([0x89, modrm.modrm]);
                off.write(text);
            }
            Inst::movmi32 => {
                let ((reg, off), i) = mi();
                let (reg, b) = encode_modrm_reg(reg);
                let modrm = reg | off.modrm_bits();
                if b {
                    // REX byte
                    text.push(0b0100_0100);
                }
                text.extend([0xC7, modrm]);
                off.write(text);
                let imm = i as i64;
                let imm32: Result<i32, _> = imm.try_into();
                text.extend(imm32.expect("immediate too large").to_le_bytes());
            }
            Inst::call => todo!(),
            Inst::ret0 | Inst::ret32 => {
                text.push(0xc3);
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum OffsetClass {
    Zero,
    Byte(i8),
    DWord(i32),
}
impl OffsetClass {
    fn from_imm(value: i64) -> Self {
        if value == 0 {
            Self::Zero
        } else if let Ok(b) = value.try_into() {
            Self::Byte(b)
        } else {
            Self::DWord(value.try_into().expect("encoded offset too large"))
        }
    }

    fn modrm_bits(self) -> u8 {
        (match self {
            OffsetClass::Zero => 0b00,
            OffsetClass::Byte(_) => 0b01,
            OffsetClass::DWord(_) => 0b10,
        }) << 6
    }

    fn write(self, text: &mut Vec<u8>) {
        match self {
            OffsetClass::Zero => {}
            OffsetClass::Byte(b) => text.push(b as u8),
            OffsetClass::DWord(dw) => text.extend((dw as u32).to_le_bytes()),
        }
    }
}

struct Modrm {
    rex: u8,
    modrm: u8,
}
#[rustfmt::skip]
fn encode_modrm_reg(r: Register) -> (u8, bool) {
    use Register::*;
    let mut b = false;

    let modrm = match r {
        rax | eax => 0b_000,
        rcx | ecx => 0b_001,
        rdx | edx => 0b_010,
        rbx | ebx => 0b_011,
        rsp | esp => 0b_100,
        rsi | esi => 0b_110,
        rdi | edi => 0b_111,
        r8  | r8d => { b = true; 0b_000 }
        r9  | r9d => { b = true; 0b_001 }
        r10  | r10d => { b = true; 0b_010 }
        r11  | r11d => { b = true; 0b_011 }
        r12  | r12d => { b = true; 0b_100 }
        r13  | r13d => { b = true; 0b_101 }
        r14  | r14d => { b = true; 0b_110 }
        r15  | r15d => { b = true; 0b_111 }
        rbp => 0b_101,
        reg => todo!("encode {reg:?}"),
    };
    (modrm, b)
}

fn encode_modrm_rr(reg_a: Register, reg_b: Register, wide: bool) -> Modrm {
    let (modrm_a, r) = encode_modrm_reg(reg_a);
    let (modrm_b, b) = encode_modrm_reg(reg_b);
    let rex = if wide || r || b {
        0b_0100_0000 | ((wide as u8) << 3) | ((r as u8) << 2) | ((b as u8) << 0)
    } else {
        0
    };
    Modrm {
        rex,
        modrm: modrm_a | modrm_b << 3 | 0b11 << 6,
    }
}

fn encode_modrm_rm(reg_val: Register, reg_ptr: Register, off: OffsetClass, wide: bool) -> Modrm {
    let (modrm_a, r) = encode_modrm_reg(reg_val);
    let (modrm_b, b) = encode_modrm_reg(reg_ptr);
    let rex = if wide || r || b {
        0b_0100_0000 | ((wide as u8) << 3) | ((r as u8) << 2) | ((b as u8) << 0)
    } else {
        0
    };
    Modrm {
        rex,
        modrm: modrm_a << 3 | modrm_b | off.modrm_bits(),
    }
}

fn encode_modrm_mr(reg_ptr: Register, off: OffsetClass, reg_val: Register, wide: bool) -> Modrm {
    let (modrm_a, r) = encode_modrm_reg(reg_ptr);
    let (modrm_b, b) = encode_modrm_reg(reg_val);
    let rex = if wide || r || b {
        0b_0100_0000 | ((wide as u8) << 3) | ((r as u8) << 2) | ((b as u8) << 0)
    } else {
        0
    };
    Modrm {
        rex,
        modrm: modrm_a | modrm_b << 3 | off.modrm_bits(),
    }
}

fn encode_modrm_ri(reg: Register, wide: bool) -> Modrm {
    let (modrm_a, r) = encode_modrm_reg(reg);
    let rex = if wide || r {
        0b_0100_0000 | ((wide as u8) << 3) | ((r as u8) << 2)
    } else {
        0
    };
    Modrm {
        rex,
        modrm: modrm_a | if true { 0b1100_0000 } else { 0 },
    }
}
