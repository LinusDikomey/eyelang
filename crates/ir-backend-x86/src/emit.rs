use std::{collections::VecDeque, hint::unreachable_unchecked};

use ir::mc::{MachineIR, MirBlock, Op, OpType};

use crate::isa::{Inst, Reg};

pub fn write(ir: &MachineIR<Inst>, text: &mut Vec<u8>) {
    let start = text.len();
    #[cold]
    fn op_error(expected: &'static str, found: Op<Reg>) -> ! {
        panic!("invalid instruction operand, expected {expected} but found value {found:?}")
    }

    fn r(a: u64) -> Reg {
        let a = Op::decode(a, OpType::Reg);
        let Op::Reg(a) = a else {
            op_error("Register", a)
        };
        a
    }

    fn m(a: u64, b: u64) -> (Reg, OffsetClass) {
        let a = Op::decode(a, OpType::Reg);
        let Op::Reg(a) = a else {
            op_error("Register", a)
        };
        (a, OffsetClass::from_imm(b as i64))
    }

    let mut block_queue = VecDeque::from([MirBlock::ENTRY]);
    let mut block_offsets: Box<[Option<u32>]> =
        vec![None; ir.block_count() as usize].into_boxed_slice();

    let mut missing_block_addrs = Vec::new();

    while let Some(block) = block_queue.pop_front() {
        let offset = &mut block_offsets[block.0 as usize];
        if offset.is_some() {
            continue;
        }
        *offset = Some((text.len() - start) as u32);
        println!("{:?} -> {:?}", block, ir.block_successors(block));
        block_queue.extend(ir.block_successors(block));

        for inst in ir.block_insts(block) {
            let rr = || (r(inst.ops[0]), r(inst.ops[1]));
            let ri = || (r(inst.ops[0]), inst.ops[1]);
            let rm = || (r(inst.ops[0]), m(inst.ops[1], inst.ops[2]));
            let mr = || (m(inst.ops[0], inst.ops[1]), r(inst.ops[2]));
            let mi = || (m(inst.ops[0], inst.ops[1]), inst.ops[2]);
            let b = || MirBlock(inst.ops[0] as u32);

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
                Inst::addri32 | Inst::addri64 => {
                    let wide = inst.inst == Inst::addri64;
                    let (a, b) = ri();
                    let modrm = encode_modrm_ri(a, wide);
                    if modrm.rex != 0 {
                        text.push(modrm.rex);
                    }
                    if b <= u8::MAX as u64 {
                        text.extend([0x83, modrm.modrm, b as u8]);
                    } else {
                        todo!("handle larger imm values");
                    }
                }
                Inst::subri64 => {
                    let (a, b) = ri();
                    let modrm = encode_modrm_ri(a, true);
                    if modrm.rex != 0 {
                        text.push(modrm.rex);
                    }
                    let o = 5;
                    if let Ok(b8) = b.try_into() {
                        text.extend([0x83, modrm.modrm | o << 3, b8]);
                    } else {
                        todo!("handle larger imm values");
                    }
                }
                Inst::movrr32 | Inst::movrr64 => {
                    let wide = inst.inst == Inst::movrr64;
                    let (a, b) = rr();
                    if a != b {
                        let modrm = encode_modrm_rr(a, b, wide);
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
                            text.push(REX | REX_B);
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
                Inst::push64 => {
                    let r = r(inst.ops[0]);
                    let (r, b) = encode_modrm_reg(r);
                    if b {
                        text.push(REX | REX_B);
                    }
                    text.push(0x50 + r);
                }
                Inst::pop64 => {
                    let r = r(inst.ops[0]);
                    let (r, b) = encode_modrm_reg(r);
                    if b {
                        text.push(REX | REX_B);
                    }
                    text.push(0x58 + r);
                }
                Inst::ret0 | Inst::ret32 => {
                    text.push(0xc3);
                }
                Inst::cmpri8 => {
                    let (r, imm) = ri();
                    let (r, b) = encode_modrm_reg(r);
                    if b {
                        text.push(REX | REX_B);
                    }
                    let imm8: Result<i8, _> = imm.try_into();
                    let o = 7;
                    text.extend([0x80, dbg!((0b11 << 6) | r | o << 3), imm8.unwrap() as u8]);
                }
                Inst::cmprr32 => {
                    let (a, b) = rr();
                    let modrm = encode_modrm_rr(a, b, false);
                    if modrm.rex != 0 {
                        text.push(REX);
                    }
                    text.extend([0x3B, modrm.modrm]);
                }
                Inst::cmpri32 => {
                    let (r, imm) = ri();
                    let (r, b) = encode_modrm_reg(r);
                    if b {
                        text.push(REX | REX_B);
                    }
                    let o = 7;
                    let imm8: Result<i8, _> = imm.try_into();
                    if let Ok(imm8) = imm8 {
                        text.extend([0x83, r | o << 3, imm8 as u8]);
                    } else {
                        todo!("larger immediate for cmp");
                    }
                }
                Inst::jmp => emit_jmp(
                    &[0xEB],
                    &[0xE9],
                    b(),
                    text,
                    start,
                    &block_offsets,
                    &mut missing_block_addrs,
                ),
                Inst::je => emit_jmp(
                    &[0x74],
                    &[0x0F, 0x84],
                    b(),
                    text,
                    start,
                    &block_offsets,
                    &mut missing_block_addrs,
                ),
                Inst::setz8
                | Inst::setnz8
                | Inst::setl8
                | Inst::setle8
                | Inst::setg8
                | Inst::setge8 => {
                    let r = r(inst.ops[0]);
                    let po = match inst.inst {
                        Inst::setz8 => 0x94,
                        Inst::setnz8 => 0x95,
                        Inst::setl8 => 0x9C,
                        Inst::setle8 => 0x9E,
                        Inst::setg8 => 0x9F,
                        Inst::setge8 => 0x9D,
                        _ => unsafe { unreachable_unchecked() },
                    };
                    let (r, b) = encode_modrm_reg(r);
                    if b {
                        text.push(REX | REX_B);
                    }
                    text.extend([0x0F, po, 0b11 << 6 | r]);
                }
            }
        }
    }
    for (offset_location, block) in missing_block_addrs {
        let block_offset = block_offsets[block.0 as usize].unwrap();
        let offset: i32 = (block_offset as i64 - offset_location as i64 - 4)
            .try_into()
            .unwrap();
        let i = start + offset_location as usize;
        text[i..i + 4].copy_from_slice(&offset.to_le_bytes());
    }
}

fn emit_jmp(
    rel8_op: &[u8],
    rel32_op: &[u8],
    target: MirBlock,
    text: &mut Vec<u8>,
    start: usize,
    block_offsets: &[Option<u32>],
    missing_block_addrs: &mut Vec<(u32, MirBlock)>,
) {
    let my_rel8_offset = (text.len() + rel8_op.len() - start + 1) as u32;
    if let Some(known) = block_offsets[target.0 as usize] {
        let offset: i32 = (known as i64 - my_rel8_offset as i64).try_into().unwrap();
        let offset8: Result<i8, _> = offset.try_into();
        if let Ok(offset8) = offset8 {
            text.extend(rel8_op);
            text.push(offset8 as u8);
        } else {
            text.extend(rel32_op);
            let offset: i32 = (known as i64 - (text.len() - start + 4) as i64)
                .try_into()
                .unwrap();
            text.extend(offset.to_le_bytes());
        }
    } else {
        text.extend(rel32_op);
        let offset = (text.len() - start) as u32;
        missing_block_addrs.push((offset, target));
        text.extend(0i32.to_le_bytes());
    }
}

const REX: u8 = 0b0100_0001;
const REX_B: u8 = 1 << 0;
const REX_X: u8 = 1 << 1;
const REX_R: u8 = 1 << 2;
const REX_W: u8 = 1 << 3;

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
fn encode_modrm_reg(r: Reg) -> (u8, bool) {
    use Reg::*;
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

fn encode_modrm_rr(reg_a: Reg, reg_b: Reg, wide: bool) -> Modrm {
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

fn encode_modrm_rm(reg_val: Reg, reg_ptr: Reg, off: OffsetClass, wide: bool) -> Modrm {
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

fn encode_modrm_mr(reg_ptr: Reg, off: OffsetClass, reg_val: Reg, wide: bool) -> Modrm {
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

fn encode_modrm_ri(reg: Reg, wide: bool) -> Modrm {
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
