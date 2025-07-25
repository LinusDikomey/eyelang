use std::collections::VecDeque;

use ir::{
    Argument, BlockId, Environment, FunctionIr, MCReg, ModuleOf,
    block_graph::Blocks,
    mc::{Mc, ParcopySolver, RegClass},
    parameter_types::Int32,
};

use super::isa::{Reg, X86};

pub fn write(
    env: &Environment,
    mc: ModuleOf<Mc>,
    x86: ModuleOf<X86>,
    ir: &FunctionIr,
    text: &mut Vec<u8>,
) {
    let mut parcopy = ParcopySolver::new();
    let start = text.len();
    let mut block_queue = VecDeque::from([BlockId::ENTRY]);
    let mut block_offsets: Box<[Option<u32>]> =
        vec![None; ir.block_count() as usize].into_boxed_slice();

    let mut missing_block_addrs: Vec<(u32, BlockId)> = Vec::new();

    while let Some(block) = block_queue.pop_front() {
        let offset = &mut block_offsets[block.idx()];
        if offset.is_some() {
            continue;
        }
        *offset = Some((text.len() - start) as u32);
        block_queue.extend(ir.successors(env, block).iter());

        for (r, i) in ir.get_block(block) {
            if let Some(inst) = i.as_module(mc) {
                match inst.op() {
                    Mc::IncomingBlockArgs => {}
                    Mc::Copy | Mc::AssignBlockArgs => {
                        let args = ir.args_iter(i, env).map(|arg| {
                            let Argument::MCReg(r) = arg else {
                                unreachable!()
                            };
                            r
                        });
                        parcopy.parcopy(
                            args,
                            |to, from| {
                                // FIXME: assumes 32 bits right now
                                let to = to.phys().unwrap();
                                let from: Reg = from.phys().unwrap();
                                let mut wide = false;
                                let opcode = match from.class() {
                                    RegClass::GP8 => 0x88,
                                    RegClass::GP16 => 0x89,
                                    RegClass::GP32 => 0x89,
                                    RegClass::GP64 => {
                                        wide = true;
                                        0x89
                                    }
                                    RegClass::F32 => todo!(),
                                    RegClass::F64 => todo!(),
                                    RegClass::Flags => todo!(),
                                };
                                let (ra, r) = encode_reg(to);
                                let (rb, b) = encode_reg(from);
                                // HACK: currently checking the encoded registers to see if they
                                // are the same. This shouldn't be necessary but right now, the
                                // register size might be wrong after regalloc so only the encoded
                                // registers will be equal.
                                if ra != rb || r != b {
                                    let rex = encode_rex(wide, r, false, b);
                                    let modrm = MODRM_RR | (rb << 3) | ra;
                                    if rex != 0 {
                                        text.push(rex);
                                    }
                                    text.extend([opcode, modrm]);
                                }
                            },
                            MCReg::from_phys(super::TMP_REGISTER),
                        );
                    }
                }
                continue;
            }
            let Some(inst) = i.as_module(x86) else {
                panic!("expected x86 instruction but encountered other module at {r:?}");
            };

            use X86 as I;
            match inst.op() {
                I::push_r64 | I::pop_r64 => {
                    let (r, b) = encode_reg(ir.args(i, env));
                    let rex = encode_rex(false, false, false, b);
                    if rex != 0 {
                        text.push(rex);
                    }
                    let opcode = if inst.op() == I::push_r64 { 0x50 } else { 0x58 };
                    text.push(opcode + r);
                }
                I::mov_ri8 => {
                    let (a, imm): (Reg, u32) = ir.args(i, env);
                    let imm8: i8 = (imm as i32).try_into().unwrap();
                    let (ra, b) = encode_reg(a);
                    let rex = encode_rex(false, false, false, b);
                    if rex != 0 {
                        text.push(rex);
                    }
                    text.extend([0xB0 + ra, imm8 as u8]);
                }
                I::mov_ri16 => {
                    let (a, imm): (Reg, u32) = ir.args(i, env);
                    let imm16: i16 = (imm as i32).try_into().unwrap();
                    let (ra, b) = encode_reg(a);
                    let rex = encode_rex(false, false, false, b);
                    if rex != 0 {
                        text.push(rex);
                    }
                    text.extend([0xB8 + ra]);
                    text.extend(imm16.to_le_bytes());
                }
                I::mov_ri32 => {
                    let (a, imm): (Reg, u32) = ir.args(i, env);
                    let (ra, b) = encode_reg(a);
                    let rex = encode_rex(false, false, false, b);
                    if rex != 0 {
                        text.push(rex);
                    }
                    text.extend([0xB8 + ra]);
                    text.extend(imm.to_le_bytes());
                }
                I::mov_ri64 => inst_ri(text, &[0xC7], ir.args(i, env), true, 0),
                I::mov_rr32 | I::mov_rr64 => {
                    inst_rr(text, &[0x89], ir.args(i, env), inst.op() == I::mov_rr64)
                }
                I::mov_rm8 => inst_rm(text, &[0x8A], ir.args(i, env), false),
                I::mov_rm16 => inst_rm(text, &[0x8B], ir.args(i, env), false),
                I::mov_rm32 | I::mov_rm64 => {
                    inst_rm(text, &[0x8B], ir.args(i, env), inst.op() == I::mov_rm64)
                }
                I::mov_mr8 => inst_mr(text, &[0x88], ir.args(i, env), false),
                I::mov_mr16 => inst_mr(text, &[0x89], ir.args(i, env), false),
                I::mov_mr32 | I::mov_mr64 => {
                    inst_mr(text, &[0x89], ir.args(i, env), inst.op() == I::mov_mr64)
                }
                I::ret0 | I::ret64 | I::ret128 => {
                    text.push(0xc3);
                }
                I::cmp_rr32 => {
                    let (a, b) = ir.args(i, env);
                    let modrm = encode_modrm_rr(b, a, false);
                    if modrm.rex != 0 {
                        text.push(modrm.rex);
                    }
                    text.extend([0x3B, modrm.modrm]);
                }
                I::jmp => {
                    let target = ir.args(i, env);
                    emit_jmp(
                        &[0xEB],
                        &[0xE9],
                        target,
                        text,
                        start,
                        &block_offsets,
                        &mut missing_block_addrs,
                    );
                }
                I::jl => {
                    let target = ir.args(i, env);
                    emit_jmp(
                        &[0x7C, 0xCB],
                        &[0x0F, 0x8C],
                        target,
                        text,
                        start,
                        &block_offsets,
                        &mut missing_block_addrs,
                    );
                }
                I::add_rr8 => inst_rr(text, &[0x00], ir.args(i, env), false),
                I::add_rr16 => inst_rr(text, &[0x01], ir.args(i, env), false),
                I::add_rr32 | I::add_rr64 => {
                    inst_rr(text, &[0x01], ir.args(i, env), inst.op() == I::add_rr64)
                }
                I::add_ri64 => inst_ri(text, &[0x81], ir.args(i, env), true, 0),

                I::sub_rr8 | I::sub_rr16 | I::sub_rr32 | I::sub_rr64 => todo!("sub"),

                I::sub_ri64 => inst_ri(text, &[0x81], ir.args(i, env), true, 5),

                I::neg_r8 => inst_r(text, &[0xF6], ir.args(i, env), 3, false),
                I::neg_r32 => inst_r(text, &[0xF7], ir.args(i, env), 3, false),
                I::neg_r64 => inst_r(text, &[0xF7], ir.args(i, env), 3, true),
                I::lea_rm32 | I::lea_rm64 => {
                    let opcode: &[u8] = &[0x8D];
                    let (reg_val, reg_ptr, off) = ir.args(i, env);
                    let wide = inst.op() == I::lea_rm64;
                    let off = OffsetClass::from_imm(off);
                    let (modrm_a, r) = encode_reg(reg_val);
                    let (modrm_b, b) = encode_reg(reg_ptr);
                    let rex = encode_rex(wide, r, false, b);
                    if rex != 0 {
                        text.push(rex);
                    }
                    text.extend(opcode);
                    text.push(off.modrm_bits() | (modrm_a << 3) | modrm_b);
                    //text.push(0x24); // wtf
                    off.write(text);
                }
            }
        }
    }
    for (offset_location, block) in missing_block_addrs {
        let block_offset = block_offsets[block.idx()].unwrap();
        let offset: i32 = (block_offset as i64 - offset_location as i64 - 4)
            .try_into()
            .unwrap();
        let i = start + offset_location as usize;
        text[i..i + 4].copy_from_slice(&offset.to_le_bytes());
    }
}

fn inst_r(text: &mut Vec<u8>, opcode: &[u8], a: Reg, extension: u8, wide: bool) {
    let modrm = encode_modrm_r(a, wide, extension);
    if modrm.rex != 0 {
        text.push(modrm.rex);
    }
    text.extend(opcode);
    text.push(modrm.modrm);
}

fn inst_rr(text: &mut Vec<u8>, opcode: &[u8], (a, b): (Reg, Reg), wide: bool) {
    let modrm = encode_modrm_rr(a, b, wide);
    if modrm.rex != 0 {
        text.push(modrm.rex);
    }
    text.extend(opcode);
    text.push(modrm.modrm);
}

fn inst_rm(
    text: &mut Vec<u8>,
    opcode: &[u8],
    (reg_val, reg_ptr, off): (Reg, Reg, Int32),
    wide: bool,
) {
    let off = OffsetClass::from_imm(off);
    let (modrm_a, r) = encode_reg(reg_val);
    let (modrm_b, b) = encode_reg(reg_ptr);
    let rex = encode_rex(wide, r, false, b);
    if rex != 0 {
        text.push(rex);
    }
    text.extend(opcode);
    text.push(off.modrm_bits() | (modrm_a << 3) | modrm_b);
    off.write(text);
}

fn inst_mr(
    text: &mut Vec<u8>,
    opcode: &[u8],
    (reg_ptr, off, reg_val): (Reg, Int32, Reg),
    wide: bool,
) {
    // encoded exactly the same way, just swap the arguments around correctly
    inst_rm(text, opcode, (reg_val, reg_ptr, off), wide);
}

fn inst_ri(text: &mut Vec<u8>, opcode: &[u8], (r, imm): (Reg, u32), wide: bool, i: u8) {
    let modrm = encode_modrm_ri(r, wide, i);
    if modrm.rex != 0 {
        text.push(modrm.rex);
    }
    text.extend(opcode);
    text.push(modrm.modrm);
    text.extend(imm.to_le_bytes());
}

/*
fn inst_mi(
    text: &mut Vec<u8>,
    opcode: &[u8],
    wide: bool,
    ((reg, off), i): ((Reg, OffsetClass), u64),
) {
    let (reg, b) = encode_reg(reg);
    let modrm = reg | off.modrm_bits();
    let rex = encode_rex(wide, false, false, b);
    if rex != 0 {
        text.push(rex);
    }
    text.extend(opcode);
    text.push(modrm);
    off.write(text);
    let imm = i as i64;
    let imm32: Result<i32, _> = imm.try_into();
    text.extend(imm32.expect("immediate too large").to_le_bytes());
}
*/

fn emit_jmp(
    rel8_op: &[u8],
    rel32_op: &[u8],
    target: BlockId,
    text: &mut Vec<u8>,
    start: usize,
    block_offsets: &[Option<u32>],
    missing_block_addrs: &mut Vec<(u32, BlockId)>,
) {
    let my_rel8_offset = (text.len() + rel8_op.len() - start + 1) as u32;
    if let Some(known) = block_offsets[target.idx()] {
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

//const PRECISION_16: u8 = 0x66;

#[derive(Debug, Clone, Copy)]
enum OffsetClass {
    Zero,
    Byte(i8),
    DWord(i32),
}
impl OffsetClass {
    fn from_imm(value: u32) -> Self {
        let value = value as i32;
        if value == 0 {
            Self::Zero
        } else if let Ok(b) = value.try_into() {
            Self::Byte(b)
        } else {
            Self::DWord(value)
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
            OffsetClass::DWord(dw) => text.extend(dw.to_le_bytes()),
        }
    }
}

struct Modrm {
    rex: u8,
    modrm: u8,
}
#[rustfmt::skip]
fn encode_reg(r: Reg) -> (u8, bool) {
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

const MODRM_RR: u8 = 0b1100_0000;

fn encode_rex(w: bool, r: bool, x: bool, b: bool) -> u8 {
    if w || r || x || b {
        0b_0100_0000 | ((w as u8) << 3) | ((r as u8) << 2) | ((x as u8) << 1) | b as u8
    } else {
        0
    }
}

fn encode_modrm_r(r: Reg, wide: bool, extension: u8) -> Modrm {
    debug_assert!(extension < 8);
    let (ra, r) = encode_reg(r);
    Modrm {
        rex: encode_rex(wide, r, false, false),
        modrm: MODRM_RR | (extension << 3) | ra,
    }
}

fn encode_modrm_rr(reg_a: Reg, reg_b: Reg, wide: bool) -> Modrm {
    let (ra, r) = encode_reg(reg_a);
    let (rb, b) = encode_reg(reg_b);
    Modrm {
        rex: encode_rex(wide, r, false, b),
        modrm: MODRM_RR | (rb << 3) | ra,
    }
}

fn encode_modrm_ri(reg: Reg, wide: bool, i: u8) -> Modrm {
    debug_assert!(i < 8);
    let (rm, r) = encode_reg(reg);
    Modrm {
        rex: encode_rex(wide, r, false, false),
        modrm: MODRM_RR | i << 3 | rm,
    }
}

/*
fn encode_modrm_mr(reg_ptr: Reg, off: OffsetClass, reg_val: Reg, wide: bool) -> Modrm {
    let (modrm_a, r) = encode_reg(reg_ptr);
    let (modrm_b, b) = encode_reg(reg_val);
    Modrm {
        rex: encode_rex(wide, r, false, b),
        modrm: modrm_a | (modrm_b << 3) | off.modrm_bits(),
    }
}
*/
