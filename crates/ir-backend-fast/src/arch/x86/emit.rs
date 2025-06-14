use std::{collections::VecDeque, hint::unreachable_unchecked};

use ir::{
    Argument, BlockId, BlockTarget, Environment, FunctionIr, MCReg, ModuleOf,
    block_graph::Blocks,
    mc::{Mc, OpType, RegClass},
};

use super::isa::{Reg, X86};

pub fn write(
    env: &Environment,
    mc: ModuleOf<Mc>,
    x86: ModuleOf<X86>,
    ir: &FunctionIr,
    text: &mut Vec<u8>,
) {
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
                    Mc::Copy => {
                        let mut args = ir.args_iter(i, env).map(|arg| {
                            let Argument::MCReg(r) = arg else {
                                unreachable!()
                            };
                            r
                        });
                        // FIXME: this doesn't handle conflicting copies, will require a proper
                        // parallel copy algo in the future
                        loop {
                            let Some(to) = args.next() else { break };
                            let from = args.next().unwrap();
                            let to = to.phys::<Reg>().unwrap();
                            let from = from.phys::<Reg>().unwrap();
                            if to.bit() == from.bit() {
                                continue;
                            }
                            // FIXME: assumes 32 bits right now
                            let modrm = encode_modrm_rr(to, from, false);
                            if modrm.rex != 0 {
                                text.push(modrm.rex);
                            }
                            text.extend([0x89, modrm.modrm]);
                        }
                    }
                }
                continue;
            }
            let Some(inst) = i.as_module(x86) else {
                panic!("expected x86 instruction but encountered other module at {r:?}");
            };

            use X86 as I;
            match inst.op() {
                I::movri32 | I::movri64 => {
                    let wide = inst.op() == I::movri64;
                    let (a, b): (Reg, u64) = ir.args(i, env);
                    let imm32: i32 = b.try_into().unwrap();
                    let [i0, i1, i2, i3] = imm32.to_le_bytes();
                    let (r, b) = encode_reg(a);
                    if b || wide {
                        text.push(REX | if b { REX_B } else { 0 } | if wide { REX_W } else { 0 });
                    }
                    text.extend([0xB8 + r, i0, i1, i2, i3]);
                }
                I::movrr32 | I::movrr64 => {
                    let (a, b): (Reg, Reg) = ir.args(i, env);
                    let wide = inst.op() == I::movrr64;
                    let modrm = encode_modrm_rr(a, b, wide);
                    if modrm.rex != 0 {
                        text.push(modrm.rex);
                    }
                    text.extend([0x89, modrm.modrm]);
                }
                I::ret32 => {
                    text.push(0xc3);
                }
                I::cmprr32 => {
                    let (a, b) = ir.args(i, env);
                    let modrm = encode_modrm_rr(b, a, false);
                    if modrm.rex != 0 {
                        text.push(REX);
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
                        &[0x7C, 0xcb],
                        &[0x0F, 0x8C],
                        target,
                        text,
                        start,
                        &block_offsets,
                        &mut missing_block_addrs,
                    );
                }
                I::addrr32 => {
                    inst_rr(text, &[0x01], ir.args(i, env));
                }
            }

            /*
            match inst.inst {
                Inst::Copy => {
                    let (a, b) = rr();
                    copy_rr(text, a, b);
                }
                Inst::Copyargs => {
                    // TODO: handle conflicting copies
                    let (to, from) = inst.decode_copyargs(ir.extra_ops());
                    for (&to, &from) in to.iter().zip(from) {
                        let Op::Reg(to) = to else { unreachable!() };
                        match from {
                            Op::Reg(from) => copy_rr(text, to, from),
                            Op::None => panic!(),
                            Op::Imm(imm) => {
                                let modrm = encode_modrm_ri(to, false);
                                if modrm.rex != 0 {
                                    text.push(modrm.rex);
                                }
                                if imm <= u32::MAX as u64 {
                                    let [b0, b1, b2, b3] = (imm as u32).to_le_bytes();
                                    let (r, b) = encode_reg(to);
                                    if b {
                                        text.push(REX | REX_B);
                                    }
                                    text.extend([0xB8 + r, modrm.modrm, b0, b1, b2, b3]);
                                } else {
                                    todo!("handle larger immediate values")
                                }
                            }
                            Op::VReg(_) => unreachable!("vregs should be eliminated by regalloc"),
                            Op::Func(_) | Op::Block(_) => unreachable!(),
                        }
                    }
                }
                Inst::addrr32 => inst_rr(text, &[0x01], rr()),
                Inst::addrm32 => inst_rm(text, &[0x03], rm()),
                Inst::addri32 | Inst::addri64 => {
                    let wide = inst.inst == Inst::addri64;
                    let (r, i) = ri();
                    if i == 0 {
                        continue;
                    }
                    inst_ri(text, &[0x83], wide, 0, (r, i));
                }
                Inst::subrr32 => {
                    let (a, b) = rr();
                    let modrm = encode_modrm_rr(a, b, false);
                    if modrm.rex != 0 {
                        text.push(modrm.rex);
                    }
                    text.extend([0x29, modrm.modrm]);
                }
                Inst::subri32 | Inst::subri64 => {
                    let wide = inst.inst == Inst::subri64;
                    let (r, i) = ri();
                    if i == 0 {
                        continue;
                    };
                    inst_ri(text, &[0x83], wide, 5 << 3, (r, i));
                }
                Inst::subrm32 => inst_rm(text, &[0x2B], rm()),
                Inst::imulrr32 => inst_rr(text, &[0x0F, 0xAF], swap(rr())),
                Inst::imulrm32 => inst_rm(text, &[0x0F, 0xAF], rm()),
                Inst::imulrri32 => {
                    let (a, b, i) = rri();
                    let modrm = encode_modrm_rr(b, a, false);
                    if modrm.rex != 0 {
                        text.push(modrm.rex);
                    }
                    let imm = i as i64;
                    let imm8: Result<i8, _> = imm.try_into();
                    if let Ok(imm8) = imm8 {
                        text.extend([0x6B, modrm.modrm, imm8 as u8]);
                    } else {
                        let imm32: i32 = imm.try_into().expect("TODO: mul with 64-bit imm");
                        text.extend([0x69, modrm.modrm]);
                        text.extend(imm32.to_le_bytes());
                    }
                }
                Inst::movrr8 => inst_rr(text, &[0x88], rr()),
                Inst::movrr16 => {
                    text.push(PRECISION_16);
                    inst_rr(text, &[0x89], rr());
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
                Inst::movri8 => {
                    let (r, i) = ri();
                    let (r, b) = encode_reg(r);
                    if b {
                        text.push(REX | REX_B);
                    }
                    let i: i8 = i.try_into().unwrap();
                    text.extend([0xB0 + r, i as u8]);
                }
                Inst::movri16 => {
                    let (r, i) = ri();
                    let (r, b) = encode_reg(r);
                    text.push(PRECISION_16);
                    if b {
                        text.push(REX | REX_B);
                    }
                    let i: i16 = i.try_into().unwrap();
                    let [i0, i1] = i.to_le_bytes();
                    text.extend([0xB8 + r, i0, i1]);
                }
                Inst::movri32 | Inst::movri64 => {
                    let wide = inst.inst == Inst::movri64;
                    let (a, b) = ri();
                    let imm32: i32 = b.try_into().unwrap();
                    let [i0, i1, i2, i3] = imm32.to_le_bytes();
                    let (r, b) = encode_reg(a);
                    if b || wide {
                        text.push(REX | if b { REX_B } else { 0 } | if wide { REX_W } else { 0 });
                    }
                    text.extend([0xB8 + r, i0, i1, i2, i3]);
                }
                Inst::movrm8 => inst_rm(text, &[0x88], rm()),
                Inst::movrm16 => {
                    text.push(PRECISION_16);
                    inst_rm(text, &[0x89], rm());
                }
                Inst::movrm32 | Inst::movrm64 => {
                    let wide = inst.inst == Inst::movrm64;
                    let (r, (ptr, off)) = rm();
                    let modrm = encode_modrm_rm(r, ptr, off, wide);
                    if modrm.rex != 0 {
                        text.push(modrm.rex);
                    }
                    text.extend([0x8b, modrm.modrm]);
                    off.write(text);
                }
                Inst::movmr8 => {
                    let ((ptr, off), r) = mr();
                    let modrm = encode_modrm_mr(ptr, off, r, false);
                    if modrm.rex != 0 {
                        text.push(modrm.rex);
                    }
                    text.extend([0x8A, modrm.modrm]);
                }
                Inst::movmr16 => {
                    let ((ptr, off), r) = mr();
                    let modrm = encode_modrm_mr(ptr, off, r, false);
                    text.push(PRECISION_16);
                    if modrm.rex != 0 {
                        text.push(modrm.rex);
                    }
                    text.extend([0x89, modrm.modrm]);
                }
                Inst::movmr32 | Inst::movmr64 => {
                    let wide = inst.inst == Inst::movmr64;
                    let ((ptr, off), r) = mr();
                    let modrm = encode_modrm_mr(ptr, off, r, wide);
                    if modrm.rex != 0 {
                        text.push(modrm.rex);
                    }
                    text.extend([0x89, modrm.modrm]);
                    off.write(text);
                }
                Inst::movmi8 => inst_mi(text, &[0xC6], false, mi()),
                Inst::movmi16 => {
                    text.push(PRECISION_16);
                    inst_mi(text, &[0xC7], false, mi());
                }
                Inst::movmi32 | Inst::movmi64 => {
                    inst_mi(text, &[0xC7], inst.inst == Inst::movmi64, mi())
                }
                Inst::call => todo!(),
                Inst::push64 => {
                    let r = r(inst.ops[0]);
                    let (r, b) = encode_reg(r);
                    if b {
                        text.push(REX | REX_B);
                    }
                    text.push(0x50 + r);
                }
                Inst::pop64 => {
                    let r = r(inst.ops[0]);
                    let (r, b) = encode_reg(r);
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
                    let (r, b) = encode_reg(r);
                    if b {
                        text.push(REX | REX_B);
                    }
                    let imm8: Result<i8, _> = imm.try_into();
                    let o = 7;
                    text.extend([0x80, (0b11 << 6) | r | o << 3, imm8.unwrap() as u8]);
                }
                Inst::cmprr32 => {
                    let (a, b) = rr();
                    let modrm = encode_modrm_rr(b, a, false);
                    if modrm.rex != 0 {
                        text.push(REX);
                    }
                    text.extend([0x3B, modrm.modrm]);
                }
                Inst::cmpri32 => {
                    let (r, imm) = ri();
                    let (r, b) = encode_reg(r);
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
                Inst::cmprm32 => inst_rm(text, &[0x3B], rm()),
                Inst::cmpmi32 => todo!(),
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
                    let (r, b) = encode_reg(r);
                    if b {
                        text.push(REX | REX_B);
                    }
                    text.extend([0x0F, po, 0b11 << 6 | r]);
                }
            }
            */
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

fn swap<T>(t: (T, T)) -> (T, T) {
    (t.1, t.0)
}

fn inst_rr(text: &mut Vec<u8>, opcode: &[u8], (a, b): (Reg, Reg)) {
    let modrm = encode_modrm_rr(a, b, false);
    if modrm.rex != 0 {
        text.push(modrm.rex);
    }
    text.extend(opcode);
    text.push(modrm.modrm);
}

fn inst_rm(text: &mut Vec<u8>, opcode: &[u8], (r, (ptr, off)): (Reg, (Reg, OffsetClass))) {
    let modrm = encode_modrm_rm(r, ptr, off, false);
    if modrm.rex != 0 {
        text.push(modrm.rex);
    }
    text.extend(opcode);
    text.push(modrm.modrm);
    off.write(text);
}

fn inst_ri(text: &mut Vec<u8>, opcode: &[u8], wide: bool, modrm_bits: u8, (r, imm): (Reg, u64)) {
    let modrm = encode_modrm_ri(r, wide);
    if modrm.rex != 0 {
        text.push(modrm.rex);
    }
    if let Ok(b8) = imm.try_into() {
        text.extend(opcode);
        text.extend([modrm.modrm | modrm_bits, b8]);
    } else {
        todo!("handle larger imm values");
    }
}

fn inst_mi(
    text: &mut Vec<u8>,
    opcode: &[u8],
    wide: bool,
    ((reg, off), i): ((Reg, OffsetClass), u64),
) {
    let (reg, b) = encode_reg(reg);
    let modrm = reg | off.modrm_bits();
    if b {
        // REX byte
        text.push(0b0100_0100 | if wide { REX_W } else { 0 });
    }
    text.extend(opcode);
    text.push(modrm);
    off.write(text);
    let imm = i as i64;
    let imm32: Result<i32, _> = imm.try_into();
    text.extend(imm32.expect("immediate too large").to_le_bytes());
}

fn copy_rr(text: &mut Vec<u8>, to: Reg, from: Reg) {
    if to == from {
        return;
    }
    match to.class() {
        RegClass::GP8 => todo!(),
        RegClass::GP16 => todo!(),
        RegClass::GP32 | RegClass::GP64 => {
            let wide = to.class() == RegClass::GP64;
            let modrm = encode_modrm_rr(to, from, wide);
            if modrm.rex != 0 {
                text.push(modrm.rex);
            }
            text.extend([0x89, modrm.modrm]);
        }
        RegClass::F32 | RegClass::F64 => todo!(),
        RegClass::Flags => todo!(),
    }
}

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

const PRECISION_16: u8 = 0x66;

const REX: u8 = 0b0100_0001;
const REX_B: u8 = 1 << 0;
//const REX_X: u8 = 1 << 1;
//const REX_R: u8 = 1 << 2;
const REX_W: u8 = 1 << 3;

#[derive(Debug, Clone, Copy)]
enum OffsetClass {
    Zero,
    Byte(i8),
    DWord(i32),
}
impl OffsetClass {
    fn from_imm(value: i64) -> Self {
        let value: i32 = value.try_into().unwrap();
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
            OffsetClass::DWord(dw) => text.extend((dw as u32).to_le_bytes()),
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

fn encode_modrm_rr(reg_a: Reg, reg_b: Reg, wide: bool) -> Modrm {
    let (modrm_a, r) = encode_reg(reg_a);
    let (modrm_b, b) = encode_reg(reg_b);
    let rex = if wide || r || b {
        0b_0100_0000 | ((wide as u8) << 3) | ((r as u8) << 2) | (b as u8)
    } else {
        0
    };
    Modrm {
        rex,
        modrm: modrm_a | (modrm_b << 3) | (0b11 << 6),
    }
}

fn encode_modrm_rm(reg_val: Reg, reg_ptr: Reg, off: OffsetClass, wide: bool) -> Modrm {
    let (modrm_a, r) = encode_reg(reg_val);
    let (modrm_b, b) = encode_reg(reg_ptr);
    let rex = if wide || r || b {
        0b_0100_0000 | ((wide as u8) << 3) | ((r as u8) << 2) | (b as u8)
    } else {
        0
    };
    Modrm {
        rex,
        modrm: (modrm_a << 3) | modrm_b | off.modrm_bits(),
    }
}

fn encode_modrm_mr(reg_ptr: Reg, off: OffsetClass, reg_val: Reg, wide: bool) -> Modrm {
    let (modrm_a, r) = encode_reg(reg_ptr);
    let (modrm_b, b) = encode_reg(reg_val);
    let rex = if wide || r || b {
        0b_0100_0000 | ((wide as u8) << 3) | ((r as u8) << 2) | (b as u8)
    } else {
        0
    };
    Modrm {
        rex,
        modrm: modrm_a | (modrm_b << 3) | off.modrm_bits(),
    }
}

fn encode_modrm_ri(reg: Reg, wide: bool) -> Modrm {
    let (modrm_a, r) = encode_reg(reg);
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
