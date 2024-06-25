use super::{
    decode_reg, Instruction, MachineIR, OpUsage, RegType, Register, DEAD_BIT, PHYSICAL_BIT,
};

struct Bitmap {
    bits: Vec<u8>,
}
impl Bitmap {
    pub fn new(size: usize) -> Self {
        Self {
            bits: vec![0; size.div_ceil(8)],
        }
    }

    pub fn get(&self, index: usize) -> bool {
        self.bits[index / 8] & (1 << (index % 8)) != 0
    }

    pub fn set(&mut self, index: usize, value: bool) {
        if value {
            self.bits[index / 8] |= 1 << (index % 8);
        } else {
            self.bits[index / 8] &= !(1 << (index % 8));
        }
    }

    pub fn visit_set_bits(&self, mut on_set: impl FnMut(usize)) {
        for (i, &byte) in self.bits.iter().enumerate() {
            for bi in 0..8 {
                if byte & (1 << bi) != 0 {
                    on_set(i * 8 + bi);
                }
            }
        }
    }
}

pub fn regalloc<I: Instruction>(mir: &mut MachineIR<I>) {
    let intersecting_precolored = analyze_liveness(mir);
    perform_regalloc(mir, &intersecting_precolored);
}

fn analyze_liveness<I: Instruction>(
    mir: &mut MachineIR<I>,
) -> Vec<<I::Register as Register>::RegisterBits> {
    let mut seen = Bitmap::new(mir.virtual_register_count());
    let mut live_regs = I::Register::NO_BITS;
    let mut intersecting_precolored = vec![I::Register::NO_BITS; mir.virtual_register_count()];

    for inst in mir.insts.iter_mut().rev() {
        for (reg, usage) in inst.reg_ops_mut() {
            match decode_reg::<I::Register>(*reg) {
                RegType::Reg(r) => {
                    if !r.get_bit(&live_regs) {
                        *reg |= DEAD_BIT;
                    }
                    match usage {
                        OpUsage::Def => r.set_bit(&mut live_regs, false),
                        OpUsage::Use | OpUsage::DefUse => r.set_bit(&mut live_regs, true),
                    }
                    seen.visit_set_bits(|vreg| {
                        r.set_bit(&mut intersecting_precolored[vreg], true);
                    });
                }
                RegType::Virtual(v) => {
                    if !seen.get(v.0 as usize) {
                        seen.set(v.0 as usize, true);
                        *reg |= DEAD_BIT;
                    } else if usage == OpUsage::Def {
                        seen.set(v.0 as usize, false);
                    }
                }
            }
        }
        for &reg in inst.inst.implicit_uses() {
            if !reg.get_bit(&live_regs) {
                reg.set_bit(&mut live_regs, true);
                reg.set_bit(&mut inst.implicit_dead, true);
            }
        }
        for &reg in inst.inst.implicit_defs() {
            reg.set_bit(&mut live_regs, true);
        }
    }
    intersecting_precolored
}

fn perform_regalloc<I: Instruction>(
    mir: &mut MachineIR<I>,
    intersecing_precolored: &[<I::Register as Register>::RegisterBits],
) {
    let mut free = I::Register::ALL_BITS;
    let mut chosen = vec![I::Register::DEFAULT; mir.virtual_register_count()];
    for inst in &mut mir.insts {
        if inst.inst.is_copy() && inst.ops[1] & DEAD_BIT != 0 {
            let a = decode_reg::<I::Register>(inst.ops[0]);
            let b = decode_reg::<I::Register>(inst.ops[1]);
            match (a, b) {
                (RegType::Virtual(a), RegType::Reg(b)) => {
                    eprintln!("found potential copy {a:?} <- {}", b.to_str());
                    if !b.get_bit(&intersecing_precolored[a.0 as usize]) {
                        // theoretically not necessary but right now argument registers are not handled
                        // too well so this is needed
                        b.set_bit(&mut free, false);
                        debug_assert!(!b.get_bit(&free),);
                        chosen[a.0 as usize] = b;
                        inst.ops[0] = PHYSICAL_BIT | b.encode() as u64;
                        continue;
                    }
                }
                (RegType::Virtual(a), RegType::Virtual(b)) => {
                    let b_reg = chosen[b.0 as usize];
                    if !b_reg.get_bit(&intersecing_precolored[a.0 as usize]) {
                        debug_assert_eq!(b_reg.get_bit(&mut free), false);
                        chosen[a.0 as usize] = b_reg;
                        let encoded = PHYSICAL_BIT | b_reg.encode() as u64;
                        inst.ops[0] = encoded;
                        inst.ops[1] = encoded;
                        continue;
                    }
                }
                _ => {}
            }
        }
        for (reg, usage) in inst.reg_ops_mut() {
            let dead = *reg & DEAD_BIT != 0;
            match decode_reg::<I::Register>(*reg) {
                RegType::Reg(r) => {
                    r.set_bit(&mut free, !dead);
                }
                RegType::Virtual(r) => {
                    if usage == OpUsage::Def {
                        // TODO: proper register classes
                        // TODO: spilling
                        let occupied = intersecing_precolored[r.0 as usize];
                        let avail = free & !occupied;
                        let chosen_reg = I::Register::allocate_reg(avail, super::SizeClass::S32)
                            .expect("register allocation failed, TODO: spilling");
                        chosen_reg.set_bit(&mut free, false);
                        chosen[r.0 as usize] = chosen_reg;
                        *reg = PHYSICAL_BIT | chosen_reg.encode() as u64;
                        // preserve the dead bit
                        if dead {
                            *reg |= DEAD_BIT;
                        }
                    }
                }
            }
        }
        for (reg, _usage) in inst.reg_ops_mut() {
            if let RegType::Virtual(r) = decode_reg::<I::Register>(*reg) {
                // All Defs where already replaced with physical registers so only DefUse and Use
                // remain. Update them with the chosen register and set the free bit if it's dead.
                let dead = *reg & DEAD_BIT != 0;
                let chosen_reg = chosen[r.0 as usize];
                *reg = PHYSICAL_BIT | chosen_reg.encode() as u64;
                if dead {
                    chosen_reg.set_bit(&mut free, true);
                    // always preserve the dead bit
                    *reg |= DEAD_BIT;
                }
            }
        }
    }
}
