use std::collections::VecDeque;

use crate::{block_graph::Block, Bitmap, BlockGraph};

use super::{
    decode_reg, Instruction, InstructionStorage, MachineIR, Op, OpUsage, RegType, Register,
    DEAD_BIT, PHYSICAL_BIT,
};

pub fn regalloc<I: Instruction>(mir: &mut MachineIR<I>) {
    analyze_liveness(mir);
    //perform_regalloc(mir);
}

fn analyze_liveness<I: Instruction>(mir: &mut MachineIR<I>) {
    let graph = BlockGraph::calculate(mir);
    let mut workqueue: VecDeque<_> = graph.postorder().iter().copied().collect();
    let mut workqueue_set: Bitmap = Bitmap::new_with_ones(mir.block_count() as usize);

    let mut liveins: Box<[Bitmap]> = (0..mir.block_count())
        .map(|_| Bitmap::new(mir.virtual_register_count()))
        .collect();
    let mut liveouts = liveins.clone();

    while let Some(block) = workqueue.pop_front() {
        workqueue_set.set(block.idx(), false);
        // PERF: just reuse one bitmap in the future and copy over
        let mut live = liveouts[block.idx()].clone();
        let (block_insts, extra_ops) = mir.block_insts_mut(block);
        for inst in block_insts.iter_mut().rev() {
            // TODO: observe register classes
            analyze_inst_liveness(&mut live, inst, extra_ops)
        }
        for pred in graph.preds(block) {
            if liveouts[pred.idx()].union_with(&live) {
                if !workqueue_set.get(pred.idx()) {
                    workqueue_set.set(pred.idx(), true);
                    workqueue.push_back(pred);
                }
            }
        }
        liveins[block.idx()] = live;
    }
}

fn analyze_inst_liveness<I: Instruction>(
    live: &mut Bitmap,
    //live_regs: &mut <I::Register as Register>::RegisterBits,
    //intersecting_precolored: &mut [<I::Register as Register>::RegisterBits],
    inst: &mut InstructionStorage<I>,
    extra_ops: &mut [Op<I::Register>],
) {
    if inst.inst.is_copyargs() {
        let (_to, from) = inst.decode_copyargs(extra_ops);
        for op in from {
            if let &Op::VReg(v) = op {
                if !live.get(v.0 as usize) {
                    live.set(v.0 as usize, true);
                    // TODO: mark dead in extra_ops
                }
            }
        }
        return;
    }
    for (reg, usage) in inst.reg_ops_mut() {
        match decode_reg::<I::Register>(*reg) {
            RegType::Reg(_) => {}
            /*RegType::Reg(r) => {
                if !r.get_bit(live_regs) {
                    *reg |= DEAD_BIT;
                }
                match usage {
                    OpUsage::Def => r.set_bit(live_regs, false),
                    OpUsage::Use | OpUsage::DefUse => r.set_bit(live_regs, true),
                }
                live.visit_set_bits(|vreg| {
                    r.set_bit(&mut intersecting_precolored[vreg], true);
                });
            }*/
            RegType::Virtual(v) => {
                if !live.get(v.0 as usize) {
                    live.set(v.0 as usize, true);
                    *reg |= DEAD_BIT;
                } else if usage == OpUsage::Def {
                    live.set(v.0 as usize, false);
                }
            }
        }
    }
    /*
        for &reg in inst.inst.implicit_uses() {
            if !reg.get_bit(live_regs) {
                reg.set_bit(live_regs, true);
                reg.set_bit(&mut inst.implicit_dead, true);
            }
        }
        for &reg in inst.inst.implicit_defs() {
            reg.set_bit(live_regs, true);
        }
    */
}

/*
fn perform_regalloc<I: Instruction>(mir: &mut MachineIR<I>) {
    let mut free = I::Register::ALL_BITS;
    let mut chosen = vec![I::Register::DEFAULT; mir.virtual_register_count()];
    for inst in &mut mir.insts {
        if inst.inst.is_phi() {
            //continue; // TODO
        }
        if inst.inst.is_copy() && inst.ops[1] & DEAD_BIT != 0 {
            let a = decode_reg::<I::Register>(inst.ops[0]);
            let b = decode_reg::<I::Register>(inst.ops[1]);
            match (a, b) {
                (RegType::Virtual(a), RegType::Reg(b)) => {
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
*/
