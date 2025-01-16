use std::collections::VecDeque;

use crate::{block_graph::Block, Bitmap, BlockGraph};

use super::{
    decode_reg, Instruction, InstructionStorage, MachineIR, Op, OpUsage, RegType, Register,
    DEAD_BIT, PHYSICAL_BIT,
};

pub fn regalloc<I: Instruction>(mir: &mut MachineIR<I>, log: bool) {
    let graph = BlockGraph::calculate(mir, &());
    let mut intersecting_precolored = vec![I::Register::NO_BITS; mir.virtual_register_count()];
    let mut liveins: Box<[Bitmap]> = (0..mir.block_count())
        .map(|_| Bitmap::new(mir.virtual_register_count()))
        .collect();
    analyze_liveness(mir, &graph, &mut liveins, &mut intersecting_precolored);
    if log {
        eprintln!("liveins:");
        for (i, liveins) in liveins.iter().enumerate() {
            eprint!("  bb{i}:");
            liveins.visit_set_bits(|vreg| eprint!(" %{vreg}"));
            eprintln!();
        }
        eprintln!();
    }
    perform_regalloc(mir, &graph, &intersecting_precolored, &liveins);
}

fn analyze_liveness<I: Instruction>(
    mir: &mut MachineIR<I>,
    graph: &BlockGraph<MachineIR<I>>,
    liveins: &mut [Bitmap],
    intersecting_precolored: &mut [<I::Register as Register>::RegisterBits],
) {
    let mut workqueue: VecDeque<_> = graph.postorder().iter().copied().collect();
    let mut workqueue_set: Bitmap = Bitmap::new_with_ones(mir.block_count() as usize);
    let mut liveouts = liveins.to_vec();

    while let Some(block) = workqueue.pop_front() {
        workqueue_set.set(block.idx(), false);
        // PERF: just reuse one bitmap in the future and copy over
        let mut live = liveouts[block.idx()].clone();
        let (block_insts, extra_ops) = mir.block_insts_mut(block);
        analyze_block_liveness(&mut live, intersecting_precolored, block_insts, extra_ops);
        for pred in graph.preds(block) {
            if liveouts[pred.idx()].union_with(&live) && !workqueue_set.get(pred.idx()) {
                workqueue_set.set(pred.idx(), true);
                workqueue.push_back(pred);
            }
        }
        liveins[block.idx()] = live;
    }
}

fn analyze_block_liveness<I: Instruction>(
    live: &mut Bitmap,
    intersecting_precolored: &mut [<I::Register as Register>::RegisterBits],
    insts: &mut [InstructionStorage<I>],
    extra_ops: &mut [Op<I::Register>],
) {
    let mut live_precolored = I::Register::NO_BITS;
    for inst in insts.iter_mut().rev() {
        analyze_inst_liveness(
            live,
            &mut live_precolored,
            intersecting_precolored,
            inst,
            extra_ops,
        )
    }
}

fn analyze_inst_liveness<I: Instruction>(
    live: &mut Bitmap,
    live_precolored: &mut <I::Register as Register>::RegisterBits,
    intersecting_precolored: &mut [<I::Register as Register>::RegisterBits],
    inst: &mut InstructionStorage<I>,
    extra_ops: &mut [Op<I::Register>],
) {
    if inst.inst.is_copyargs() {
        let (to, from) = inst.decode_copyargs(extra_ops);
        for op in from {
            if let &Op::VReg(v) = op {
                if !live.get(v.0 as usize) {
                    live.set(v.0 as usize, true);
                    // TODO: mark dead in extra_ops
                }
            }
        }
        for op in to {
            let Op::VReg(v) = op else { unreachable!() };
            live.set(v.0 as usize, false);
        }
        return;
    }
    for (reg, usage) in inst.reg_ops_mut() {
        match decode_reg::<I::Register>(*reg) {
            RegType::Reg(r) => {
                if !r.get_bit(live_precolored) {
                    *reg |= DEAD_BIT;
                }
                match usage {
                    OpUsage::Def => r.set_bit(live_precolored, false),
                    OpUsage::Use | OpUsage::DefUse => r.set_bit(live_precolored, true),
                }
                live.visit_set_bits(|vreg| {
                    r.set_bit(&mut intersecting_precolored[vreg], true);
                });
            }
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
    for &reg in inst.inst.implicit_uses() {
        if !reg.get_bit(live_precolored) {
            reg.set_bit(live_precolored, true);
            reg.set_bit(&mut inst.implicit_dead, true);
        }
    }
    for &reg in inst.inst.implicit_defs() {
        reg.set_bit(live_precolored, false);
    }
}

fn perform_regalloc<I: Instruction>(
    mir: &mut MachineIR<I>,
    graph: &BlockGraph<MachineIR<I>>,
    intersecting_precolored: &[<I::Register as Register>::RegisterBits],
    liveins: &[Bitmap],
) {
    let mut chosen = vec![I::Register::DEFAULT; mir.virtual_register_count()];

    // first choose the registers for all block arguments
    for &block in graph.postorder().iter() {
        let mut free = I::Register::ALL_BITS;
        for arg in mir.block_args(block).iter() {
            let avail = free & !intersecting_precolored[arg.0 as usize];
            let class = mir.virtual_reg_class(arg);
            let chosen_reg = I::Register::allocate_reg(avail, class)
                .expect("register allocation failed, TODO: spilling");
            chosen_reg.set_bit(&mut free, false);
            chosen[arg.0 as usize] = chosen_reg;
        }
    }

    // then go over the blocks again to fill in the remaining registers
    for &block in graph.postorder().iter().rev() {
        let mut free = I::Register::ALL_BITS;
        liveins[block.idx()].visit_set_bits(|livein| {
            chosen[livein].set_bit(&mut free, false);
        });
        for arg in mir.block_args(block).iter() {
            chosen[arg.0 as usize].set_bit(&mut free, false);
        }
        let (insts, extra_ops) = mir.block_insts_mut(block);
        for (i, inst) in insts.iter_mut().enumerate() {
            if inst.inst.is_copyargs() {
                let (to, from) = inst.decode_copyargs_mut(extra_ops);
                for op in to {
                    if let Op::VReg(vreg) = *op {
                        *op = Op::Reg(chosen[vreg.0 as usize]);
                    }
                }
                for op in from {
                    match *op {
                        Op::VReg(vreg) => {
                            let chosen = chosen[vreg.0 as usize];
                            *op = Op::Reg(chosen);
                            chosen.set_bit(&mut free, false);
                        }
                        Op::Reg(reg) => {
                            reg.set_bit(&mut free, false);
                        }
                        _ => {}
                    }
                }
                continue;
            }
            if inst.inst.is_copy() && inst.ops[1] & DEAD_BIT != 0 {
                let a = decode_reg::<I::Register>(inst.ops[0]);
                let b = decode_reg::<I::Register>(inst.ops[1]);
                match (a, b) {
                    (RegType::Virtual(a), RegType::Reg(b)) => {
                        if !b.get_bit(&intersecting_precolored[a.0 as usize]) {
                            // theoretically not necessary but right now argument registers are not
                            // handled too well so this is needed
                            b.set_bit(&mut free, false);
                            debug_assert!(!b.get_bit(&free));
                            chosen[a.0 as usize] = b;
                            inst.ops[0] = PHYSICAL_BIT | b.encode() as u64;
                            continue;
                        }
                    }
                    (RegType::Virtual(a), RegType::Virtual(b)) => {
                        let b_reg = chosen[b.0 as usize];
                        if !b_reg.get_bit(&intersecting_precolored[a.0 as usize]) {
                            debug_assert!(!b_reg.get_bit(&free), "{block:?}:{i}");
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
            for (reg, _) in inst
                .reg_ops_mut()
                .filter(|&(_, usage)| usage != OpUsage::Def)
            {
                if let RegType::Virtual(r) = decode_reg::<I::Register>(*reg) {
                    // Update Def/DefUse with the chosen register and set the free bit if it's dead.
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
            for (reg, usage) in inst.reg_ops_mut().rev() {
                let dead = *reg & DEAD_BIT != 0;
                match decode_reg::<I::Register>(*reg) {
                    RegType::Reg(r) => {
                        r.set_bit(&mut free, dead);
                    }
                    RegType::Virtual(r) => {
                        if usage == OpUsage::Def {
                            // TODO: proper register classes
                            // TODO: spilling
                            let occupied = intersecting_precolored[r.0 as usize];
                            let avail = free & !occupied;
                            let chosen_reg =
                                I::Register::allocate_reg(avail, super::RegClass::GP32)
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
        }
    }
}
