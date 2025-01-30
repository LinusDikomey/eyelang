use std::collections::VecDeque;

use crate::{ArgumentMut, Bitmap, BlockGraph, Environment, FunctionIr, MCReg, Ref, Usage};

use super::Register;

pub fn regalloc<R: Register>(env: &Environment, ir: &mut FunctionIr, log: bool) {
    let graph = BlockGraph::calculate(ir, env);
    let mut intersecting_precolored = vec![R::NO_BITS; ir.mc_reg_count() as usize];
    let mut liveins: Box<[Bitmap]> = (0..ir.block_count())
        .map(|_| Bitmap::new(ir.mc_reg_count() as usize))
        .collect();
    analyze_liveness::<R>(env, ir, &graph, &mut liveins, &mut intersecting_precolored);
    if log {
        eprintln!("liveins:");
        for (i, liveins) in liveins.iter().enumerate() {
            eprint!("  bb{i}:");
            liveins.visit_set_bits(|vreg| eprint!(" %{vreg}"));
            eprintln!();
        }
        eprintln!();
    }
    perform_regalloc::<R>(env, ir, &graph, &intersecting_precolored, &liveins);
}

fn analyze_liveness<R: Register>(
    env: &Environment,
    ir: &mut FunctionIr,
    graph: &BlockGraph<FunctionIr>,
    liveins: &mut [Bitmap],
    intersecting_precolored: &mut [R::RegisterBits],
) {
    let mut workqueue: VecDeque<_> = graph.postorder().iter().copied().collect();
    let mut workqueue_set: Bitmap = Bitmap::new_with_ones(ir.block_count() as usize);
    let mut liveouts = liveins.to_vec();

    while let Some(block) = workqueue.pop_front() {
        workqueue_set.set(block.idx(), false);
        // PERF: just reuse one bitmap in the future and copy over
        let mut live = liveouts[block.idx()].clone();
        let mut live_precolored = R::NO_BITS;
        for r in ir.block_refs(block).iter().rev() {
            analyze_inst_liveness::<R>(
                env,
                ir,
                &mut live,
                &mut live_precolored,
                intersecting_precolored,
                r,
            );
        }
        for pred in graph.preds(block) {
            if liveouts[pred.idx()].union_with(&live) && !workqueue_set.get(pred.idx()) {
                workqueue_set.set(pred.idx(), true);
                workqueue.push_back(pred);
            }
        }
        liveins[block.idx()] = live;
    }
}

fn analyze_inst_liveness<R: Register>(
    env: &Environment,
    ir: &mut FunctionIr,
    live: &mut Bitmap,
    live_precolored: &mut R::RegisterBits,
    intersecting_precolored: &mut [R::RegisterBits],
    inst_r: Ref,
) {
    /*
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
    */
    for arg in ir.args_mut(inst_r, env) {
        let ArgumentMut::MCReg(usage, r) = arg else {
            continue;
        };
        if let Some(p) = r.phys::<R>() {
            if !p.get_bit(live_precolored) {
                r.set_dead();
            }
            p.set_bit(live_precolored, usage != Usage::Def);
            live.visit_set_bits(|vreg| {
                p.set_bit(&mut intersecting_precolored[vreg], true);
            });
        } else {
            let i = r.virt().unwrap() as usize;
            if !live.get(i) {
                live.set(i, true);
                r.set_dead();
            } else if usage == Usage::Def {
                live.set(i, false);
            }
        }
    }
    // TODO: implicit usages
    /*
    for &reg in inst.inst.implicit_uses() {
        if !reg.get_bit(live_precolored) {
            reg.set_bit(live_precolored, true);
            reg.set_bit(&mut inst.implicit_dead, true);
        }
    }
    for &reg in inst.inst.implicit_defs() {
        reg.set_bit(live_precolored, false);
    }
    */
}

fn perform_regalloc<R: Register>(
    env: &Environment,
    ir: &mut FunctionIr,
    graph: &BlockGraph<FunctionIr>,
    intersecting_precolored: &[R::RegisterBits],
    liveins: &[Bitmap],
) {
    let mut chosen = vec![R::DEFAULT; ir.mc_reg_count() as usize];

    // first choose the registers for all block arguments
    for &block in graph.postorder().iter() {
        let mut free = R::ALL_BITS;
        /*
        for arg in mir.block_args(block) {
            let avail = free & !intersecting_precolored[arg.0 as usize];
            let class = mir.virtual_reg_class(arg);
            let chosen_reg =
                R::allocate_reg(avail, class).expect("register allocation failed, TODO: spilling");
            chosen_reg.set_bit(&mut free, false);
            chosen[arg.0 as usize] = chosen_reg;
        }
        */
    }

    // then go over the blocks again to fill in the remaining registers
    for &block in graph.postorder().iter().rev() {
        let mut free = R::ALL_BITS;
        liveins[block.idx()].visit_set_bits(|livein| {
            chosen[livein].set_bit(&mut free, false);
        });
        /*
        for arg in mir.block_args(block).iter() {
            chosen[arg.0 as usize].set_bit(&mut free, false);
        }
        */
        for r in ir.block_refs(block).iter() {
            let inst = ir.get_inst(r);

            /*
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
            */
            for arg in ir.args_mut(r, env) {
                match arg {
                    ArgumentMut::MCReg(Usage::Def, _) => {}
                    ArgumentMut::MCReg(_, reg) => {
                        if let Some(r) = reg.virt() {
                            // Update Def/DefUse with the chosen register and set the free bit if it's dead.
                            let dead = reg.is_dead();
                            let chosen_reg = chosen[r as usize];
                            *reg = MCReg::from_phys(chosen_reg);
                            if dead {
                                chosen_reg.set_bit(&mut free, true);
                                // always preserve the dead bit
                                reg.set_dead();
                            }
                        }
                    }
                    _ => {}
                }
            }
            for arg in ir.args_mut(r, env).rev() {
                if let ArgumentMut::MCReg(usage, r) = arg {
                    if let Some(phys) = r.phys::<R>() {
                        phys.set_bit(&mut free, r.is_dead());
                    } else if usage == Usage::Def {
                        let i = r.virt().unwrap() as usize;
                        // TODO: proper register classes
                        // TODO: spilling
                        let occupied = intersecting_precolored[i];
                        let avail = free & !occupied;
                        let chosen_reg = R::allocate_reg(avail, super::RegClass::GP32)
                            .expect("register allocation failed, TODO: spilling");
                        chosen_reg.set_bit(&mut free, false);
                        chosen[i] = chosen_reg;
                        let dead = r.is_dead();
                        *r = MCReg::from_phys(chosen_reg);
                        // preserve the dead bit
                        if dead {
                            r.set_dead();
                        }
                    }
                }
            }
        }
    }
}
