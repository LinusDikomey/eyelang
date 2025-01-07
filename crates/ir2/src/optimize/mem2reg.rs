use core::fmt;
use std::collections::VecDeque;

use dmap::{DHashMap, DHashSet};

use crate::{
    dialect::{self, Mem},
    modify::IrModify,
    Argument, Bitmap, BlockGraph, BlockId, FunctionIr, ModuleOf, Ref,
};

pub struct Mem2Reg {
    mem: ModuleOf<dialect::Mem>,
}
impl Mem2Reg {
    pub fn new(env: &mut crate::Environment) -> Self {
        Self {
            mem: env.get_dialect_module(),
        }
    }
}
impl fmt::Debug for Mem2Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Mem2Reg")
    }
}
impl super::FunctionPass for Mem2Reg {
    fn run(&self, env: &crate::Environment, _types: &crate::Types, ir: FunctionIr) -> FunctionIr {
        let Self { mem } = *self;
        let mut can_alias = Bitmap::new(ir.inst_count() as usize);
        let mut variables = dmap::new();

        for block in ir.block_ids() {
            for (r, inst) in ir.get_block(block) {
                if let Some(inst) = inst.as_module(mem) {
                    match inst.op() {
                        Mem::Decl => {
                            variables.insert(r, dmap::new_set());
                            continue;
                        }
                        Mem::Load => continue,
                        Mem::Store => {
                            let [Argument::Ref(_ptr), Argument::Ref(value)] = ir.args_n(&inst)
                            else {
                                unreachable!()
                            };
                            if value.is_ref() {
                                can_alias.set(value.idx(), true);
                            }
                            continue;
                        }
                        _ => {}
                    }
                }
                for arg in ir.args(inst, env) {
                    if let Argument::Ref(r) = arg {
                        if r.is_ref() {
                            can_alias.set(r.idx(), true);
                        }
                    }
                }
            }
        }

        dbg!(&variables);
        // any variables that can alias will not be removed by mem2reg
        variables.retain(|v, _| !can_alias.get(v.idx()));

        dbg!(&variables);

        // track all blocks containing stores to each variable
        for block in ir.block_ids() {
            for (_, inst) in ir.get_block(block) {
                if let Some(inst) = inst.as_module(mem) {
                    if inst.op() == Mem::Store {
                        let [Argument::Ref(ptr), Argument::Ref(_value)] = ir.args_n(&inst) else {
                            unreachable!()
                        };
                        if let Some(blocks) = variables.get_mut(&ptr) {
                            blocks.insert(block);
                        }
                    }
                }
            }
        }

        let block_graph = BlockGraph::calculate(&ir, env);

        let mut ir = IrModify::new(ir);

        // find block arg positions
        let positions: DHashMap<Ref, DHashSet<BlockId>> = variables
            .iter()
            .map(|(&v, blocks_containing_store)| {
                let mut result = dmap::new_set();
                let mut to_consider: VecDeque<BlockId> =
                    blocks_containing_store.iter().copied().collect();
                let mut queued: DHashSet<_> = blocks_containing_store.clone();
                while let Some(block) = to_consider.pop_front() {
                    println!("considering {block}");
                    for frontier in block_graph.dominance_frontier(block) {
                        result.insert(frontier);
                        if !queued.contains(&frontier) {
                            eprintln!("to_consider: {frontier}");
                            to_consider.push_back(frontier);
                            queued.insert(frontier);
                        }
                    }
                }
                (v, result)
            })
            .collect();
        dbg!(&positions);

        for (&var, blocks) in &positions {
            let ty = ir.get_inst(var).ty();
            for &block in blocks {
                ir.add_block_arg(env, block, ty);
            }
        }

        for &block in block_graph.postorder() {
            println!(
                "Block {block} dominated by {:?}",
                block_graph.dominators(block).collect::<Vec<_>>()
            );
            for b in block_graph.dominance_frontier(block) {
                println!(" ~ {b}");
            }
        }
        ir.finish_and_compress(env)
    }
}

#[cfg(test)]
mod tests {
    use crate::{optimize::FunctionPass, BlockId, BlockTarget, Environment, Ref};

    fn assert_set_eq<T: PartialEq + std::fmt::Debug>(
        set: impl IntoIterator<Item = T>,
        items: &[T],
    ) {
        let set: Vec<T> = set.into_iter().collect();
        assert_eq!(
            set.len(),
            items.len(),
            "item count doesn't match, expected {items:?} but found {set:?}"
        );
        for item in items {
            if !set.contains(item) {
                panic!("expected {items:?} but found {set:?}, missing {item:?}");
            }
        }
    }

    fn test_func(env: &mut Environment) -> (crate::FunctionIr, crate::Types) {
        let cf = env.get_dialect_module::<crate::dialect::Cf>();
        let mem = env.get_dialect_module::<crate::dialect::Mem>();
        let arith = env.get_dialect_module::<crate::dialect::Arith>();

        let mut builder = crate::builder::Builder::new(&*env);

        let unit = builder.types.add(crate::Primitive::Unit);
        let i32 = builder.types.add(crate::Primitive::I32);
        let ptr = builder.types.add(crate::Primitive::Ptr);

        builder.create_and_begin_block([]);
        let b1 = builder.create_block();
        let b2 = builder.create_block();
        let b3 = builder.create_block();
        let b4 = builder.create_block();

        let a = builder.append(mem.Decl(i32, ptr));
        let five = builder.append(arith.Int(5, i32));
        builder.append(mem.Store(a, five, unit));
        builder.append(cf.Branch(Ref::TRUE, BlockTarget(b1, &[]), BlockTarget(b3, &[]), unit));

        builder.begin_block(b1, []);
        let a_load = builder.append(mem.Load(a, i32));
        let one = builder.append(arith.Int(1, i32));
        let plus1 = builder.append(arith.Add(a_load, one, i32));
        builder.append(mem.Store(a, plus1, unit));
        builder.append(cf.Goto(BlockTarget(b2, &[]), unit));

        builder.begin_block(b2, []);
        let a_load = builder.append(mem.Load(a, i32));
        let times2 = builder.append(arith.Add(a_load, a_load, i32));
        builder.append(mem.Store(a, times2, unit));

        let cond = Ref::TRUE;
        builder.append(cf.Branch(cond, BlockTarget(b1, &[]), BlockTarget(b4, &[]), unit));

        builder.begin_block(b3, []);
        let two = builder.append(arith.Int(2, i32));
        builder.append(mem.Store(a, two, unit));
        builder.append(cf.Goto(BlockTarget(b4, &[]), unit));

        builder.begin_block(b4, []);
        let ret = builder.append(mem.Load(a, i32));
        builder.append(cf.Ret(ret, unit));

        builder.finish_body()
    }

    #[test]
    fn dominance_frontier() {
        let mut env = crate::Environment::new(crate::Primitive::create_infos());
        let (ir, _) = test_func(&mut env);
        let graph = crate::BlockGraph::calculate(&ir, &env);
        let b0 = BlockId(0);
        let b1 = BlockId(1);
        let b2 = BlockId(2);
        let b3 = BlockId(3);
        let b4 = BlockId(4);
        assert!(graph.dominance_frontier(b0).next().is_none());
        assert_set_eq(graph.dominance_frontier(b0), &[]);
        assert_set_eq(graph.dominance_frontier(b1), &[b1, b4]);
        assert_set_eq(graph.dominance_frontier(b2), &[b1, b4]);
        assert_set_eq(graph.dominance_frontier(b3), &[b4]);
        assert_set_eq(graph.dominance_frontier(b4), &[]);
    }

    #[test]
    fn mem2reg_optimize() {
        let mut env = crate::Environment::new(crate::Primitive::create_infos());
        let (ir, types) = test_func(&mut env);
        println!(
            "Before:\n{}",
            crate::display::BodyDisplay {
                env: &env,
                types: &types,
                ir: &ir,
            }
        );
        let ir = super::Mem2Reg::new(&mut env).run(&env, &types, ir);
        println!(
            "After:\n{}",
            crate::display::BodyDisplay {
                env: &env,
                types: &types,
                ir: &ir,
            }
        );
    }
}
