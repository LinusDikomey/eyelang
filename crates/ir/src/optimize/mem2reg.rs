use core::fmt;
use std::collections::VecDeque;

use dmap::{DHashMap, DHashSet};

use crate::{
    dialect::{self, Mem},
    modify::IrModify,
    Argument, Bitmap, BlockGraph, BlockId, FunctionIr, ModuleOf, Ref, Refs, TypeId,
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

        let block_bodies: Box<[Refs]> = ir
            .block_ids()
            .map(|block| {
                for (r, inst) in ir.get_block(block) {
                    if let Some(inst) = inst.as_module(mem) {
                        match inst.op() {
                            Mem::Decl => {
                                let [Argument::TypeId(ty)] = ir.args_n(&inst) else {
                                    unreachable!()
                                };
                                variables.insert(r, (dmap::new_set(), ty));
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
                    for arg in ir.args_iter(inst, env) {
                        if let Argument::Ref(r) = arg {
                            if r.is_ref() {
                                can_alias.set(r.idx(), true);
                            }
                        }
                    }
                }
                ir.block_refs(block)
            })
            .collect();

        // any variables that can alias will not be removed by mem2reg
        variables.retain(|v, _| !can_alias.get(v.idx()));

        // track all blocks containing stores to each variable
        for block in ir.block_ids() {
            for (_, inst) in ir.get_block(block) {
                if let Some(inst) = inst.as_module(mem) {
                    if inst.op() == Mem::Store {
                        let [Argument::Ref(ptr), Argument::Ref(_value)] = ir.args_n(&inst) else {
                            unreachable!()
                        };
                        if let Some((blocks, _)) = variables.get_mut(&ptr) {
                            blocks.insert(block);
                        }
                    }
                }
            }
        }

        let block_graph = BlockGraph::calculate(&ir, env);

        let mut ir = IrModify::new(ir);

        // find block arg positions
        let variables: DHashMap<Ref, (TypeId, DHashSet<BlockId>)> = variables
            .into_iter()
            .map(|(v, (blocks_containing_store, ty))| {
                let mut result = dmap::new_set();
                let mut to_consider: VecDeque<BlockId> =
                    blocks_containing_store.iter().copied().collect();
                let mut queued: DHashSet<_> = blocks_containing_store;
                while let Some(block) = to_consider.pop_front() {
                    for frontier in block_graph.dominance_frontier(block) {
                        result.insert(frontier);
                        if !queued.contains(&frontier) {
                            to_consider.push_back(frontier);
                            queued.insert(frontier);
                        }
                    }
                }
                (v, (ty, result))
            })
            .collect();

        // insert block arguments
        let variables: DHashMap<Ref, DHashMap<BlockId, (Ref, u32)>> = variables
            .into_iter()
            .map(|(var, (ty, blocks))| {
                (
                    var,
                    blocks
                        .into_iter()
                        .map(|block| (block, ir.add_block_arg(env, block, ty)))
                        .collect(),
                )
            })
            .collect();

        enum Op {
            Enter(BlockId),
            Leave,
        }
        let mut stack = vec![Op::Enter(BlockId::ENTRY)];
        let mut vars_stack = vec![];

        fn decide_value(vars: &[DHashMap<Ref, Ref>], var: Ref) -> Ref {
            vars.iter()
                .rev()
                .find_map(|map| map.get(&var).copied())
                .unwrap_or(Ref::UNIT)
        }

        let mut seen = Bitmap::new(ir.block_ids().len());

        while let Some(op) = stack.pop() {
            match op {
                Op::Enter(block) => {
                    if seen.get(block.idx()) {
                        continue;
                    }
                    seen.set(block.idx(), true);
                    let mut block_vars = dmap::new();
                    for (&var, blocks) in &variables {
                        if let Some(&(arg, _)) = blocks.get(&block) {
                            block_vars.insert(var, arg);
                        }
                    }
                    vars_stack.push(block_vars);
                    stack.push(Op::Leave);
                    let refs = block_bodies[block.idx()];
                    for r in refs.iter() {
                        let inst = ir.get_inst(r);
                        if let Some(inst) = inst.as_module(self.mem) {
                            match inst.op() {
                                Mem::Decl if variables.contains_key(&r) => {
                                    ir.replace_with(r, Ref::UNIT);
                                }
                                Mem::Load => {
                                    // TODO: figure out loads of differing types
                                    let [Argument::Ref(ptr)] = ir.args_n(&inst) else {
                                        unreachable!()
                                    };
                                    if variables.contains_key(&ptr) {
                                        ir.replace_with(r, decide_value(&vars_stack, ptr));
                                    }
                                }
                                Mem::Store => {
                                    let [Argument::Ref(ptr), Argument::Ref(value)] =
                                        ir.args_n(&inst)
                                    else {
                                        unreachable!()
                                    };
                                    if variables.contains_key(&ptr) {
                                        ir.replace_with(r, Ref::UNIT);
                                        vars_stack.last_mut().unwrap().insert(ptr, value);
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    let terminator = refs.iter().last().unwrap();
                    ir.visit_block_targets_mut(terminator, env, |target, args| {
                        for (&var, blocks) in &variables {
                            if let Some(&(_, idx)) = blocks.get(&target) {
                                args[idx as usize] = decide_value(&vars_stack, var);
                            }
                        }
                        stack.push(Op::Enter(target));
                    });
                }
                Op::Leave => {
                    vars_stack.pop();
                }
            }
        }

        ir.finish_and_compress(env)
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use crate::{
        mc::UnknownRegister, optimize::FunctionPass, BlockId, BlockTarget, Environment, Ref,
    };

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
        println!("Before:\n{}", ir.display(&env, &types),);
        let ir = super::Mem2Reg::new(&mut env).run(&env, &types, ir);
        println!("After:\n{}", ir.display(&env, &types),);
        let mem = env.get_dialect_module::<crate::dialect::Mem>();
        for block in ir.block_ids() {
            for (_, inst) in ir.get_block(block) {
                assert!(
                    inst.as_module(mem).is_none(),
                    "there should be no memory instructions left after mem2reg in this case"
                );
            }
        }
    }
}
