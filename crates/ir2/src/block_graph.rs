use std::{borrow::Cow, collections::HashSet, hash::Hash};

use crate::{Argument, Bitmap, BlockId, Environment, FunctionIr};

pub trait Block: Copy + Hash + Eq + core::fmt::Debug {
    const ENTRY: Self;

    fn from_raw(value: u32) -> Self;
    fn idx(self) -> usize;
}
impl Block for BlockId {
    const ENTRY: Self = Self::ENTRY;

    fn from_raw(value: u32) -> Self {
        Self(value)
    }

    fn idx(self) -> usize {
        self.0 as usize
    }
}

pub trait Blocks {
    type Block: Block;
    type Env;

    fn block_count(&self) -> u32;
    fn successors(&self, env: &Self::Env, block: Self::Block) -> Cow<[Self::Block]>;
}

pub struct BlockGraph<B: Blocks> {
    dominators: Box<[HashSet<B::Block>]>,
    preds: Box<[HashSet<B::Block>]>,
    postorder: Vec<B::Block>,
}
impl<B: Blocks> BlockGraph<B> {
    pub fn calculate(ir: &B, env: &B::Env) -> Self {
        let full_dominators: HashSet<_> = (0..ir.block_count()).map(B::Block::from_raw).collect();
        let (postorder, preds) = calculate_postorder_and_preds(ir, env);

        let mut dominators: Box<[_]> = (0..ir.block_count())
            .map(|_| full_dominators.clone())
            .collect();

        loop {
            let mut changed = false;

            for &block in postorder.iter().rev() {
                let mut new_set = preds[block.idx()]
                    .iter()
                    .map(|p| dominators[p.idx()].clone())
                    .reduce(|a, b| &a & &b)
                    .unwrap_or_default();
                new_set.insert(block);
                if new_set.len() != dominators[block.idx()].len() {
                    dominators[block.idx()] = new_set;
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }

        Self {
            dominators,
            preds,
            postorder,
        }
    }

    pub fn block_dominates(&self, dominated: B::Block, dominating: B::Block) -> bool {
        self.dominators[dominated.idx()].contains(&dominating)
    }

    pub fn pred_count(&self, block: B::Block) -> usize {
        self.preds[block.idx()].len()
    }

    pub fn preceeds(&self, block: B::Block, pred: B::Block) -> bool {
        self.preds[block.idx()].contains(&pred)
    }

    pub fn preds(&self, block: B::Block) -> impl Iterator<Item = B::Block> + use<'_, B> {
        self.preds[block.idx()].iter().copied()
    }

    pub fn postorder(&self) -> &[B::Block] {
        &self.postorder
    }
}

impl Blocks for FunctionIr {
    type Block = BlockId;
    type Env = Environment;

    fn block_count(&self) -> u32 {
        self.block_count()
    }

    fn successors(&self, env: &Environment, block: BlockId) -> Cow<[BlockId]> {
        // PERF: maybe return a SmallVec or something to prevent many heap allocations.
        // Alternatively could just track successors (and maybe predecessors) in IR to be able to
        // retrieve them easily.
        let (_, terminator) = self.get_block(block).last().expect("empty block found");
        let func = &env[terminator.function];
        let params = &func.params;
        let varargs = func.varargs;
        debug_assert!(func.terminator);
        terminator
            .args(params, varargs, self.blocks(), self.extra())
            .filter_map(|arg| {
                if let Argument::BlockTarget(target) = arg {
                    Some(target.0)
                } else {
                    None
                }
            })
            .collect()
    }

    /*
    pub fn dominates(&self, ir: &FunctionIr, i: u32, dominating: Ref) -> bool {
        self.block_dominates(
            ir.get_block_from_index(i),
            ir.get_block_from_index(dominating_index),
        )
        todo!()
    }
    */
}

fn calculate_postorder_and_preds<B: Blocks>(
    ir: &B,
    env: &B::Env,
) -> (Vec<B::Block>, Box<[HashSet<B::Block>]>) {
    enum Event {
        Enter,
        Exit,
    }
    let mut stack = vec![(Event::Enter, B::Block::ENTRY)];
    let mut postorder = Vec::with_capacity(ir.block_count() as usize);
    let mut preds = vec![HashSet::new(); ir.block_count() as usize].into_boxed_slice();
    let mut seen = Bitmap::new(ir.block_count() as usize);
    seen.set(0, true);

    while let Some((event, block)) = stack.pop() {
        match event {
            Event::Enter => {
                stack.push((Event::Exit, block));
                let succs = ir.successors(env, block);
                for &succ in succs.iter() {
                    preds[succ.idx()].insert(block);
                }
                // suggestion doesn't work because seen is borrowed twice
                #[allow(clippy::filter_map_bool_then)]
                stack.extend(succs.iter().filter_map(|&block| {
                    (!seen.get(block.idx())).then(|| {
                        seen.set(block.idx(), true);
                        (Event::Enter, block)
                    })
                }));
            }
            Event::Exit => postorder.push(block),
        }
    }

    (postorder, preds)
}
