use std::{borrow::Cow, collections::HashSet, hash::Hash};

use crate::{
    mc::{MachineIR, MirBlock},
    Bitmap, BlockIndex, FunctionIr, Ref, Tag,
};

pub trait Block: Copy + Hash + Eq + core::fmt::Debug {
    const ENTRY: Self;

    fn from_raw(value: u32) -> Self;
    fn idx(self) -> usize;
}

pub trait Blocks {
    type Block: Block;

    fn block_count(&self) -> u32;
    fn successors(&self, block: Self::Block) -> Cow<[Self::Block]>;
}
impl Blocks for FunctionIr {
    type Block = BlockIndex;

    fn block_count(&self) -> u32 {
        self.blocks().len() as u32
    }

    fn successors(&self, block: BlockIndex) -> Cow<[BlockIndex]> {
        // PERF: maybe return a SmallVec or something to prevent many heap allocations.
        // Alternatively could just track successors (and maybe predecessors) in IR to be able to
        // retrieve them easily.
        let (_, terminator) = self.get_block(block).last().expect("empty block found");
        match terminator.tag {
            Tag::Goto => {
                let (next, _) = terminator.data.goto();
                vec![next].into()
            }
            Tag::Branch => {
                let (_, a, b, _) = terminator.data.branch(&self.extra);
                vec![a, b].into()
            }
            Tag::Ret => Cow::Borrowed(&[]),
            tag => panic!("block {block:?} doesn't have a terminator, found {tag:?} instead"),
        }
    }
}
impl<I: crate::mc::Instruction> Blocks for MachineIR<I> {
    type Block = MirBlock;

    fn successors(&self, block: Self::Block) -> Cow<[Self::Block]> {
        Cow::Borrowed(self.block_successors(block))
    }

    fn block_count(&self) -> u32 {
        self.block_count()
    }
}

pub struct BlockGraph<B: Blocks> {
    dominators: Box<[HashSet<B::Block>]>,
    preds: Box<[HashSet<B::Block>]>,
    postorder: Vec<B::Block>,
}
impl<B: Blocks> BlockGraph<B> {
    pub fn calculate(ir: &B) -> Self {
        let full_dominators: HashSet<_> = (0..ir.block_count()).map(B::Block::from_raw).collect();
        let (postorder, preds) = calculate_postorder_and_preds(ir);

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

    pub fn preds<'a>(&'a self, block: B::Block) -> impl 'a + Iterator<Item = B::Block> {
        self.preds[block.idx()].iter().copied()
    }

    pub fn postorder(&self) -> &[B::Block] {
        &self.postorder
    }
}
impl BlockGraph<FunctionIr> {
    pub fn dominates(&self, ir: &FunctionIr, i: u32, dominating: Ref) -> bool {
        let Some(dominating_index) = dominating.into_ref() else {
            // values are always fine
            return true;
        };
        self.block_dominates(
            ir.get_block_from_index(i),
            ir.get_block_from_index(dominating_index),
        )
    }
}

fn calculate_postorder_and_preds<B: Blocks>(ir: &B) -> (Vec<B::Block>, Box<[HashSet<B::Block>]>) {
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
                let succs = ir.successors(block);
                for &succ in succs.iter() {
                    preds[succ.idx() as usize].insert(block);
                }
                stack.extend(succs.iter().filter_map(|&block| {
                    (!seen.get(block.idx() as usize)).then(|| {
                        seen.set(block.idx() as usize, true);
                        (Event::Enter, block)
                    })
                }));
            }
            Event::Exit => postorder.push(block),
        }
    }

    (postorder, preds)
}
