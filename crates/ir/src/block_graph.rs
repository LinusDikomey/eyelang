use std::collections::HashSet;

use crate::{Bitmap, BlockIndex, FunctionIr, Ref, Tag};

pub struct BlockGraph {
    dominators: Box<[HashSet<BlockIndex>]>,
    preds: Box<[HashSet<BlockIndex>]>,
    postorder: Vec<BlockIndex>,
}
impl BlockGraph {
    pub fn calculate(ir: &FunctionIr) -> Self {
        let full_dominators: HashSet<_> = ir.blocks().collect();
        let (postorder, preds) = calculate_postorder_and_preds(ir);

        let mut dominators: Box<[_]> = ir.blocks().map(|_| full_dominators.clone()).collect();

        loop {
            let mut changed = false;

            for &block in postorder.iter().rev() {
                let mut new_set = preds[block.0 as usize]
                    .iter()
                    .map(|p| dominators[p.0 as usize].clone())
                    .reduce(|a, b| &a & &b)
                    .unwrap_or_default();
                new_set.insert(block);
                if new_set.len() != dominators[block.0 as usize].len() {
                    dominators[block.0 as usize] = new_set;
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

    pub fn block_dominates(&self, dominated: BlockIndex, dominating: BlockIndex) -> bool {
        self.dominators[dominated.0 as usize].contains(&dominating)
    }

    pub fn preceeds(&self, block: BlockIndex, pred: BlockIndex) -> bool {
        self.preds[block.0 as usize].contains(&pred)
    }

    pub fn postorder(&self) -> &[BlockIndex] {
        &self.postorder
    }
}

// PERF: maybe return a SmallVec or something to prevent many heap allocations. Alternatively could
// just track successors (and maybe predecessors) in IR to be able to retrieve them easily.
fn successors(ir: &FunctionIr, block: BlockIndex) -> Vec<BlockIndex> {
    let (_, terminator) = ir.get_block(block).last().expect("empty block found");
    match terminator.tag {
        Tag::Goto => {
            let next = unsafe { terminator.data.block };
            vec![next]
        }
        Tag::Branch => {
            let (_, a, b) = terminator.data.branch(&ir.extra);
            vec![a, b]
        }
        Tag::Ret => vec![],
        tag => panic!("block {block:?} doesn't have a terminator, found {tag:?} instead"),
    }
}

fn calculate_postorder_and_preds(ir: &FunctionIr) -> (Vec<BlockIndex>, Box<[HashSet<BlockIndex>]>) {
    enum Event {
        Enter,
        Exit,
    }
    let mut stack = vec![(Event::Enter, BlockIndex::ENTRY)];
    let mut postorder = vec![];
    let mut preds = vec![HashSet::new(); ir.blocks().len()].into_boxed_slice();
    let mut seen = Bitmap::new(ir.blocks().len());

    while let Some((event, block)) = stack.pop() {
        match event {
            Event::Enter => {
                stack.push((Event::Exit, block));
                let succs = successors(ir, block);
                for &succ in &succs {
                    preds[succ.idx() as usize].insert(block);
                }
                // successors are reversed to improve some heuristics, for example this will make a
                // reverse postorder traversal visit the true branch first which is often better
                stack.extend(succs.into_iter().rev().filter_map(|block| {
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
