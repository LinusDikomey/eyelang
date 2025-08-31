mod macros;
pub use macros::visitor;

use crate::{
    BlockGraph, BlockId, Environment, FunctionId, FunctionIr, INLINE_ARGS, Instruction, IntoArgs,
    Parameter, Ref, TypeId, Types, modify::IrModify,
};

pub trait Visitor<Ctx = ()> {
    type Output;
    fn visit_instruction(
        &self,
        ir: &mut IrModify,
        types: &Types,
        env: &Environment,
        inst: &Instruction,
        r: Ref,
        block: BlockId,
        ctx: &mut Ctx,
    ) -> Option<Self::Output>;
}
pub trait RewriteStrategy {
    type BlockInstructions: IntoIterator<Item = u32>;
    fn next_block(&mut self, ir: &IrModify) -> Option<BlockId>;
    fn iterate_block(&self, ir: &IrModify, block: BlockId) -> Self::BlockInstructions;
}
#[derive(Default)]
pub struct LinearRewriteOrder {
    next_block: u32,
}
impl LinearRewriteOrder {
    pub fn new() -> Self {
        Self::default()
    }
}
impl RewriteStrategy for LinearRewriteOrder {
    type BlockInstructions = std::ops::Range<u32>;
    fn next_block(&mut self, ir: &IrModify) -> Option<BlockId> {
        ir.block_ids()
            .last()
            .is_some_and(|last| self.next_block <= last.0)
            .then(|| {
                let id = BlockId(self.next_block);
                self.next_block += 1;
                id
            })
    }

    fn iterate_block(&self, ir: &IrModify, block: BlockId) -> Self::BlockInstructions {
        let info = ir.get_block(block);
        let s = info.idx + info.arg_count;
        s..s + info.len
    }
}
pub struct ReverseRewriteOrder {
    blocks: std::vec::IntoIter<BlockId>,
}
impl ReverseRewriteOrder {
    pub fn new(graph: &BlockGraph<FunctionIr>) -> Self {
        Self {
            blocks: graph.postorder().to_vec().into_iter(),
        }
    }
}
impl RewriteStrategy for ReverseRewriteOrder {
    type BlockInstructions = std::iter::Rev<std::ops::Range<u32>>;

    fn next_block(&mut self, _ir: &IrModify) -> Option<BlockId> {
        self.blocks.next()
    }

    fn iterate_block(&self, ir: &IrModify, block: BlockId) -> Self::BlockInstructions {
        let info = ir.get_block(block);
        let s = info.idx + info.arg_count;
        (s..s + info.len).rev()
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Rewrite {
    Replace(Instruction),
    Rename(Ref),
}

pub trait IntoVisit<T> {
    fn into_visit(self, ir: &mut IrModify, env: &Environment, block: BlockId) -> Option<T>;
}
impl<T> IntoVisit<T> for T {
    fn into_visit(self, _ir: &mut IrModify, _env: &Environment, _block: BlockId) -> Option<T> {
        Some(self)
    }
}
impl<'a, A: IntoArgs<'a>> IntoVisit<Rewrite> for (FunctionId, A, TypeId) {
    fn into_visit(self, ir: &mut IrModify, env: &Environment, block: BlockId) -> Option<Rewrite> {
        Some(Rewrite::Replace(ir.prepare_instruction(
            &env[self.0].params,
            env[self.0].varargs,
            block,
            self,
        )))
    }
}
impl IntoVisit<Rewrite> for Ref {
    fn into_visit(
        self,
        _ir: &mut IrModify,
        _env: &Environment,
        _block: BlockId,
    ) -> Option<Rewrite> {
        Some(Rewrite::Rename(self))
    }
}
impl IntoVisit<Rewrite> for () {
    fn into_visit(
        self,
        _ir: &mut IrModify,
        _env: &Environment,
        _block: BlockId,
    ) -> Option<Rewrite> {
        None
    }
}

pub trait RewriteCtx {
    fn begin_block(&mut self, _env: &Environment, _ir: &mut IrModify, _block: BlockId) {}
    fn end_block(&mut self, _env: &Environment, _ir: &mut IrModify, _block: BlockId) {}
}
impl RewriteCtx for () {}

pub fn rewrite_in_place<Ctx: RewriteCtx, R: Visitor<Ctx, Output = Rewrite>>(
    ir: &mut IrModify,
    types: &Types,
    env: &Environment,
    ctx: &mut Ctx,
    rewriter: &R,
    mut strategy: impl RewriteStrategy,
) {
    while let Some(block) = strategy.next_block(ir) {
        ctx.begin_block(env, ir, block);
        for idx in strategy.iterate_block(ir, block) {
            let r = Ref(idx);
            let Ok(&inst) = ir.try_get_inst(r) else {
                // instruction was deleted, skip it
                continue;
            };
            let rewrite = rewriter.visit_instruction(ir, types, env, &inst, r, block, ctx);
            match rewrite {
                None => {}
                Some(Rewrite::Replace(new_inst)) => {
                    ir.replace_with_inst(r, new_inst);
                }
                Some(Rewrite::Rename(new_ref)) => {
                    ir.replace_with(r, new_ref);
                }
            }
        }
        ctx.end_block(env, ir, block);
    }
}
/// Tracks renames of values to replace all uses of values with other values
pub struct RenameTable {
    renames: Box<[Option<Ref>]>,
}
impl RenameTable {
    pub fn new(ir: &FunctionIr) -> Self {
        Self {
            renames: vec![None; ir.inst_count() as usize].into_boxed_slice(),
        }
    }

    pub fn rename(&mut self, idx: u32, rename: Ref) {
        self.renames[idx as usize] = Some(rename);
    }

    pub fn visit_inst(&self, ir: &mut IrModify, inst: &mut Instruction, env: &Environment) {
        let get_new =
            |r: Ref| -> Option<Ref> { r.into_ref().and_then(|i| self.renames[i as usize]) };
        let get = |r: Ref| get_new(r).unwrap_or(r);
        let params = &env[inst.function].params;
        let count = params.iter().map(|p| p.slot_count()).sum();
        let args = if count <= INLINE_ARGS {
            &mut inst.args[..count]
        } else {
            let i = inst.args[0] as usize;
            &mut ir.ir.extra[i..i + count]
        };
        let mut args = args.iter_mut();

        for param in params {
            if matches!(param, Parameter::Ref | Parameter::RefOf(_)) {
                let value = args.next().unwrap();
                *value = get(Ref(*value)).0;
            } else {
                for _ in 0..param.slot_count() {
                    let ignored = args.next();
                    debug_assert!(ignored.is_some());
                }
            }
        }
    }
}
