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
        let s = info.args_idx + info.arg_count;
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
        let s = info.args_idx + info.arg_count;
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
            loop {
                let Ok(&inst) = ir.try_get_inst(r) else {
                    // instruction was deleted, skip it
                    break;
                };
                let mut inst = inst;
                crate::update_inst_refs(
                    &mut inst,
                    env,
                    &mut ir.ir.extra,
                    &ir.ir.blocks,
                    |r| ir.renames.get(&r).copied().unwrap_or(r),
                    std::convert::identity,
                );
                let rewrite = rewriter.visit_instruction(ir, types, env, &inst, r, block, ctx);
                match rewrite {
                    None => break,
                    Some(Rewrite::Replace(new_inst)) => {
                        ir.replace_with_inst(env, r, new_inst);
                    }
                    Some(Rewrite::Rename(new_ref)) => {
                        ir.replace_with(env, r, new_ref);
                    }
                }
            }
        }
        ctx.end_block(env, ir, block);
    }
}
/// Tracks renames of values to replace all uses of values with other values
pub struct RenameTable {
    refs: Box<[Ref]>,
    blocks: Box<[BlockId]>,
    old_types_offset: u32,
}
impl RenameTable {
    pub fn new(ir: &FunctionIr, old_types_offset: u32) -> Self {
        Self {
            refs: ir.refs().collect(),
            blocks: ir.block_ids().collect(),
            old_types_offset,
        }
    }

    pub fn rename(&mut self, old: Ref, renamed: Ref) {
        self.refs[old.idx()] = renamed;
    }

    pub fn rename_block(&mut self, old: BlockId, renamed: BlockId) {
        self.blocks[old.idx()] = renamed;
    }

    pub fn get(&self, r: Ref) -> Ref {
        r.into_ref().map_or(r, |i| self.refs[i as usize])
    }

    pub fn visit_inst(
        &self,
        ir: &mut IrModify,
        old_extra: &[u32],
        inst: &mut Instruction,
        env: &Environment,
    ) {
        let get = |r: Ref| -> Ref { r.into_ref().map_or(r, |i| self.refs[i as usize]) };
        let get_block = |b: BlockId| self.blocks[b.idx()];
        let params = &env[inst.function].params[..];
        let count = params.iter().map(|p| p.slot_count()).sum();
        let is_inline = count <= INLINE_ARGS;
        let mut new_args_start = 0;
        if !is_inline {
            let i = inst.args[0] as usize;
            let old = &old_extra[i..i + count];
            new_args_start = ir.ir.extra.len();
            ir.ir.extra.extend_from_slice(old);
        };
        let mut arg_idx: usize = 0;
        let get_arg = |ir: &IrModify, inst: &Instruction, i| {
            if is_inline {
                inst.args[i]
            } else {
                ir.ir.extra()[new_args_start + i]
            }
        };
        let set_arg = |ir: &mut IrModify, inst: &mut Instruction, i: usize, value| {
            if is_inline {
                inst.args[i] = value;
            } else {
                ir.ir.extra[new_args_start + i] = value;
            }
        };

        inst.ty.0 += self.old_types_offset;

        for param in params {
            match param {
                Parameter::Ref | Parameter::RefOf(_) => {
                    let value = get_arg(ir, inst, arg_idx);
                    set_arg(ir, inst, arg_idx, get(Ref(value)).0);
                    arg_idx += 1;
                }
                Parameter::BlockId => {
                    let value = get_arg(ir, inst, arg_idx);
                    set_arg(ir, inst, arg_idx, get_block(BlockId(value)).0);
                    arg_idx += 1;
                }
                Parameter::BlockTarget => {
                    let target = BlockId(get_arg(ir, inst, arg_idx));
                    let new_target = get_block(target);
                    set_arg(ir, inst, arg_idx, new_target.0);
                    let arg_count = ir.ir.blocks[new_target.idx()].arg_count;
                    let idx = get_arg(ir, inst, arg_idx + 1);
                    let args = &old_extra[idx as usize..idx as usize + arg_count as usize];
                    let new_idx = ir.ir.extra.len() as u32;
                    set_arg(ir, inst, arg_idx + 1, new_idx);
                    ir.ir.extra.extend(args.iter().map(|&arg| get(Ref(arg)).0));
                    arg_idx += 2;
                }
                Parameter::TypeId => {
                    let value = get_arg(ir, inst, arg_idx);
                    set_arg(ir, inst, arg_idx, value + self.old_types_offset);
                    arg_idx += 1;
                }
                _ => {
                    arg_idx += param.slot_count();
                }
            }
        }
        debug_assert_eq!(arg_idx, count);
    }
}
