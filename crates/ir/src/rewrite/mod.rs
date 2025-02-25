mod macros;
pub use macros::visitor;

use crate::{
    modify::IrModify, BlockId, Environment, FunctionId, FunctionIr, Instruction, IntoArgs,
    Parameter, Ref, TypeId, Types, INLINE_ARGS,
};

pub trait Visitor<Ctx = ()> {
    type Output;
    fn visit_instruction(
        &mut self,
        ir: &mut IrModify,
        types: &Types,
        env: &Environment,
        inst: &Instruction,
        r: Ref,
        block: BlockId,
        ctx: &mut Ctx,
    ) -> Option<Self::Output>;
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
    rewriter: &mut R,
) {
    for block in ir.block_ids() {
        ctx.begin_block(env, ir, block);
        let block_info = ir.get_block(block);
        let i = block_info.idx + block_info.arg_count;
        for idx in i..i + block_info.len {
            let r = Ref(idx);
            let inst = *ir.get_inst(r);
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
