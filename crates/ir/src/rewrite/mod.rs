mod macros;
pub use macros::visitor;

use crate::{
    builtins::Builtin, BlockId, Environment, FunctionId, FunctionIr, Instruction, IntoArgs,
    ModuleId, Parameter, Ref, TypeId, Types, INLINE_ARGS,
};

pub trait Visitor {
    type Output;
    fn visit_instruction(
        &mut self,
        ir: &mut FunctionIr,
        types: &Types,
        env: &Environment,
        inst: &Instruction,
        block: BlockId,
    ) -> Option<Self::Output>;
}

#[derive(Debug, Clone, Copy)]
pub enum Rewrite {
    Keep,
    Replace(Instruction),
    Rename(Ref),
}
impl Rewrite {
    pub fn success(&self) -> bool {
        !matches!(self, Self::Keep)
    }
}

pub trait IntoVisit<T> {
    fn into_visit(self, ir: &mut FunctionIr, env: &Environment, block: BlockId) -> T;
}
impl<T> IntoVisit<T> for T {
    fn into_visit(self, _ir: &mut FunctionIr, _env: &Environment, _block: BlockId) -> T {
        self
    }
}
impl<'a, A: IntoArgs<'a>> IntoVisit<Rewrite> for (FunctionId, A, TypeId) {
    fn into_visit(self, ir: &mut FunctionIr, env: &Environment, block: BlockId) -> Rewrite {
        Rewrite::Replace(ir.prepare_instruction(
            &env[self.0].params,
            env[self.0].varargs,
            block,
            self,
        ))
    }
}
impl IntoVisit<Rewrite> for Ref {
    fn into_visit(self, _ir: &mut FunctionIr, _env: &Environment, _block: BlockId) -> Rewrite {
        Rewrite::Rename(self)
    }
}

pub fn rewrite_in_place<R: Visitor<Output = Rewrite>>(
    ir: &mut FunctionIr,
    types: &Types,
    env: &Environment,
    mut rewriter: R,
) {
    let mut renames = RenameTable::new(ir);
    for block in ir.block_ids() {
        let block_info = &ir.blocks[block.0 as usize];
        let i = block_info.idx + block_info.arg_count;
        for idx in i..i + block_info.len {
            let mut inst = ir.insts[idx as usize];
            renames.visit_inst(ir, &mut inst, env);
            let rewrite = rewriter.visit_instruction(ir, types, env, &inst, block);
            match rewrite {
                Some(Rewrite::Keep) | None => {}
                Some(Rewrite::Replace(new_inst)) => {
                    inst = new_inst;
                }
                Some(Rewrite::Rename(new_ref)) => {
                    inst.function = FunctionId {
                        module: ModuleId::BUILTINS,
                        function: Builtin::Nothing.id(),
                    };
                    renames.rename(idx, new_ref);
                }
            }
            ir.insts[idx as usize] = inst;
        }
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

    pub fn visit_inst(&self, ir: &mut FunctionIr, inst: &mut Instruction, env: &Environment) {
        let get_new =
            |r: Ref| -> Option<Ref> { r.into_ref().and_then(|i| self.renames[i as usize]) };
        let get = |r: Ref| get_new(r).unwrap_or(r);
        let params = &env[inst.function].params;
        let count = params.iter().map(|p| p.slot_count()).sum();
        let args = if count <= INLINE_ARGS {
            &mut inst.args[..count]
        } else {
            let i = inst.args[0] as usize;
            &mut ir.extra[i..i + count]
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
