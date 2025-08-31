use std::fmt;

use crate::{
    BUILTIN, BlockId, Builtin, Environment, FunctionIr, Instruction, Ref, Types,
    dialect::{Arith, Cf, Mem, Tuple},
    modify::IrModify,
    pipeline::FunctionPass,
    rewrite::{self, IntoVisit, LinearRewriteOrder, Rewrite},
    use_counts::UseCounts,
};

pub struct Peepholes {
    peephole: Peephole,
}
impl fmt::Debug for Peepholes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Peepholes")
    }
}
impl Peepholes {
    pub fn new(env: &mut Environment) -> Self {
        Self {
            peephole: Peephole::new(env),
        }
    }
}
impl FunctionPass for Peepholes {
    fn run(
        &self,
        env: &crate::Environment,
        types: &crate::Types,
        ir: FunctionIr,
        _name: &str,
        _state: &mut (),
    ) -> (crate::FunctionIr, Option<crate::Types>) {
        let mut ir = IrModify::new(ir);
        let mut ctx = PeepholeCtx {
            use_counts: UseCounts::compute(&ir, env),
        };
        rewrite::rewrite_in_place(
            &mut ir,
            types,
            env,
            &mut ctx,
            self,
            LinearRewriteOrder::new(),
        );
        (ir.finish_and_compress(env), None)
    }
}
struct PeepholeCtx {
    use_counts: UseCounts,
}
impl rewrite::RewriteCtx for PeepholeCtx {}

impl rewrite::Visitor<PeepholeCtx> for Peepholes {
    type Output = Rewrite;

    fn visit_instruction(
        &self,
        ir: &mut IrModify,
        types: &Types,
        env: &Environment,
        inst: &crate::Instruction,
        r: crate::Ref,
        block: crate::BlockId,
        ctx: &mut PeepholeCtx,
    ) -> Option<Self::Output> {
        if let Some(rewrite) = pre_peephole(&self.peephole, ir, types, env, inst, r, block, ctx) {
            return Some(rewrite);
        }
        self.peephole
            .visit_instruction(ir, types, env, inst, r, block, ctx)
    }
}

fn pre_peephole(
    dialects: &Peephole,
    ir: &mut IrModify,
    types: &Types,
    env: &Environment,
    inst: &Instruction,
    r: Ref,
    block: BlockId,
    _ctx: &mut PeepholeCtx,
) -> Option<Rewrite> {
    if let Some(arith) = inst.as_module(dialects.arith) {
        let ty = types[inst.ty()];
        if let Some(binop) = arith.inst.int_binop(ty) {
            let (lhs, rhs): (Ref, Ref) = ir.typed_args(&arith);
            // if any of the operands of one of these instructions is undef, the whole
            // instruction becomes undef
            for arg in [lhs, rhs] {
                if ir
                    .get_inst(arg)
                    .as_module(BUILTIN)
                    .is_some_and(|inst| inst.op() == Builtin::Undef)
                {
                    return Some(Rewrite::Rename(arg));
                }
            }
            let l_int: Option<u64> = ir
                .get_inst(lhs)
                .as_module(dialects.arith)
                .and_then(|i| (i.inst == Arith::Int).then(|| ir.typed_args(&i)));
            let r_int: Option<u64> = ir
                .get_inst(rhs)
                .as_module(dialects.arith)
                .and_then(|i| (i.inst == Arith::Int).then(|| ir.typed_args(&i)));
            match (l_int, r_int) {
                (Some(l), Some(r)) => {
                    return dialects
                        .arith
                        .Int(dbg!((binop.fold)(l, r)), inst.ty())
                        .into_visit(ir, env, block);
                }
                (Some(l), None) => {
                    if binop.commutative {
                        // if only the lhs is a constant and the op is commutative, swap the operands
                        return (inst.function, (rhs, l), arith.ty()).into_visit(ir, env, block);
                    }
                }
                (None, Some(b)) => {
                    // op(op(a, 1), 2) => op(a, fold(1, 2)) (reassociate and fold constants)
                    if binop.associative
                        && let Some(l_inst) = ir.get_inst(lhs).as_module(dialects.arith)
                        && l_inst.op() == arith.op()
                        && let (x, y) = ir.typed_args::<(Ref, Ref), _>(&l_inst)
                        && let Some(int_inst) = ir.get_inst(y).as_module(dialects.arith)
                        && int_inst.op() == Arith::Int
                    {
                        let a: u64 = ir.typed_args(&int_inst);
                        let folded = ir.add_before(
                            env,
                            r,
                            dialects.arith.Int((binop.fold)(a, b), inst.ty()),
                        );
                        return (inst.function, (x, folded), inst.ty()).into_visit(ir, env, block);
                    }
                }
                (None, None) => {}
            }
        }
    }
    None
}

rewrite::visitor! {
    Peephole,
    Rewrite,
    ir, types, inst, env, _dialects,
    _ctx: PeepholeCtx;

    use builtin: crate::Builtin;
    use arith: Arith;
    use tuple: Tuple;
    use mem: Mem;
    use cf: Cf;

    patterns:
        (%r = arith.Add (builtin.Undef) __) => builtin.Undef(ir.get_ref_ty(r));
        (%r = arith.Add __ (builtin.Undef)) => builtin.Undef(ir.get_ref_ty(r));
}
