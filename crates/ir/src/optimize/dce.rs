use crate::{Bitmap, Function, Tag};

#[derive(Debug)]
pub struct Dce;
impl super::FunctionPass for Dce {
    fn run(&self, function: &mut Function, _instrument: bool) {
        run(function);
    }
}

fn run(function: &mut Function) {
    let Some(ir) = &mut function.ir else { return };
    let mut alive_insts = Bitmap::new(ir.total_inst_count() as usize);
    // assume all instructions are dead, then iterate, marking instructions as alive until a fix
    // point is reached.
    loop {
        let mut changed = false;
        for block in ir.blocks() {
            for (i, inst) in ir.get_block(block) {
                // also don't delete block args for now, they will need special treatment
                if inst.tag.has_side_effect() || inst.tag == Tag::BlockArg {
                    alive_insts.set(i as usize, true);
                }
                if alive_insts.get(i as usize) {
                    inst.visit_refs(ir, |r| {
                        if let Some(i) = r.into_ref() {
                            if !alive_insts.get(i as usize) {
                                changed = true;
                                alive_insts.set(i as usize, true);
                            }
                        }
                    })
                }
            }
        }
        if !changed {
            break;
        }
    }
    alive_insts.visit_unset_bits(|dead_inst| {
        let dead_inst = dead_inst as u32;
        if dead_inst < ir.total_inst_count() && ir.get_inst(dead_inst).tag != Tag::BlockArg {
            ir.delete(dead_inst);
        }
    });
}
