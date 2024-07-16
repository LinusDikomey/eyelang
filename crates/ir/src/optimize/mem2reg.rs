//! this module currently implements a very simple subset of the SSA algorithm. It only works
//! locally inside each Block and thus won't create any new block arguments. It will fail to
//! eliminate many kinds of stack allocations.

use std::collections::{hash_map::Entry, HashMap};

use crate::{Bitmap, IrType, Ref, Tag};

use super::RenameTable;

pub fn run(function: &mut crate::Function) {
    let Some(ir) = &mut function.ir else { return };
    let mut can_alias = Bitmap::new(ir.total_inst_count() as usize);

    // observe all uses and mark pointer values as potentially aliasing if they aren't only
    // stored/loaded
    for block in ir.blocks() {
        for arg in ir.get_block_args(block).iter() {
            can_alias.set(arg as usize, true);
        }
        for (i, inst) in ir.get_block(block) {
            if inst.tag != Tag::Decl {
                can_alias.set(i as usize, true);
            }
            match inst.tag {
                Tag::Load => {}
                Tag::Store => {
                    if let Some(idx) = inst.data.bin_op().1.into_ref() {
                        can_alias.set(idx as usize, true);
                    }
                }
                _ => {
                    inst.visit_refs(ir, |r| {
                        if let Some(idx) = r.into_ref() {
                            can_alias.set(idx as usize, true);
                        }
                    });
                }
            }
        }
    }

    let mut stored_values: HashMap<u32, (u32, Ref, IrType)> = HashMap::new();
    let mut renames = RenameTable::new(ir);
    for block in ir.blocks() {
        stored_values.clear();
        for i in ir.get_block_range(block) {
            let mut inst = ir.get_inst(i);
            renames.visit_inst(ir, &mut inst);
            ir.replace(i, inst);

            if inst.tag == Tag::Store {
                let (ptr, value) = inst.data.bin_op();
                let Some(ptr_idx) = ptr.into_ref() else {
                    continue;
                };
                let value_ty = ir.get_ref_ty(value, &function.types);
                let prev_store = stored_values.get(&ptr_idx);
                if let Some(&(store_idx, _, stored_ty)) = prev_store {
                    if function.types.are_equal(stored_ty, value_ty) {
                        // previous store is dead and can be deleted
                        ir.delete(store_idx);
                    }
                }

                // invalidate potentially aliasing stored values on store
                stored_values.retain(|&ptr_idx, _| !can_alias.get(ptr_idx as usize));

                stored_values.insert(ptr_idx, (i, value, value_ty));
            } else if inst.tag == Tag::Load {
                let ptr = inst.data.un_op();
                let Some(ptr_idx) = ptr.into_ref() else {
                    continue;
                };
                if let Some(&(_store_idx, stored, stored_ty)) = stored_values.get(&ptr_idx) {
                    if !function.types.are_equal(function.types[inst.ty], stored_ty) {
                        continue;
                    }
                    ir.delete(i);
                    renames.rename(i, stored);
                }
            } else if inst.tag == Tag::Call {
                // invalidate potentially aliasing stored values on call
                stored_values.retain(|&ptr_idx, _| !can_alias.get(ptr_idx as usize));
            }
        }
    }

    // now find and delete dead decls. Keep track of (dead, list of stores)
    let mut decls: HashMap<u32, (bool, Vec<u32>)> = HashMap::new();
    let visit_ref = |decls: &mut HashMap<u32, (bool, Vec<u32>)>, r: Ref| {
        if let Some(idx) = r.into_ref() {
            if ir.get_inst(idx).tag == Tag::Decl {
                match decls.entry(idx) {
                    Entry::Occupied(mut entry) => entry.get_mut().0 = false,
                    Entry::Vacant(entry) => {
                        entry.insert((false, Vec::new()));
                    }
                }
            }
        }
    };
    for block in ir.blocks() {
        for (i, inst) in ir.get_block(block) {
            match inst.tag {
                Tag::Decl => {
                    decls.entry(i).or_insert((true, Vec::new()));
                }
                Tag::Store => {
                    let (ptr, value) = inst.data.bin_op();
                    visit_ref(&mut decls, value);
                    if let Some(ptr_idx) = ptr.into_ref() {
                        if ir.get_inst(ptr_idx).tag == Tag::Decl {
                            decls.entry(ptr_idx).or_insert((true, Vec::new())).1.push(i);
                        }
                    }
                }
                _ => {
                    inst.visit_refs(ir, |r| visit_ref(&mut decls, r));
                }
            }
        }
    }

    // now delete all dead decls along with their stores
    for (decl_idx, stores) in decls
        .into_iter()
        .filter_map(|(i, (dead, stores))| dead.then_some((i, stores)))
    {
        ir.delete(decl_idx);
        for store_idx in stores {
            ir.delete(store_idx);
        }
    }
}
