use crate::{Data, FunctionIr, Instruction, IrType, IrTypes, Ref, Tag};

use super::RenameTable;

pub fn run(function: &mut crate::Function) {
    let Some(ir) = &mut function.ir else { return };
    let mut renames = RenameTable::new(ir);
    for block in ir.blocks() {
        for i in ir.get_block_range(block) {
            let mut inst = ir.get_inst(i);
            renames.visit_inst(ir, &mut inst);
            ir.replace(i, inst);
            let m = match_inst(ir, &function.types, inst);
            match m {
                Match::None => {}
                Match::Replace(new_inst) => ir.replace(i, new_inst),
                Match::Delete(r) => {
                    assert_ne!(
                        r,
                        Ref::index(i),
                        "can't replace an instruction with it's own index, just do nothing instead"
                    );
                    ir.delete(i);
                    renames.rename(i, r);
                }
            }
        }
    }
}

enum Match {
    None,
    /// replace the matching instruction with another instruction
    Replace(Instruction),
    /// delete the matching instruction and replace with the given value
    Delete(Ref),
}
impl Match {
    fn success(&self) -> bool {
        !matches!(self, Self::None)
    }
}

fn get_const_int(ir: &FunctionIr, r: Ref) -> Option<u64> {
    if let Some(val) = r.into_val() {
        match val {
            crate::RefVal::True => Some(1),
            crate::RefVal::False => Some(0),
            crate::RefVal::Unit => None,
            crate::RefVal::Undef => None,
        }
    } else {
        let inst = ir.get_inst(r.into_ref().unwrap());
        if inst.tag == Tag::Int {
            return Some(inst.data.int());
        }
        None
    }
}

fn match_inst(ir: &FunctionIr, types: &IrTypes, inst: Instruction) -> Match {
    if inst.tag == Tag::Add {
        let (l, r) = inst.data.bin_op();
        match (get_const_int(ir, l), get_const_int(ir, r)) {
            (Some(a), Some(b)) => {
                return Match::Replace(Instruction {
                    tag: Tag::Int,
                    data: Data {
                        int: fold_add(a, b, types[inst.ty]),
                    },
                    ty: inst.ty,
                })
            }
            (Some(0), None) => return Match::Delete(r),
            (None, Some(0)) => return Match::Delete(r),
            (Some(c), None) => {
                if let Some(r_ref) = r.into_ref() {
                    let m = add_const(ir, ir.get_inst(r_ref), c, types[inst.ty]);
                    if m.success() {
                        return m;
                    }
                }
                // normalize to always have the constant on the right
                return Match::Replace(Instruction {
                    data: Data { bin_op: (r, l) },
                    tag: Tag::Add,
                    ty: inst.ty,
                });
            }
            (None, Some(c)) => {
                if let Some(l_ref) = l.into_ref() {
                    let m = add_const(ir, ir.get_inst(l_ref), c, types[inst.ty]);
                    if m.success() {
                        return m;
                    }
                }
            }
            (None, None) => {}
        }
    }
    Match::None
}

fn fold_add(a: u64, b: u64, ty: IrType) -> u64 {
    match ty {
        IrType::U1 => a.wrapping_add(b) % 2,
        IrType::U8 | IrType::I8 => a.wrapping_add(b) % (u8::MAX as u64 + 1),
        IrType::U16 | IrType::I16 => a.wrapping_add(b) % (u16::MAX as u64 + 1),
        IrType::U32 | IrType::I32 => a.wrapping_add(b) % (u32::MAX as u64 + 1),
        IrType::U64 | IrType::I64 => a.wrapping_add(b),
        IrType::U128 | IrType::I128 => todo!("fold 128-bit integers"),
        _ => unreachable!(),
    }
}

fn add_const(ir: &FunctionIr, l: Instruction, r: u64, _ty: IrType) -> Match {
    if l.tag == Tag::Sub {
        if get_const_int(ir, l.data.bin_op().1).is_some_and(|val| val == r) {
            return Match::Delete(l.data.bin_op().0);
        }
    }
    Match::None
}
