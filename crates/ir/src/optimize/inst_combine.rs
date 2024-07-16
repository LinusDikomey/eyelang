use crate::{Function, FunctionIr, Instruction, IrTypes, Ref, Tag};

use super::RenameTable;

#[derive(Debug)]
pub struct InstCombine;
impl super::FunctionPass for InstCombine {
    fn run(&self, function: &mut Function) {
        run(function);
    }
}

pub fn run(function: &mut Function) {
    let Some(ir) = &mut function.ir else { return };
    let mut renames = RenameTable::new(ir);
    for block in ir.blocks() {
        for i in ir.get_block_range(block) {
            let mut inst = ir.get_inst(i);
            renames.visit_inst(ir, &mut inst);
            ir.replace(i, inst);
            // try applying patterns until no more matches are found
            loop {
                let m = match_patterns(ir, &function.types, inst, true);
                match m {
                    Match::None => break,
                    Match::Replace(new_inst) => {
                        inst = new_inst;
                        ir.replace(i, inst);
                    }
                    Match::Delete(r) => {
                        assert_ne!(
                            r,
                            Ref::index(i),
                            "can't replace an instruction with it's own index, just do nothing instead"
                        );
                        ir.delete(i);
                        renames.rename(i, r);
                        break;
                    }
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

macro_rules! ref_matches_pattern {
    ($ir: ident, $r: expr, ($name: ident @ $pat: tt)) => {
        let $name = $r;
        ref_matches_pattern!($ir, $name, $pat);
    };
    // One underscore doesn't work here for some reason. Just use 2 underscores for now.
    ($ir: ident, $r: expr, __) => {};
    ($ir: ident, $r: expr, $name: ident) => {
        let $name = $r;
    };
    ($ir: ident, $r: expr, (Int $val: literal)) => {
        let Some(r_idx) = $r.into_ref() else {
            return Match::None;
        };
        if $ir.get_inst(r_idx).tag != Tag::Int {
            return Match::None;
        }
        if $ir.get_inst(r_idx).data.int() != $val {
            return Match::None;
        }
    };
    ($ir: ident, $r: expr, (Int $val: ident)) => {
        let Some(r_idx) = $r.into_ref() else {
            return Match::None;
        };
        if $ir.get_inst(r_idx).tag != Tag::Int {
            return Match::None;
        }
        let $val = $ir.get_inst(r_idx).data.int();
    };
    ($ir: ident, $r: expr, ($constructor: ident $lhs: tt $rhs: tt)) => {
        let Some(r_idx) = $r.into_ref() else {
            return Match::None;
        };
        if $ir.get_inst(r_idx).tag != Tag::$constructor {
            return Match::None;
        }
        let (__lhs, __rhs) = $ir.get_inst(r_idx).data.bin_op();
        ref_matches_pattern!($ir, __lhs, $lhs);
        ref_matches_pattern!($ir, __rhs, $rhs);
    };
}

macro_rules! patterns {
    ($function: ident $ir: ident  $types: ident $inst: ident $($pattern_name: ident : ($constructor: ident $lhs: tt $rhs: tt) $(if $cond: expr)? => $result: expr,)*) => {
        fn $function($ir: &FunctionIr, $types: &IrTypes, $inst: Instruction, diagnose: bool) -> Match {
            $(
                let result = (|| {
                    if $inst.tag != Tag::$constructor {
                        return Match::None;
                    }
                    let (lhs, rhs) = $inst.data.bin_op();
                    ref_matches_pattern!($ir, lhs, $lhs);
                    ref_matches_pattern!($ir, rhs, $rhs);
                    $(
                        if !($cond) {
                            return Match::None;
                        }
                    )*
                    if diagnose {
                        eprintln!("Matched pattern {}", stringify!($pattern_name));
                    }
                    $result
                })();
                if result.success() { return result; }
            )*
            Match::None
        }
    };
}

fn ref_value_eq(ir: &FunctionIr, a: Ref, b: Ref) -> bool {
    if a == b {
        return true;
    }
    let Some(a_idx) = a.into_ref() else {
        return false;
    };
    let Some(b_idx) = b.into_ref() else {
        return false;
    };
    let a = ir.get_inst(a_idx);
    let b = ir.get_inst(b_idx);
    if a.tag == Tag::Int && b.tag == Tag::Int && a.data.int() == b.data.int() {
        return true;
    }
    if a.tag == Tag::Float && b.tag == Tag::Float && a.data.float() == b.data.float() {
        return true;
    }
    false
}

patterns!(match_patterns ir types inst
    add_consts:
        (Add (Int l) (Int r)) => Match::Replace(Instruction::int(crate::fold::fold_add(l, r, types[inst.ty]), inst.ty)),
    add_canonicalize:
        (Add (l @ (Int __)) r) => Match::Replace(Instruction::add(r, l, inst.ty)),

    sub_consts:
        (Sub (Int l) (Int r)) => Match::Replace(Instruction::int(crate::fold::fold_sub(l, r, types[inst.ty]), inst.ty)),

    mul_consts:
        (Mul (Int l) (Int r)) => Match::Replace(Instruction::int(crate::fold::fold_mul(l, r, types[inst.ty]), inst.ty)),
    mul_canonicalize:
        (Mul (l @ (Int __)) r) => Match::Replace(Instruction::mul(r, l, inst.ty)),

    div_consts:
        (Div (Int l) (Int r)) => Match::Replace(Instruction::int(crate::fold::fold_div(l, r, types[inst.ty]), inst.ty)),

    rem_consts:
        (Rem (Int l) (Int r)) => Match::Replace(Instruction::int(crate::fold::fold_rem(l, r, types[inst.ty]), inst.ty)),

    add_identity:
        (Add l (Int 0)) => Match::Delete(l),
    sub_identity:
        (Sub l (Int 0)) => Match::Delete(l),
    mul_identity:
        (Mul l (Int 1)) => Match::Delete(l),
    div_identity:
        (Div l (Int 1)) => Match::Delete(l),

    redundant_add_sub:
        (Add (Sub a x) y) if ref_value_eq(ir, x, y) => Match::Delete(a),
    redundant_sub_add:
        (Sub (Add a x) y) if ref_value_eq(ir, x, y) => Match::Delete(a),
    //add_add:
        // TODO: when you can add instructions, add int(fold_add(a, b)) and fold add
        //(Add (Add base (Int a)) (Int b)) => Match::None,
);
