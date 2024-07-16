use color_format::ceprintln;

use crate::{fold, Function, FunctionIr, Instruction, IrTypes, Ref, Tag};

use super::RenameTable;

#[derive(Debug)]
pub struct InstCombine;
impl super::FunctionPass for InstCombine {
    fn run(&self, function: &mut Function, instrument: bool) {
        run(function, instrument);
    }
}

pub fn run(function: &mut Function, instrument: bool) {
    let Some(ir) = &mut function.ir else { return };
    let mut renames = RenameTable::new(ir);
    let mut total_matches: usize = 0;
    for block in ir.blocks() {
        for i in ir.get_block_range(block) {
            let mut inst = ir.get_inst(i);
            renames.visit_inst(ir, &mut inst);
            ir.replace(i, inst);
            // try applying patterns until no more matches are found
            loop {
                let m = match_patterns(ir, &function.types, inst, instrument);
                match m {
                    Match::None => break,
                    Match::Replace(new_inst) => {
                        inst = new_inst;
                        ir.replace(i, inst);
                        total_matches += 1;
                    }
                    Match::Delete(r) => {
                        assert_ne!(
                            r,
                            Ref::index(i),
                            "can't replace an instruction with it's own index, just do nothing instead"
                        );
                        ir.delete(i);
                        renames.rename(i, r);
                        total_matches += 1;
                        break;
                    }
                }
            }
        }
    }
    if instrument {
        ceprintln!(
            "InstCombine matched {total_matches} times in #r<{}>",
            function.name
        )
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
    ($ir: ident, $r: expr, __) => {
        _ = $r;
    };
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
        fn $function($ir: &FunctionIr, $types: &IrTypes, $inst: Instruction, instrument: bool) -> Match {
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
                    if instrument {
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
    // ---------- constant folding operations ----------
    add_consts:
        (Add (Int l) (Int r)) => Match::Replace(Instruction::int(fold::fold_add(l, r, types[inst.ty]), inst.ty)),
    sub_consts:
        (Sub (Int l) (Int r)) => Match::Replace(Instruction::int(fold::fold_sub(l, r, types[inst.ty]), inst.ty)),
    mul_consts:
        (Mul (Int l) (Int r)) => Match::Replace(Instruction::int(fold::fold_mul(l, r, types[inst.ty]), inst.ty)),
    div_consts:
        (Div (Int l) (Int r)) => Match::Replace(Instruction::int(fold::fold_div(l, r, types[inst.ty]), inst.ty)),
    rem_consts:
        (Rem (Int l) (Int r)) => Match::Replace(Instruction::int(fold::fold_rem(l, r, types[inst.ty]), inst.ty)),

    eq_consts:
        (Eq (Int l) (Int r)) => Match::Delete(Ref::bool(l == r)),
    ne_consts:
        (NE (Int l) (Int r)) => Match::Delete(Ref::bool(l != r)),
    // TODO: fold comparisons
    lt_consts:
        (LT (l_ref @ (Int l)) (Int r)) => Match::Delete(Ref::bool(fold::fold_lt(l, r, ir.get_ref_ty(l_ref, types)))),
    gt_consts:
        (GT (l_ref @ (Int l)) (Int r)) => Match::Delete(Ref::bool(fold::fold_gt(l, r, ir.get_ref_ty(l_ref, types)))),
    le_consts:
        (LE (l_ref @ (Int l)) (Int r)) => Match::Delete(Ref::bool(fold::fold_le(l, r, ir.get_ref_ty(l_ref, types)))),
    ge_consts:
        (GE (l_ref @ (Int l)) (Int r)) => Match::Delete(Ref::bool(fold::fold_ge(l, r, ir.get_ref_ty(l_ref, types)))),


    // ---------- canonicalization (moving constants to the right side) ----------

    add_canonicalize:
        (Add (l @ (Int __)) r) => Match::Replace(Instruction::add(r, l, inst.ty)),
    mul_canonicalize:
        (Mul (l @ (Int __)) r) => Match::Replace(Instruction::mul(r, l, inst.ty)),


    lt_canonicalize:
        (LT (l @ (Int __)) r) => Match::Replace(Instruction::ge(r, l, inst.ty)),
    gt_canonicalize:
        (GT (l @ (Int __)) r) => Match::Replace(Instruction::le(r, l, inst.ty)),
    le_canonicalize:
        (LE (l @ (Int __)) r) => Match::Replace(Instruction::gt(r, l, inst.ty)),
    ge_canonicalize:
        (GE (l @ (Int __)) r) => Match::Replace(Instruction::lt(r, l, inst.ty)),

    add_identity:
        (Add l (Int 0)) => Match::Delete(l),
    sub_identity:
        (Sub l (Int 0)) => Match::Delete(l),
    mul_identity:
        (Mul l (Int 1)) => Match::Delete(l),
    div_identity:
        (Div l (Int 1)) => Match::Delete(l),

    // ---------- trivial results ----------
    sub_trivial:
        (Sub l r) if ref_value_eq(ir, l, r) => Match::Replace(Instruction::int(0, inst.ty)),
    eq_trivial:
        (Eq l r) if ref_value_eq(ir, l, r) => Match::Delete(Ref::bool(true)),

    ne_trivial:
        (NE l r) if ref_value_eq(ir, l, r) => Match::Delete(Ref::bool(false)),
    ge_trivial:
        (GE l (Int 0)) if ir.get_ref_ty(l, types).is_unsigned_int() => Match::Delete(Ref::bool(true)),

    rem_always_zero:
        (Rem __ (Int 1)) => Match::Replace(Instruction::int(0, inst.ty)),

    redundant_add_sub:
        (Add (Sub a x) y) if ref_value_eq(ir, x, y) => Match::Delete(a),
    redundant_sub_add:
        (Sub (Add a x) y) if ref_value_eq(ir, x, y) => Match::Delete(a),

    // ---------- replace comparisons with eq/ne ----------
    gt_0_unsigned:
        (GT l (zero @ (Int 0))) if ir.get_ref_ty(l, types).is_unsigned_int() => Match::Replace(Instruction::ne(l, zero, inst.ty)),


    // TODO: the patterns below require adding additional instructions
    //lt_1_unsigned:
    // TODO: add Int(1)
    //    (LT l (Int 1)) if types[inst.ty].is_unsigned_int() => Match::Replace(Instruction::eq(l, int_1, inst.ty)),

    //add_add:
    // TODO: add Int(fold_add(a, b)) and fold add
    //(Add (Add l (Int a)) (Int b)) => Match::Replace(Instruction::int(l, folded)),
);
