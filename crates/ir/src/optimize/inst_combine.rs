use color_format::ceprintln;

use crate::{fold, Function, FunctionIr, Instruction, IrType, IrTypes, Ref, Tag};

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
                let m = match_patterns(ir, &function.types, i, instrument);
                match m {
                    Match::None => break,
                    Match::Replace(new_inst) => {
                        total_matches += 1;
                        // sometimes, a constant fold creates a boolean (U1) where the
                        // materialization instruction can be skipped
                        if new_inst.tag == Tag::Int
                            && matches!(function.types[new_inst.ty], IrType::U1)
                        {
                            ir.delete(i);
                            renames.rename(i, Ref::bool(new_inst.data.int() != 0));
                            break;
                        }
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

#[allow(unused_macros)] // TODO: remove allow when unary patterns are used
macro_rules! nullary_op_pat {
    ($tag: ident $ir: ident $r: expr) => {
        if !$r
            .into_ref()
            .is_some_and(|r_idx| $ir.get_inst(r_idx).tag == Tag::$tag)
        {
            return Match::None;
        }
    };
}

macro_rules! un_op_pat {
    ($tag: ident $ir: ident, $r: expr, $val: tt) => {
        let Some(r_idx) = $r.into_ref() else {
            return Match::None;
        };
        if $ir.get_inst(r_idx).tag != Tag::$tag {
            return Match::None;
        }
        let val = $ir.get_inst(r_idx).data.un_op();
        pattern_ref!($ir, val, $val);
    };
}

macro_rules! bin_op_pat {
    ($tag: ident $ir: ident, $r: expr, $lhs: tt, $rhs: tt) => {
        let Some(r_idx) = $r.into_ref() else {
            return Match::None;
        };
        if $ir.get_inst(r_idx).tag != Tag::$tag {
            return Match::None;
        }
        let (lhs, rhs) = $ir.get_inst(r_idx).data.bin_op();
        pattern_ref!($ir, lhs, $lhs);
        pattern_ref!($ir, rhs, $rhs);
    };
}

macro_rules! value_pat {
    ($val: expr, _) => {
        _ = $val
    };
    ($val: expr, $i: literal) => {
        if $val != $i {
            return Match::None;
        }
    };
    ($val: expr, $name: ident) => {
        let $name = $val;
    };
}

macro_rules! pattern_ref {
    ($ir: ident, $r: expr, undef) => {
        if $r != Ref::UNDEF {
            return Match::None;
        }
    };
    ($ir: ident, $r: expr, true) => {
        if $r != Ref::bool(true) {
            return Match::None;
        }
    };
    ($ir: ident, $r: expr, false) => {
        if $r != Ref::bool(false) {
            return Match::None;
        }
    };
    ($ir: ident, $r: expr, (bool $b: ident)) => {
        let $b = match $r {
            r if r == Ref::bool(false) => false,
            r if r == Ref::bool(true) => true,
            _ => return Match::None,
        };
    };
    ($ir: ident, $r: expr, (const $val: ident)) => {
        let r = $r;
        let $val = if let Some(r_val) = r.into_val() {
            match r_val {
                RefVal::True => 1,
                RefVal::False => 0,
                _ => return Match::None,
            }
        } else {
            let r_idx = r.into_ref().unwrap();
            let inst = $ir.get_inst(r_idx);
            if inst.tag == Tag::Int {
                inst.data.int()
            } else if inst.tag == Tag::Float {
                inst.data.float().to_bits()
            } else {
                return Match::None;
            };
        }
    };
    ($ir: ident, $r: expr, ($name: ident @ $pat: tt)) => {
        let $name = $r;
        pattern_ref!($ir, $name, $pat);
    };
    ($ir: ident, $r: expr, __) => {
        _ = $r;
    };
    ($ir: ident, $r: expr, $name: ident) => {
        let $name = $r;
    };
    // TODO (Global)
    ($ir: ident, $r: expr, (Ret $val: tt)) => { un_op_pat!(Ret $ir, $r, $val) };
    // TODO (Goto)
    // TODO (Branch)
    ($ir: ident, $r: expr, (Int $val: tt)) => {
        let r = $r;
        let val = match r.into_val() {
            Some($crate::RefVal::False) => 0,
            Some($crate::RefVal::True) => 1,
            Some(_) => return Match::None,
            None => {
                let inst = $ir.get_inst(r.into_ref().unwrap());
                if inst.tag != Tag::Int {
                    return Match::None;
                }
                inst.data.int()
            }
        };
        value_pat!(val, $val);
    };
    // TODO (LargeInt)
    ($ir: ident, $r: expr, (Float $val: tt)) => {
        let Some(r_idx) = $r.into_ref() else {
            return Match::None;
        };
        if $ir.get_inst(r_idx).tag != Tag::Float {
            return Match::None;
        }
        let val = $ir.get_inst(r_idx).data.float();
        value_pat!(val, $val);
    };

    // TODO (Decl)
    ($ir: ident, $r: expr, (Load $val: tt)) => { un_op_pat!(Load $ir, $r, $val) };
    ($ir: ident, $r: expr, (Store $lhs: tt $rhs: tt)) => { bin_op_pat!(Store $ir, $r, $lhs, $rhs) };
    // TODO (MemberPtr)
    // TODO (MemberValue)
    // TODO (ArrayIndex)
    // TODO (String)
    // TODO (Call)

    ($ir: ident, $r: expr, (Neg $val: tt)) => { un_op_pat!(Neg $ir, $r, $val) };
    ($ir: ident, $r: expr, (Not $val: tt)) => { un_op_pat!(Not $ir, $r, $val) };

    ($ir: ident, $r: expr, (Add $lhs: tt $rhs: tt)) => { bin_op_pat!(Add $ir, $r, $lhs, $rhs) };
    ($ir: ident, $r: expr, (Sub $lhs: tt $rhs: tt)) => { bin_op_pat!(Sub $ir, $r, $lhs, $rhs) };
    ($ir: ident, $r: expr, (Mul $lhs: tt $rhs: tt)) => { bin_op_pat!(Mul $ir, $r, $lhs, $rhs) };
    ($ir: ident, $r: expr, (Div $lhs: tt $rhs: tt)) => { bin_op_pat!(Div $ir, $r, $lhs, $rhs) };
    ($ir: ident, $r: expr, (Rem $lhs: tt $rhs: tt)) => { bin_op_pat!(Rem $ir, $r, $lhs, $rhs) };

    ($ir: ident, $r: expr, (Or $lhs: tt $rhs: tt)) => { bin_op_pat!(Or $ir, $r, $lhs, $rhs) };
    ($ir: ident, $r: expr, (And $lhs: tt $rhs: tt)) => { bin_op_pat!(And $ir, $r, $lhs, $rhs) };

    ($ir: ident, $r: expr, (Eq $lhs: tt $rhs: tt)) => { bin_op_pat!(Eq $ir, $r, $lhs, $rhs) };
    ($ir: ident, $r: expr, (NE $lhs: tt $rhs: tt)) => { bin_op_pat!(NE $ir, $r, $lhs, $rhs) };
    ($ir: ident, $r: expr, (LT $lhs: tt $rhs: tt)) => { bin_op_pat!(LT $ir, $r, $lhs, $rhs) };
    ($ir: ident, $r: expr, (GT $lhs: tt $rhs: tt)) => { bin_op_pat!(GT $ir, $r, $lhs, $rhs) };
    ($ir: ident, $r: expr, (LE $lhs: tt $rhs: tt)) => { bin_op_pat!(LE $ir, $r, $lhs, $rhs) };
    ($ir: ident, $r: expr, (GE $lhs: tt $rhs: tt)) => { bin_op_pat!(GE $ir, $r, $lhs, $rhs) };

    ($ir: ident, $r: expr, (CastInt $val: tt)) => { un_op_pat!(CastInt $ir, $r, $val) };
    ($ir: ident, $r: expr, (CastFloat $val: tt)) => { un_op_pat!(CastFloat $ir, $r, $val) };
    ($ir: ident, $r: expr, (CastIntToFloat $val: tt)) => { un_op_pat!(CastIntToFloat $ir, $r, $val) };
    ($ir: ident, $r: expr, (CastFloatToInt $val: tt)) => { un_op_pat!(CastFloatToInt $ir, $r, $val) };

    ($ir: ident, $r: expr, (IntToPtr $val: tt)) => { un_op_pat!(IntToPtr $ir, $r, $val) };
    ($ir: ident, $r: expr, (PtrToInt $val: tt)) => { un_op_pat!(PtrToInt $ir, $r, $val) };

    // TODO (Asm)
}

macro_rules! patterns {
    (
        $function: ident
        $ir: ident
        $types: ident
        $inst: ident
        $($pattern_name: ident : $pattern: tt $(if $cond: expr)? => $result: expr)*
    ) => {
        fn $function(
            $ir: &FunctionIr,
            #[allow(unused)] $types: &IrTypes,
            idx: u32,
            instrument: bool,
        ) -> Match {
            #[allow(unused)]
            let $inst = $ir.get_inst(idx);
            let r = Ref::index(idx);
            $(
                let result = (|| {
                    pattern_ref!($ir, r, $pattern);
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

pub fn ref_value_eq(ir: &FunctionIr, a: Ref, b: Ref) -> bool {
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
    // ---------- undef propagation ----------
    add_undef_l:
        (Add undef __) => Match::Delete(Ref::UNDEF)
    add_undef_r:
        (Add __ undef) => Match::Delete(Ref::UNDEF)
    sub_undef_l:
        (Sub undef __) => Match::Delete(Ref::UNDEF)
    sub_undef_r:
        (Sub __ undef) => Match::Delete(Ref::UNDEF)
    store_undef:
        (Store __ undef) => Match::Delete(Ref::UNDEF)
    // ---------- constant folding operations ----------
    add_consts:
        (Add (Int l) (Int r)) =>
            Match::Replace(Instruction::int(fold::fold_add(l, r, types[inst.ty]), inst.ty))
    add_fconsts:
        (Add (Float l) (Float r)) => Match::Replace(Instruction::float(l + r, inst.ty))
    sub_consts:
        (Sub (Int l) (Int r)) =>
            Match::Replace(Instruction::int(fold::fold_sub(l, r, types[inst.ty]), inst.ty))
    sub_fconsts:
        (Sub (Float l) (Float r)) => Match::Replace(Instruction::float(l - r, inst.ty))
    mul_consts:
        (Mul (Int l) (Int r)) =>
            Match::Replace(Instruction::int(fold::fold_mul(l, r, types[inst.ty]), inst.ty))
    mul_fconsts:
        (Mul (Float l) (Float r)) => Match::Replace(Instruction::float(l * r, inst.ty))
    div_consts:
        (Div (Int l) (Int r)) =>
            Match::Replace(Instruction::int(fold::fold_div(l, r, types[inst.ty]), inst.ty))
    div_fconsts:
        (Div (Float l) (Float r)) => Match::Replace(Instruction::float(l / r, inst.ty))
    rem_consts:
        (Rem (Int l) (Int r)) =>
            Match::Replace(Instruction::int(fold::fold_rem(l, r, types[inst.ty]), inst.ty))
    rem_fconsts:
        (Rem (Float l) (Float r)) => Match::Replace(Instruction::float(l % r, inst.ty))

    not_const_true:
        (Not true) => Match::Delete(Ref::bool(false))
    not_const_false:
        (Not false) => Match::Delete(Ref::bool(true))

    neg_const:
        (Neg (Int x)) => Match::Replace(Instruction::int(fold::fold_neg(x, types[inst.ty]), inst.ty))
    neg_fconst:
        (Neg (Float x)) => Match::Replace(Instruction::float(-x, inst.ty))

    eq_consts:
        (Eq (Int l) (Int r)) => Match::Delete(Ref::bool(l == r))
    eq_consts_bool:
        (Eq (bool l) (bool r)) => Match::Delete(Ref::bool(l == r))
    eq_consts_float:
        (Eq (Float l) (Float r)) => Match::Delete(Ref::bool(l == r))
    ne_consts:
        (NE (Int l) (Int r)) => Match::Delete(Ref::bool(l != r))
    // TODO: fold comparisons
    lt_consts:
        (LT (l_ref @ (Int l)) (Int r)) =>
            Match::Delete(Ref::bool(fold::fold_lt(l, r, ir.get_ref_ty(l_ref, types))))
    gt_consts:
        (GT (l_ref @ (Int l)) (Int r)) =>
            Match::Delete(Ref::bool(fold::fold_gt(l, r, ir.get_ref_ty(l_ref, types))))
    le_consts:
        (LE (l_ref @ (Int l)) (Int r)) =>
            Match::Delete(Ref::bool(fold::fold_le(l, r, ir.get_ref_ty(l_ref, types))))
    ge_consts:
        (GE (l_ref @ (Int l)) (Int r)) =>
            Match::Delete(Ref::bool(fold::fold_ge(l, r, ir.get_ref_ty(l_ref, types))))


    // ---------- canonicalization (moving constants to the right side) ----------

    add_canonicalize:
        (Add (l @ (Int __)) r) =>
            Match::Replace(Instruction::add(r, l, inst.ty))
    mul_canonicalize:
        (Mul (l @ (Int __)) r) =>
            Match::Replace(Instruction::mul(r, l, inst.ty))

    eq_canonicalize:
        (Eq (l @ (Int _)) r) => Match::Replace(Instruction::eq(r, l, inst.ty))
    ne_canonicalize:
        (NE (l @ (Int _)) r) => Match::Replace(Instruction::ne(r, l, inst.ty))
    lt_canonicalize:
        (LT (l @ (Int _)) r) =>
            Match::Replace(Instruction::ge(r, l, inst.ty))
    gt_canonicalize:
        (GT (l @ (Int _)) r) =>
            Match::Replace(Instruction::le(r, l, inst.ty))
    le_canonicalize:
        (LE (l @ (Int _)) r) =>
            Match::Replace(Instruction::gt(r, l, inst.ty))
    ge_canonicalize:
        (GE (l @ (Int _)) r) =>
            Match::Replace(Instruction::lt(r, l, inst.ty))

    add_identity:
        (Add l (Int 0)) => Match::Delete(l)
    sub_identity:
        (Sub l (Int 0)) => Match::Delete(l)
    mul_identity:
        (Mul l (Int 1)) => Match::Delete(l)
    div_identity:
        (Div l (Int 1)) => Match::Delete(l)

    or_identity_1:
        (Or l false) => Match::Delete(l)
    or_identity_2:
        (Or false r) => Match::Delete(r)

    and_identity_1:
        (And l true) => Match::Delete(l)
    and_identity_2:
        (And true r) => Match::Delete(r)


    // ---------- trivial results ----------
    sub_trivial:
        (Sub l r) if ref_value_eq(ir, l, r) => Match::Replace(Instruction::int(0, inst.ty))
    eq_trivial:
        (Eq l r) if ref_value_eq(ir, l, r) => Match::Delete(Ref::bool(true))
    or_trivial_1:
        (Or __ true) => Match::Delete(Ref::bool(true))
    or_trivial_2:
        (Or true __) => Match::Delete(Ref::bool(true))
    and_trivial_1:
        (And __ false) => Match::Delete(Ref::bool(false))
    and_trivial_2:
        (And false __) => Match::Delete(Ref::bool(false))

    eq_true:
        (Eq l true) => Match::Delete(l)
    ne_false:
        (NE l false) => Match::Delete(l)
    eq_false:
        (Eq l false) => Match::Replace(Instruction::not(l, inst.ty))
    ne_true:
        (NE l true) => Match::Replace(Instruction::not(l, inst.ty))

    ne_trivial:
        (NE l r) if ref_value_eq(ir, l, r) => Match::Delete(Ref::bool(false))
    ge_trivial:
        (GE l (Int 0)) if ir.get_ref_ty(l, types).is_unsigned_int() => Match::Delete(Ref::bool(true))

    rem_always_zero:
        (Rem __ (Int 1)) => Match::Replace(Instruction::int(0, inst.ty))

    redundant_add_sub:
        (Add (Sub a x) y) if ref_value_eq(ir, x, y) => Match::Delete(a)
    redundant_sub_add:
        (Sub (Add a x) y) if ref_value_eq(ir, x, y) => Match::Delete(a)
    redundant_div_mul:
        (Mul (Div a x) y) if ref_value_eq(ir, x, y) => Match::Delete(a)
    redundant_not_not:
        (Not (Not x)) => Match::Delete(x)

    // ---------- replace comparisons with eq/ne ----------
    gt_0_unsigned:
        (GT l (zero @ (Int 0))) if ir.get_ref_ty(l, types).is_unsigned_int() => Match::Replace(Instruction::ne(l, zero, inst.ty))

    // TODO: the patterns below require adding additional instructions
    //lt_1_unsigned:
    // TODO: add Int(1)
    //    (LT l (Int 1)) if types[inst.ty].is_unsigned_int() => Match::Replace(Instruction::eq(l, int_1, inst.ty)),

    //add_add:
    // TODO: add Int(fold_add(a, b)) and fold add
    //(Add (Add l (Int a)) (Int b)) => Match::Replace(Instruction::int(l, folded)),
);
