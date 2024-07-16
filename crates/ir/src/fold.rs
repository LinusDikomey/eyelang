use crate::IrType;

macro_rules! def_fold {
    ($function: ident $bool_function: ident $int_function: ident) => {
        pub fn $function(a: u64, b: u64, ty: IrType) -> u64 {
            match ty {
                IrType::U1 => $bool_function(a != 0, b != 0) as u64,
                IrType::U8 => (a as u8).$int_function(b as u8) as u64,
                IrType::I8 => (a as i8).$int_function(b as i8) as u64,
                IrType::U16 => (a as u16).$int_function(b as u16) as u64,
                IrType::I16 => (a as i16).$int_function(b as i16) as u64,
                IrType::U32 => (a as u32).$int_function(b as u32) as u64,
                IrType::I32 => (a as i32).$int_function(b as i32) as u64,
                IrType::U64 => a.$int_function(b),
                IrType::I64 => (a as i64).$int_function(b as i64) as u64,
                IrType::U128 | IrType::I128 => todo!("fold 128-bit integers"),
                _ => unreachable!(),
            }
        }
    };
}
fn add_bool(a: bool, b: bool) -> bool {
    a != b
}
def_fold!(fold_add add_bool wrapping_add);
def_fold!(fold_sub add_bool wrapping_sub);

fn mul_bool(a: bool, b: bool) -> bool {
    a & b
}
def_fold!(fold_mul mul_bool wrapping_mul);

fn div_bool(a: bool, b: bool) -> bool {
    if !b {
        panic!("bool div by zero")
    }
    a
}
def_fold!(fold_div_unchecked div_bool wrapping_div);
pub fn fold_div(a: u64, b: u64, ty: IrType) -> u64 {
    if b == 0 {
        // TODO: decide what happens on div-by-zero. Until then, just return 0.
        return 0;
    }
    fold_div_unchecked(a, b, ty)
}
def_fold!(fold_rem_unchecked div_bool wrapping_rem);
pub fn fold_rem(a: u64, b: u64, ty: IrType) -> u64 {
    if b == 0 {
        // TODO: decide what happens on rem-by-zero. Until then, just return 0.
        return 0;
    }
    fold_rem_unchecked(a, b, ty)
}
