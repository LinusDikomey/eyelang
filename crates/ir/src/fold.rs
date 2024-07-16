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

macro_rules! def_fold_cmp {
    ($function: ident $op: tt) => {
        pub fn $function(a: u64, b: u64, ty: IrType) -> bool {
            match ty {
                IrType::U1 => (a != 0) $op (b != 0),
                IrType::U8 => (a as u8) $op (b as u8),
                IrType::I8 => (a as i8) $op (b as i8),
                IrType::U16 => (a as u16) $op (b as u16),
                IrType::I16 => (a as i16) $op (b as i16),
                IrType::U32 => (a as u32) $op (b as u32),
                IrType::I32 => (a as i32) $op (b as i32),
                IrType::U64 => a $op (b),
                IrType::I64 => (a as i64) $op (b as i64),
                IrType::U128 | IrType::I128 => todo!("fold 128-bit integers"),
                _ => unreachable!(),
            }
        }
    };
}

def_fold_cmp!(fold_lt <);
def_fold_cmp!(fold_gt >);
def_fold_cmp!(fold_le <=);
def_fold_cmp!(fold_ge >=);

pub fn fold_neg(a: u64, ty: IrType) -> u64 {
    debug_assert!(ty.is_signed_int() || ty.is_float());
    match ty {
        IrType::I8 => (a as i8).wrapping_neg() as u64,
        IrType::I16 => (a as i16).wrapping_neg() as u64,
        IrType::I32 => (a as i32).wrapping_neg() as u64,
        IrType::I64 => (a as i64).wrapping_neg() as u64,
        IrType::I128 => todo!("fold 128-bit integers"),
        IrType::F32 => (-f32::from_bits(a as u32)).to_bits() as u64,
        IrType::F64 => (-f64::from_bits(a)).to_bits(),
        _ => unreachable!(),
    }
}
