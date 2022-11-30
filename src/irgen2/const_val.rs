use crate::{ir::{builder::IrBuilder, Ref}, resolve::{const_val::ConstVal, type_info::TypeTableIndex}};

use super::Res;



pub fn build(ir: &mut IrBuilder, val: &ConstVal, ty: TypeTableIndex) -> Res {
    match val {
        ConstVal::Invalid => Res::Val(Ref::UNDEF),
        ConstVal::Unit => Res::Val(Ref::UNIT),
        &ConstVal::Int(_, val) => {
            let (abs, sign) = if val < 0 {
                (-val as u128, true)
            } else {
                (val as u128, false)
            };
            let abs_ref = if abs > u64::MAX as _ {
                ir.build_large_int(abs, ty)
            } else {
                ir.build_int(abs as u64, ty)
            };
            if sign {
                Res::Val(ir.build_neg(abs_ref, ty))
            } else {
                Res::Val(abs_ref)
            }
        }
        ConstVal::Float(_, _) => todo!(),
        ConstVal::String(_) => todo!(),
        ConstVal::EnumVariant(_) => todo!(),
        ConstVal::Bool(_) => todo!(),
        ConstVal::Symbol(_) => todo!(),
        ConstVal::NotGenerated => todo!(),
    }
}