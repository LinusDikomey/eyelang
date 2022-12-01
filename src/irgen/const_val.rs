use crate::{ir::{builder::{IrBuilder, IrTypeTable}, Ref, RefVal}, resolve::{const_val::ConstVal, type_info::TypeTableIndex}};

use super::Res;



pub fn build<IrTypes: IrTypeTable>(ir: &mut IrBuilder<IrTypes>, val: &ConstVal, ty: TypeTableIndex) -> Res {
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
        ConstVal::Float(_, val) => Res::Val(ir.build_float(*val, ty)),
        ConstVal::String(bytes) => Res::Val(ir.build_string(&bytes,true, ty)),
        ConstVal::EnumVariant(_variant) => todo!(),
        &ConstVal::Bool(b) => Res::Val(Ref::val(if b { RefVal::True } else { RefVal::False })),
    }
}