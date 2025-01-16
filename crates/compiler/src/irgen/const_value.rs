use types::{Primitive, Type};

use crate::eval;

#[derive(Debug, Clone, Copy)]
pub struct UndefinedValue;

pub fn translate(value: &eval::ConstValue, ty: &Type) -> Result<(Box<[u8]>, u64), UndefinedValue> {
    // TODO: currently assumes little-endian target arch
    Ok(match value {
        eval::ConstValue::Undefined => return Err(UndefinedValue),
        eval::ConstValue::Unit => (Box::new([]), 1),
        &eval::ConstValue::Bool(b) => (Box::new([b as u8]), 1),
        &eval::ConstValue::Int(val, _) => match ty {
            Type::Primitive(Primitive::I8 | Primitive::U8) => (Box::new([val as u8]), 1),
            Type::Primitive(Primitive::I16 | Primitive::U16) => {
                (Box::new((val as u16).to_le_bytes()), 2)
            }
            Type::Primitive(Primitive::I32 | Primitive::U32) => {
                (Box::new((val as u32).to_le_bytes()), 4)
            }
            _ => unreachable!(),
        },
        &eval::ConstValue::Float(val, _) => match ty {
            Type::Primitive(Primitive::F32) => ((val as f32).to_le_bytes().into(), 4),
            Type::Primitive(Primitive::F64) => (val.to_le_bytes().into(), 8),
            _ => unreachable!(),
        },
        eval::ConstValue::Tuple(_elems) => todo!(),
        eval::ConstValue::Typed(_id, _elems) => todo!(),
    })
}
