use std::rc::Rc;

use types::{Layout, Primitive, Type};

use crate::{
    Compiler,
    check::expr::int_primitive_from_variant_count,
    compiler::ResolvedTypeContent,
    eval::{self, ConstValue},
    types::resolved_layout,
};

#[derive(Debug, Clone, Copy)]
pub struct UndefinedValue;

pub fn translate(
    value: &eval::ConstValue,
    ty: &Type,
    compiler: &mut Compiler,
    b: &mut [u8],
) -> Result<(), UndefinedValue> {
    if let Type::Invalid = ty {
        return Err(UndefinedValue);
    }
    // TODO: currently assumes little-endian target arch
    match value {
        eval::ConstValue::Undefined => return Err(UndefinedValue),
        eval::ConstValue::Unit => debug_assert!(b.is_empty()),
        &eval::ConstValue::Int(val) => match ty {
            Type::Primitive(Primitive::I8 | Primitive::U8) => b.copy_from_slice(&[val as u8]),
            Type::Primitive(Primitive::I16 | Primitive::U16) => {
                b.copy_from_slice(&(val as u16).to_le_bytes());
            }
            Type::Primitive(Primitive::I32 | Primitive::U32) => {
                b.copy_from_slice(&(val as u32).to_le_bytes());
            }
            Type::Primitive(Primitive::I64 | Primitive::U64) => {
                b.copy_from_slice(&u64::to_le_bytes(val));
            }
            Type::Primitive(Primitive::I128 | Primitive::U128) => {
                b.copy_from_slice(&(val as u128).to_le_bytes());
            }
            ty => unreachable!("unexpected type for integer ConstValue: {ty:?}"),
        },
        &eval::ConstValue::Float(val) => match ty {
            Type::Primitive(Primitive::F32) => b.copy_from_slice(&(val as f32).to_le_bytes()),
            Type::Primitive(Primitive::F64) => b.copy_from_slice(&val.to_le_bytes()),
            _ => unreachable!(),
        },
        eval::ConstValue::Aggregate(elems) => match ty {
            Type::Array(_) => todo!(),
            Type::DefId { id, generics } => {
                let def = Rc::clone(compiler.get_resolved_type_def(*id));
                match &def.def {
                    ResolvedTypeContent::Struct(struct_def) => {
                        let mut layout = Layout::EMPTY;
                        debug_assert_eq!(struct_def.field_count() as usize, elems.len());
                        for (val, (_, ty)) in elems.iter().zip(struct_def.all_fields()) {
                            let field_layout = resolved_layout(ty, compiler, generics)
                                .map_err(|_| UndefinedValue)?;
                            let offset = layout.accumulate(field_layout) as usize;
                            translate(
                                val,
                                ty,
                                compiler,
                                &mut b[offset..offset + field_layout.size as usize],
                            )?;
                        }
                    }
                    ResolvedTypeContent::Enum(enum_def) => {
                        let ConstValue::Int(active_variant) = elems[0] else {
                            unreachable!()
                        };
                        let variant_ty =
                            int_primitive_from_variant_count(enum_def.variants.len() as _);
                        let variant_layout = variant_ty.layout();
                        translate(
                            &elems[0],
                            &Type::Primitive(variant_ty),
                            compiler,
                            &mut b[..variant_layout.size as usize],
                        )?;
                        let arg_types = &enum_def.variants[active_variant as usize].1;
                        debug_assert_eq!(elems[1..].len(), arg_types.len());
                        let mut layout = variant_layout;
                        for (arg, arg_ty) in elems[1..].iter().zip(arg_types) {
                            let arg_layout = resolved_layout(arg_ty, compiler, generics)
                                .map_err(|_| UndefinedValue)?;
                            let offset = layout.accumulate(arg_layout) as usize;
                            translate(
                                arg,
                                arg_ty,
                                compiler,
                                &mut b[offset..offset + arg_layout.size as usize],
                            )?;
                        }
                    }
                }
            }
            Type::Tuple(_) => todo!(),
            Type::LocalEnum(_) => todo!(),
            Type::Primitive(_)
            | Type::Pointer(_)
            | Type::Generic(_)
            | Type::Function(_)
            | Type::Invalid => unreachable!(),
        },
    }
    Ok(())
}
