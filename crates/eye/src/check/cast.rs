use span::Span;

use crate::{hir::CastType, type_table::{TypeInfo, TypeTable, LocalTypeId}, error::{CompileError, Error}};


pub fn check(
    from_ty: LocalTypeId,
    to_ty: LocalTypeId,
    types: &TypeTable,
    span: impl FnOnce() -> Span,
) -> Result<CastType, Option<CompileError>> {
    Ok(match (types[from_ty], types[to_ty]) {
        (TypeInfo::Invalid, _) | (_, TypeInfo::Invalid) => return Err(None),
        (TypeInfo::Primitive(a), TypeInfo::Primitive(b)) if a.is_int() && b.is_int() => {
            CastType::Int {
                from: a.as_int().unwrap(),
                to: b.as_int().unwrap(),
            }
        }
        (TypeInfo::Primitive(a), TypeInfo::Primitive(b)) if a.is_float() && b.is_float() => {
            CastType::Float {
                from: a.as_float().unwrap(),
                to: b.as_float().unwrap(),
            }
        }
        (TypeInfo::Primitive(a), TypeInfo::Primitive(b)) if a.is_int() && b.is_float() => {
            CastType::IntToFloat {
                from: a.as_int().unwrap(),
                to: b.as_float().unwrap(),
            }
        }
        (TypeInfo::Primitive(a), TypeInfo::Primitive(b)) if a.is_float() && b.is_int() => {
            CastType::FloatToInt {
                from: a.as_float().unwrap(),
                to: b.as_int().unwrap(),
            }
        }
        (TypeInfo::Primitive(a), TypeInfo::Pointer(_)) if a.is_int() => {
            CastType::IntToPtr { from: a.as_int().unwrap() }
        }
        (TypeInfo::Pointer(_), TypeInfo::Primitive(b)) if b.is_int() => {
            CastType::PtrToInt { to: b.as_int().unwrap() }
        }
        (TypeInfo::Enum { ..}, TypeInfo::Primitive(b)) if b.is_int() => {
            // TODO: check enum is valid for casting
            CastType::EnumToInt { from: from_ty, to: b.as_int().unwrap() }
        }
        (a, b) => {
            let mut a_string = String::new();
            let mut b_string = String::new();
            types.type_to_string(a, &mut a_string);
            types.type_to_string(b, &mut b_string);
            return Err(Some(Error::InvalidCast { from: a_string, to: b_string }.at_span(span())));
        }
    })
}
