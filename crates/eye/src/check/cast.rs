use crate::{hir::CastType, type_table::{TypeInfo, TypeTable, LocalTypeId}, error::Error};


pub fn check(
    from_ty: LocalTypeId,
    to_ty: LocalTypeId,
    types: &TypeTable,
) -> (CastType, Option<Error>) {
    let mut error = None;
    let cast = match (types[from_ty], types[to_ty]) {
        (TypeInfo::Invalid, _) | (_, TypeInfo::Invalid) => CastType::Invalid,
        (TypeInfo::Primitive(a), TypeInfo::Primitive(b)) if a.is_int() && b.is_int() => {
            let from = a.as_int().unwrap();
            let to = b.as_int().unwrap();
            if from == to {
                error = Some(Error::TrivialCast);
                CastType::Noop
            } else {
                CastType::Int { from, to }
            }
        }
        (TypeInfo::Primitive(a), TypeInfo::Primitive(b)) if a.is_float() && b.is_float() => {
            let from = a.as_float().unwrap();
            let to = b.as_float().unwrap();
            if from == to {
                error = Some(Error::TrivialCast);
                CastType::Noop
            } else {
                CastType::Float { from, to }
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
        (TypeInfo::Pointer(_), TypeInfo::Pointer(_)) => {
            // TODO: check pointees are different, emit TrivialCast otherwise
            // pointers are untyped in the ir
            CastType::Noop
        }
        (a, b) => {
            let mut a_string = String::new();
            let mut b_string = String::new();
            types.type_to_string(a, &mut a_string);
            types.type_to_string(b, &mut b_string);
            error = Some(Error::InvalidCast { from: a_string, to: b_string });
            CastType::Invalid
        }
    };
    (cast, error)
}
