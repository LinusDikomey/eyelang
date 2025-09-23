use error::Error;

use crate::{
    Compiler,
    hir::CastType,
    types::BaseType,
    typing::{LocalTypeId, TypeInfo, TypeTable},
};

pub fn check(
    from_ty: LocalTypeId,
    to_ty: LocalTypeId,
    compiler: &mut Compiler,
    types: &TypeTable,
) -> (CastType, Option<Error>) {
    let mut error = None;
    let cast = match (types[from_ty], types[to_ty]) {
        (TypeInfo::Instance(BaseType::Invalid, _), _)
        | (_, TypeInfo::Instance(BaseType::Invalid, _)) => CastType::Invalid,
        (TypeInfo::Instance(a, a_generics), TypeInfo::Instance(b, b_generics))
            if a_generics.is_empty() && b_generics.is_empty() =>
        {
            match (a.as_int(), a.as_float(), b.as_int(), b.as_float()) {
                _ if a == b => {
                    error = Some(Error::TrivialCast);
                    CastType::Noop
                }
                _ if a == BaseType::Pointer && b == BaseType::Pointer => CastType::Noop,
                (Some(from), _, Some(to), _) => CastType::Int { from, to },
                (Some(from), _, _, Some(to)) => CastType::IntToFloat { from, to },
                (_, Some(from), Some(to), _) => CastType::FloatToInt { from, to },
                (_, Some(from), _, Some(to)) => CastType::Float { from, to },
                (Some(from), _, _, _) if b == BaseType::Pointer => CastType::IntToPtr { from },
                (_, _, Some(to), _) if a == BaseType::Pointer => CastType::PtrToInt { to },
                _ => CastType::Invalid,
            }
        }
        (a, b) => {
            let mut a_string = String::new();
            let mut b_string = String::new();
            types.type_to_string(compiler, a, &mut a_string);
            types.type_to_string(compiler, b, &mut b_string);
            error = Some(Error::InvalidCast {
                from: a_string,
                to: b_string,
            });
            CastType::Invalid
        }
    };
    (cast, error)
}
