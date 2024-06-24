use std::rc::Rc;

use crate::{
    check::expr::int_ty_from_variant_count,
    compiler::ResolvedTypeDef,
    types::{traits, TypeInfoOrIdx},
    Compiler,
};

use super::{TypeInfo, TypeTable};

pub fn unify(
    a: TypeInfo,
    b: TypeInfo,
    types: &mut TypeTable,
    compiler: &mut Compiler,
) -> Option<TypeInfo> {
    use types::Primitive as P;
    use TypeInfo::*;
    Some(match (a, b) {
        (t, Unknown | Primitive(P::Never)) | (Unknown | Primitive(P::Never), t) => t,
        (
            t,
            UnknownSatisfying {
                id: trait_id,
                generics,
            },
        )
        | (
            UnknownSatisfying {
                id: trait_id,
                generics,
            },
            t,
        ) => {
            let self_ty = generics.nth(0).unwrap();
            if types.try_specify(self_ty, t, compiler).is_err() {
                return None;
            }
            let Some(checked_trait) = compiler.get_checked_trait(trait_id.0, trait_id.1) else {
                return Some(TypeInfo::Invalid);
            };
            let candidates = traits::get_impl_candidates(types[self_ty], types, &*checked_trait);
            match candidates {
                traits::Candidates::None => return None, // TODO: better errors
                traits::Candidates::Multiple => {
                    eprintln!("TODO: defer trait impl check");
                    // self.defer_impl_check((module, trait_id), );
                    t
                }
                traits::Candidates::Unique(trait_impl) => {
                    eprintln!("CHOSE IMPL: {trait_impl:?}");
                    let impl_generics = types.add_multiple_unknown(trait_impl.generic_count.into());
                    let info_or_idx = trait_impl.instantiate(generics, impl_generics, types);
                    // TODO: probably handles generics completely incorrectly
                    types.get_info_or_idx(info_or_idx)
                }
            }
        }
        (Primitive(p_a), Primitive(p_b)) if p_a == p_b => a,
        (Invalid, _) | (_, Invalid) => Invalid,
        (Integer, Integer) => Integer,
        (Float, Float) => Float,
        (Primitive(t), Integer) | (Integer, Primitive(t)) if t.is_int() => Primitive(t),
        (Primitive(t), Float) | (Float, Primitive(t)) if t.is_float() => Primitive(t),
        (TypeDef(id_a, generics_a), TypeDef(id_b, generics_b)) if id_a == id_b => {
            debug_assert_eq!(generics_a.count, generics_b.count);
            for (a, b) in generics_a.iter().zip(generics_b.iter()) {
                if !types.try_unify(a, b, compiler) {
                    return None;
                }
            }
            a
        }
        (TypeDef(id, generics), Enum(enum_id)) | (Enum(enum_id), TypeDef(id, generics)) => {
            let ty = compiler.get_resolved_type_def(id);
            let def = Rc::clone(&ty.def);
            let ResolvedTypeDef::Enum(def) = &*def else {
                return None;
            };
            let variants = &types.enums[enum_id.idx()];
            if let Some(&first_variant) = variants.variants.first() {
                let ordinal_type = types[first_variant].args.iter().next().unwrap();
                debug_assert!(matches!(
                    types.types[ordinal_type.idx()],
                    TypeInfoOrIdx::TypeInfo(_)
                ));
                types.types[ordinal_type.idx()] =
                    TypeInfoOrIdx::TypeInfo(int_ty_from_variant_count(def.variants.len() as u32));
            }
            // iterate by index because we need to borrow types mutably during the loop
            for variant_index in 0..variants.variants.len() {
                let variant = types.enums[enum_id.idx()].variants[variant_index];
                let variant = &mut types.variants[variant.idx()];
                // TODO: make it possible to return specific errors here so it's more clear when an
                // enum doesn't match a definition
                let Some((declared_ordinal, declared_args)) = def.get_by_name(&variant.name) else {
                    eprintln!("enum variant {} not found", variant.name);
                    return None;
                };
                variant.ordinal = declared_ordinal;
                // add one because the inferred enum args contain the ordinal type
                if variant.args.count != declared_args.len() as u32 + 1 {
                    return None;
                }
                for (arg, declared_arg) in variant.args.iter().skip(1).zip(declared_args) {
                    if types
                        .try_specify_resolved(arg, declared_arg, generics, compiler)
                        .is_err()
                    {
                        return None;
                    }
                }
            }
            TypeInfo::TypeDef(id, generics)
        }
        (Enum(a), Enum(b)) => {
            _ = (a, b);
            todo!("unify enums")
        }
        (Pointer(a), Pointer(b)) => {
            if !types.try_unify(a, b, compiler) {
                return None;
            }
            Pointer(a)
        }
        (
            Array {
                element: a,
                count: c_a,
            },
            Array {
                element: b,
                count: c_b,
            },
        ) => {
            if !types.try_unify(a, b, compiler) {
                return None;
            }
            let count = match (c_a, c_b) {
                (Some(c), None) | (None, Some(c)) => Some(c),
                (None, None) => None,
                (Some(a), Some(b)) => {
                    if a == b {
                        Some(a)
                    } else {
                        return None;
                    }
                }
            };
            Array { element: a, count }
        }
        (Tuple(a), Tuple(b)) => {
            // TODO: reintroduce tuple count mode
            if a.count != b.count {
                return None;
            }
            for (a, b) in a.iter().zip(b.iter()) {
                if !types.try_unify(a, b, compiler) {
                    return None;
                }
            }
            Tuple(a)
        }
        (TypeItem { ty: a_ty }, TypeItem { ty: b_ty }) => {
            if !types.try_unify(a_ty, b_ty, compiler) {
                return None;
            }
            a
        }
        (
            FunctionItem {
                module: a_m,
                function: a_f,
                generics: a_g,
            },
            FunctionItem {
                module: b_m,
                function: b_f,
                generics: b_g,
            },
        ) if a_m == b_m && a_f == b_f => {
            debug_assert_eq!(
                a_g.count, b_g.count,
                "invalid generics count, incorrect type info constructed"
            );
            for (a, b) in a_g.iter().zip(b_g.iter()) {
                if !types.try_unify(a, b, compiler) {
                    return None;
                }
            }
            a
        }
        (
            MethodItem {
                module: a_m,
                function: a_f,
                generics: a_g,
            },
            MethodItem {
                module: b_m,
                function: b_f,
                generics: b_g,
            },
        ) if a_m == b_m && a_f == b_f => {
            for (a, b) in a_g.iter().zip(b_g.iter()) {
                types.try_unify(a, b, compiler);
            }
            a
        }
        (Generic(a), Generic(b)) if a == b => Generic(a),
        _ => return None,
    })
}
