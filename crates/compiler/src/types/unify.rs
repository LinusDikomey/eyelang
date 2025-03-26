use std::rc::Rc;

use crate::{
    Compiler,
    check::expr::int_ty_from_variant_count,
    compiler::{Generics, ResolvedTypeContent},
    types::{TypeInfoOrIdx, traits},
};

use super::{LocalTypeId, TypeInfo, TypeTable};

pub fn unify(
    a: TypeInfo,
    b: TypeInfo,
    types: &mut TypeTable,
    function_generics: &Generics,
    compiler: &mut Compiler,
    unified_id: LocalTypeId,
) -> Option<TypeInfo> {
    use TypeInfo::*;
    use types::Primitive as P;
    Some(match (a, b) {
        (t, Unknown | Primitive(P::Never)) | (Unknown | Primitive(P::Never), t) => t,
        (UnknownSatisfying(bounds), Generic(generic_id))
        | (Generic(generic_id), UnknownSatisfying(bounds)) => {
            for bound in bounds.iter() {
                let bound = *types.get_bound(bound);
                if !function_generics.unify_generic_bound(generic_id, &bound, types, compiler) {
                    // TODO: more specific error message with missing trait bound
                    return None;
                }
            }
            Generic(generic_id)
        }
        (UnknownSatisfying(a), UnknownSatisfying(b)) => {
            // TODO: this might not work and it might be much better to unify duplicate traits
            // PERF: avoid the vec and allocate into new bounds instead
            let mut bounds = types.get_bounds(a).to_vec();
            bounds.extend_from_slice(types.get_bounds(b));
            UnknownSatisfying(types.add_bounds(bounds))
        }
        (t, UnknownSatisfying(bounds)) | (UnknownSatisfying(bounds), t) => {
            let mut chosen_ty = t;
            for bound in bounds.iter() {
                let bound = *types.get_bound(bound);
                let Some(checked_trait) =
                    compiler.get_checked_trait(bound.trait_id.0, bound.trait_id.1)
                else {
                    return Some(TypeInfo::Invalid);
                };
                let checked_trait = Rc::clone(checked_trait);
                let mut s = String::new();
                types.type_to_string(compiler, chosen_ty, &mut s);
                let candidates = traits::get_impl_candidates(
                    chosen_ty,
                    bound.generics,
                    types,
                    function_generics,
                    &checked_trait,
                );
                match candidates {
                    traits::Candidates::None => return None, // TODO: better errors
                    traits::Candidates::Multiple => {
                        // TODO: might emit multiple checks since this path happens when a single
                        // bound is not fulfilled but will check all bounds again
                        types.defer_impl_check(unified_id, bounds);
                    }
                    traits::Candidates::Unique(trait_impl) => {
                        let self_ty = trait_impl.instantiate(
                            bound.generics,
                            function_generics,
                            types,
                            compiler,
                            bound.span,
                        );
                        match self_ty {
                            TypeInfoOrIdx::TypeInfo(info) => {
                                chosen_ty = unify(
                                    chosen_ty,
                                    info,
                                    types,
                                    function_generics,
                                    compiler,
                                    unified_id,
                                )?;
                            }
                            TypeInfoOrIdx::Idx(idx) => {
                                types
                                    .try_specify(idx, chosen_ty, function_generics, compiler)
                                    .ok()?;
                                chosen_ty = types[idx];
                                types.replace(idx, TypeInfoOrIdx::Idx(unified_id));
                            }
                        }
                    }
                }
            }
            chosen_ty
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
                if !types.try_unify(a, b, function_generics, compiler) {
                    return None;
                }
            }
            a
        }
        (TypeDef(id, generics), Enum(enum_id)) | (Enum(enum_id), TypeDef(id, generics)) => {
            let resolved = Rc::clone(compiler.get_resolved_type_def(id));
            let ResolvedTypeContent::Enum(def) = &resolved.def else {
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
                        .try_specify_resolved(
                            arg,
                            declared_arg,
                            generics,
                            function_generics,
                            compiler,
                        )
                        .is_err()
                    {
                        return None;
                    }
                }
            }
            TypeInfo::TypeDef(id, generics)
        }
        (Enum(a), Enum(b)) => {
            // always merge into a_variants which becomes the longer variant list to try to avoid
            // having to create new variants if one list is a subset of the other
            let (a, b) = if types.get_enum_variants(a).len() >= types.get_enum_variants(b).len() {
                (a, b)
            } else {
                (b, a)
            };
            let Some(&first_a) = types.get_enum_variants(a).first() else {
                // if a is empty, both enums are empty and just returning one is fine
                return Some(TypeInfo::Enum(a));
            };
            let ordinal_type_idx = types[first_a].args.idx;
            let b_variant_count = types.get_enum_variants(b).len();
            for i in 0..b_variant_count {
                let b_variants = types.get_enum_variants(b);
                debug_assert_eq!(
                    b_variants.len(),
                    b_variant_count,
                    "b_variant_count shouldn't change"
                );
                let b_id = b_variants[i];
                let a_variants = types.get_enum_variants(a);
                let variant = &types[b_id];
                let a_variant = a_variants
                    .iter()
                    .copied()
                    .find(|&id| types[id].name == variant.name);
                if let Some(a_variant) = a_variant {
                    let a_variant = &types[a_variant];
                    let ordinal = a_variant.ordinal;
                    // TODO: better errors
                    if a_variant.args.count != variant.args.count {
                        return None;
                    }
                    let a_args = a_variant.args;
                    let b_args = variant.args;
                    if !a_args
                        .iter()
                        .zip(b_args.iter())
                        .skip(1) // skip the ordinal argument
                        .all(|(a, b)| types.try_unify(a, b, function_generics, compiler))
                    {
                        return None;
                    }
                    types[b_id].ordinal = ordinal;
                    types.types[b_args.idx as usize] =
                        TypeInfoOrIdx::Idx(LocalTypeId(ordinal_type_idx));
                } else {
                    let a_id = types.append_enum_variant(a, variant.name.clone(), variant.args);
                    let ordinal = types[a_id].ordinal;
                    types[b_id].ordinal = ordinal;
                }
            }
            TypeInfo::Enum(a)
        }
        (Pointer(a), Pointer(b)) => {
            if !types.try_unify(a, b, function_generics, compiler) {
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
            if !types.try_unify(a, b, function_generics, compiler) {
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
                if !types.try_unify(a, b, function_generics, compiler) {
                    return None;
                }
            }
            Tuple(a)
        }
        (
            Function {
                params: a_params,
                return_type: a_ret,
            },
            Function {
                params: b_params,
                return_type: b_ret,
            },
        ) => {
            if a_params.count != b_params.count {
                return None;
            }
            if !a_params
                .iter()
                .zip(b_params.iter())
                .all(|(a, b)| types.try_unify(a, b, function_generics, compiler))
                && types.try_unify(a_ret, b_ret, function_generics, compiler)
            {
                return None;
            }
            a
        }
        (
            FunctionItem {
                module,
                function,
                generics,
            },
            func @ Function {
                params,
                return_type,
            },
        )
        | (
            func @ Function {
                params,
                return_type,
            },
            FunctionItem {
                module,
                function,
                generics,
            },
        ) => {
            // TODO: make sure the function item is actually of the correct type
            _ = (module, function, generics, params, return_type);
            func
        }
        (TypeItem { ty: a_ty }, TypeItem { ty: b_ty }) => {
            if !types.try_unify(a_ty, b_ty, function_generics, compiler) {
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
        ) => {
            if a_m == b_m && a_f == b_f {
                debug_assert_eq!(
                    a_g.count, b_g.count,
                    "invalid generics count, incorrect type info constructed"
                );
                for (a, b) in a_g.iter().zip(b_g.iter()) {
                    if !types.try_unify(a, b, function_generics, compiler) {
                        return None;
                    }
                }
                a
            } else {
                todo!("unify different function items")
            }
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
                types.try_unify(a, b, function_generics, compiler);
            }
            a
        }
        (Generic(a), Generic(b)) if a == b => Generic(a),
        _ => return None,
    })
}
