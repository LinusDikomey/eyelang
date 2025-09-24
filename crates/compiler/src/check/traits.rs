use dmap::DHashMap;
use error::Error;
use error::span::TSpan;
use parser::ast::{self, Ast, TraitId};
use parser::ast::{FunctionId, ModuleId};

use super::{LocalTypeIds, TypeInfo, TypeInfoOrIdx, TypeTable};

use crate::helpers::IteratorExt;
use crate::types::{BaseType, TypeFull, Types};
use crate::{
    Compiler,
    compiler::Signature,
    compiler::{CheckedTrait, Generics},
    typing::Bound,
};
use crate::{InvalidTypeError, Type};

pub fn trait_def(compiler: &Compiler, ast: &Ast, id: (ModuleId, TraitId)) -> CheckedTrait {
    let module = id.0;
    let def = &ast[id.1];
    // don't include self type in generics, it is handled seperately
    let generics = compiler.resolve_generics(&def.generics.types[1..], id.0, def.scope, &ast);
    let mut functions_by_name = dmap::with_capacity(def.functions.len());
    let functions: Vec<Signature> = def
        .functions
        .iter()
        .zip(0..)
        .map(|(function, function_index)| {
            let name = ast[function.name].to_owned();
            let prev = functions_by_name.insert(name, function_index);
            if prev.is_some() {
                compiler
                    .errors
                    .emit(module, Error::DuplicateDefinition.at_span(function.name));
            }
            compiler.check_signature(&ast[function.function], module, &ast)
        })
        .collect();
    let impls = def
        .impls
        .iter()
        .filter_map(|impl_| {
            let impl_ty = compiler.resolve_type(&impl_.implemented_type, module, impl_.base.scope);
            check_impl(
                compiler,
                &impl_.base,
                impl_ty,
                module,
                &ast,
                generics.count(),
                &functions,
                &functions_by_name,
                &ast.src()[def.associated_name.range()],
            )
        })
        .collect();
    CheckedTrait {
        name: if def.associated_name == TSpan::MISSING {
            "<unnamed trait>".into()
        } else {
            ast[def.associated_name].into()
        },
        generics,
        functions,
        functions_by_name,
        impls,
    }
}

pub fn check_impl(
    compiler: &Compiler,
    impl_: &ast::BaseImpl,
    impl_ty: Type,
    module: ModuleId,
    ast: &Ast,
    trait_generic_count: u8,
    trait_functions: &[Signature],
    trait_functions_by_name: &DHashMap<String, u16>,
    trait_name: &str,
) -> Option<Impl> {
    let impl_generics = compiler.resolve_generics(&impl_.generics.types, module, impl_.scope, ast);

    let trait_generics: Vec<_> = impl_
        .trait_generics
        .iter()
        .map(|generic| compiler.resolve_type(generic, module, impl_.scope))
        .collect();

    if trait_generics.len() as u8 != trait_generic_count {
        compiler.errors.emit(
            module,
            Error::InvalidGenericCount {
                expected: trait_generic_count,
                found: trait_generics.len() as _,
            }
            .at_span(impl_.trait_generics_span),
        );
        return None;
    }

    let mut function_ids = vec![ast::FunctionId::from_inner(u32::MAX); trait_functions.len()];
    let base_generics: Box<[Type]> = std::iter::once(impl_ty.clone())
        .chain(trait_generics.clone())
        .collect();
    let base_offset = base_generics.len() as u8;
    for method in &impl_.functions {
        let name = &ast[method.name];
        let Some(&function_idx) = trait_functions_by_name.get(name) else {
            compiler.errors.emit(
                module,
                Error::NotATraitMember {
                    trait_name: trait_name.to_owned(),
                    function: name.to_owned(),
                }
                .at_span(method.name),
            );
            continue;
        };
        if function_ids[function_idx as usize] != ast::FunctionId::from_inner(u32::MAX) {
            compiler
                .errors
                .emit(module, Error::DuplicateDefinition.at_span(method.name));
            continue;
        }

        let signature = compiler.get_signature(module, method.function);
        let trait_signature = &trait_functions[function_idx as usize];
        let compatible = signature.compatible_with(
            &compiler.types,
            trait_signature,
            impl_generics.count(),
            base_offset,
            &base_generics,
        );
        match compatible {
            Ok(None) | Err(InvalidTypeError) => {}
            Ok(Some(incompat)) => compiler.errors.emit(
                module,
                Error::TraitSignatureMismatch(incompat).at_span(method.name),
            ),
        }
        function_ids[function_idx as usize] = method.function;
    }
    let mut unimplemented = Vec::new();
    for (name, &i) in trait_functions_by_name {
        if function_ids[i as usize] == ast::FunctionId::from_inner(u32::MAX) {
            unimplemented.push(name.clone());
        }
    }
    if !unimplemented.is_empty() {
        compiler.errors.emit(
            module,
            Error::NotAllFunctionsImplemented { unimplemented }.at_span(ast[impl_.scope].span),
        );
    }
    Some(Impl {
        generics: impl_generics,
        trait_generics,
        impl_ty,
        impl_module: module,
        functions: function_ids,
    })
}

#[derive(Debug)]
pub enum Candidates {
    None,
    Invalid,
    Multiple,
    Unique { instance: TypeInfoOrIdx },
}

pub fn get_impl_candidates(
    compiler: &Compiler,
    bound: &Bound,
    ty: TypeInfo,
    types: &mut TypeTable,
    function_generics: &Generics,
) -> Candidates {
    let Some(checked_trait) = compiler.get_checked_trait(bound.trait_id.0, bound.trait_id.1) else {
        return Candidates::Invalid;
    };
    let mut found = None;
    let resolved;
    match ty {
        TypeInfo::Unknown(_) => return Candidates::Multiple,
        TypeInfo::Instance(base, _) => {
            resolved = compiler.get_base_type_def(base);
            let impls_for_ty = resolved
                .inherent_trait_impls
                .get(&bound.trait_id)
                .map_or(&[] as &[Impl], |v| v.as_slice());
            for impl_ in impls_for_ty {
                match is_candidate_valid(&compiler.types, impl_, bound.generics, ty, types) {
                    Ok(true) => {
                        if found.is_some() {
                            return Candidates::Multiple;
                        }
                        found = Some(impl_);
                    }
                    Ok(false) => {}
                    Err(InvalidTypeError) => return Candidates::Invalid,
                }
            }
        }
        TypeInfo::Generic(i) => {
            let mut compatible_bound = None;
            for generic_bound in function_generics.get_bounds(i) {
                if generic_bound.trait_id != bound.trait_id {
                    continue;
                }

                debug_assert_eq!(generic_bound.generics.len(), bound.generics.count as usize);
                let Ok(compatible) = generic_bound
                    .generics
                    .iter()
                    .zip(bound.generics.iter())
                    .try_all(|(&ty, idx)| {
                        types.compatible_with_type(&compiler.types, types[idx], ty)
                    })
                else {
                    return Candidates::Invalid;
                };
                if compatible {
                    if compatible_bound.is_some() {
                        return Candidates::Multiple;
                    }
                    compatible_bound = Some(generic_bound);
                }
            }
            if let Some(generic_bound) = compatible_bound {
                for (&ty, idx) in generic_bound.generics.iter().zip(bound.generics.iter()) {
                    // type was checked to be compatible so should be safe to replace
                    types.replace_value(idx, TypeInfo::Known(ty));
                }
                return Candidates::Unique {
                    instance: ty.into(),
                };
            }
        }
        _ => {} // type doesn't have inherent impls
    };
    for impl_ in &checked_trait.impls {
        match is_candidate_valid(&compiler.types, impl_, bound.generics, ty, types) {
            Ok(true) => {
                if found.is_some() {
                    return Candidates::Multiple;
                }
                found = Some(impl_);
            }
            Ok(false) => {}
            Err(InvalidTypeError) => return Candidates::Invalid,
        }
    }
    if let Some(found) = found {
        Candidates::Unique {
            instance: found.instantiate(
                bound.generics,
                function_generics,
                types,
                compiler,
                bound.span,
            ),
        }
    } else {
        Candidates::None
    }
}

fn is_candidate_valid(
    types: &Types,
    impl_: &Impl,
    trait_generics: LocalTypeIds,
    info: TypeInfo,
    table: &TypeTable,
) -> Result<bool, InvalidTypeError> {
    debug_assert_eq!(trait_generics.count, impl_.trait_generics.len() as u32);
    Ok(trait_generics
        .iter()
        .zip(&impl_.trait_generics)
        .try_all(|(idx, &ty)| table.compatible_with_type(types, table[idx], ty))?
        && matches_type_info(impl_.impl_ty, info, types, table))
}

pub fn match_instance(
    implemented_ty: Type,
    ty: Type,
    types: &Types,
    instance: &mut [Type],
) -> bool {
    match types.lookup(implemented_ty) {
        TypeFull::Generic(i) => {
            let instance_ty = &mut instance[usize::from(i)];
            if *instance_ty != Type::Invalid && *instance_ty != ty {
                return false;
            }
            *instance_ty = ty;
            true
        }
        TypeFull::Instance(implemented_base, implemented_generics) => match types.lookup(ty) {
            TypeFull::Instance(BaseType::Invalid, _) => return true,
            TypeFull::Instance(base, generics) => {
                if base != implemented_base {
                    return false;
                }
                if generics.len() != implemented_generics.len() {
                    return false;
                }
                for (&generic, &implemented_generic) in
                    generics.iter().zip(implemented_generics.iter())
                {
                    if !match_instance(implemented_generic, generic, types, instance) {
                        return false;
                    }
                }
                return true;
            }
            TypeFull::Generic(_) | TypeFull::Const(_) => return false,
        },
        TypeFull::Const(implemented_n) => {
            let TypeFull::Const(n) = types.lookup(ty) else {
                return false;
            };
            implemented_n == n
        }
    }
}

fn matches_type_info(
    _implemented_ty: Type,
    _info: TypeInfo,
    _types: &Types,
    _table: &TypeTable,
    // instance: LocalTypeIds,
) -> bool {
    // TODO: the problem is that we want to update the instance like in the method above
    // so that generics mentioned multiple times unify correctly. This is however a destructive
    // action (unification on input types) which will invalidate all the mismatched types on match
    // failure (which is just supposed to be a check). So maybe a method like can_unify(a, b) is needed
    // that doesn't modify the type table at all
    todo!("match impls again")
    /*
    match types.lookup(implemented_ty) {
        TypeFull::Generic(i) => {
            table.unify(, instance.nth(i.into()).unwrap(), generics, compiler, span);
        }
        Self::Base(impl_base, args) => {
            // TODO: pass info about which type doesn't implement a trait on error
            match implemented_ty {
                TypeInfo::Instance(BaseType::Invalid, _) => true,
                TypeInfo::Known(ty) => self.matches_type(types, ty, &mut []),
                TypeInfo::Unknown(bounds) => {
                    if !bounds.is_empty() {
                        todo!("handle multiple requirements")
                    }
                    true
                }
                TypeInfo::UnknownConst => todo!("error"),
                TypeInfo::Integer => impl_base.is_int(),
                TypeInfo::Float => impl_base.is_float(),
                TypeInfo::Instance(base, def_generics) => {
                    if *impl_base != base {
                        return false;
                    }
                    if def_generics.count as usize != args.len() {
                        return false;
                    }
                    for (arg, impl_tree) in def_generics.iter().zip(args) {
                        if !impl_tree.matches_type_info(types, table[arg], table) {
                            return false;
                        }
                    }
                    true
                }
                TypeInfo::Enum(_) => false, // TODO: auto impl some traits for local enums
                TypeInfo::Generic(_)
                | TypeInfo::BaseTypeItem { .. }
                | TypeInfo::TypeItem(_)
                | TypeInfo::TraitItem { .. }
                | TypeInfo::FunctionItem { .. }
                | TypeInfo::ModuleItem { .. }
                | TypeInfo::MethodItem { .. }
                | TypeInfo::TraitMethodItem { .. }
                | TypeInfo::EnumVariantItem { .. } => false,
            }
        }
    }
    */
}

#[derive(Debug)]
pub struct Impl {
    pub generics: Generics,
    pub trait_generics: Vec<Type>,
    pub impl_ty: Type,
    pub impl_module: ModuleId,
    pub functions: Vec<FunctionId>,
}
impl Impl {
    /// returns the instantiated impl_ty and the impl_generics
    pub fn instantiate(
        &self,
        trait_generics: LocalTypeIds,
        function_generics: &Generics,
        types: &mut TypeTable,
        compiler: &Compiler,
        span: TSpan,
    ) -> TypeInfoOrIdx {
        let impl_generics = self.generics.instantiate(types, span);
        debug_assert_eq!(trait_generics.count, self.trait_generics.len() as u32);
        for (idx, &ty) in trait_generics.iter().zip(&self.trait_generics) {
            types.specify_type_instance(
                idx,
                ty,
                impl_generics,
                function_generics,
                compiler,
                // span should never be needed since the requirements should have already been
                // checked so no errors should occur
                || unreachable!(),
            );
        }
        types.from_type_instance(&compiler.types, self.impl_ty, impl_generics)
    }
}
