use std::rc::Rc;

use dmap::DHashMap;
use error::Error;
use id::{ModuleId, TypeId};
use parser::ast::{self, TraitId};
use types::Type;

use crate::{
    Compiler, Def,
    compiler::{ResolvedEnumDef, ResolvedStructDef, ResolvedTypeContent, ResolvedTypeDef},
};

use super::traits;

pub fn type_def(compiler: &mut Compiler, ty: TypeId) -> ResolvedTypeDef {
    let resolved_ty = &compiler.types[ty.idx()];
    let module = resolved_ty.module;
    let ast_id = resolved_ty.id;
    let ast = Rc::clone(compiler.get_module_ast(module));
    let def = &ast[ast_id];
    let generics = compiler.resolve_generics(&def.generics, module, def.scope, &ast);
    let resolved_def = match &def.content {
        ast::TypeContent::Struct { members } => {
            let named_fields = members
                .iter()
                .map(|member| {
                    (
                        ast[member.name].into(),
                        compiler.resolve_type(&member.ty, module, def.scope),
                        None,
                    )
                })
                .collect();
            ResolvedTypeContent::Struct(ResolvedStructDef {
                fields: Box::new([]),
                named_fields,
            })
        }
        ast::TypeContent::Enum { variants } => {
            let variants = variants
                .iter()
                .map(|variant| {
                    let variant_name = ast[variant.name_span].to_owned();
                    let args = variant
                        .args
                        .iter()
                        .map(|ty| compiler.resolve_type(ty, module, def.scope))
                        .collect();
                    (variant_name, args)
                })
                .collect();

            ResolvedTypeContent::Enum(ResolvedEnumDef { variants })
        }
    };

    let mut methods = def.methods.clone();

    let mut inherent_trait_impls: DHashMap<(ModuleId, TraitId), Vec<traits::Impl>> = dmap::new();

    let implemented_ty = Type::DefId {
        id: ty,
        generics: (0..generics.count()).map(Type::Generic).collect(),
    };
    for trait_impl in &def.impls {
        let trait_def = compiler.resolve_path(module, def.scope, trait_impl.implemented_trait);
        let trait_id = match trait_def {
            Def::Trait(module, id) => (module, id),
            Def::Invalid => continue,
            _ => {
                compiler.errors.emit_err(
                    Error::TraitExpected
                        .at_span(trait_impl.implemented_trait.span().in_mod(module)),
                );
                continue;
            }
        };
        let Some(checked_trait) = compiler.get_checked_trait(trait_id.0, trait_id.1) else {
            // can't check trait impl because the trait was invalid
            continue;
        };
        let checked_trait = Rc::clone(checked_trait);
        let checked_impl = traits::check_impl(
            compiler,
            &trait_impl.base,
            &implemented_ty,
            module,
            &ast,
            checked_trait.generics.count(),
            &checked_trait.functions,
            &checked_trait.functions_by_name,
            &checked_trait.name,
        );
        if let Some(checked) = checked_impl {
            debug_assert_eq!(
                checked_trait.functions_by_name.len(),
                checked.functions.len()
            );
            for (name, &idx) in &checked_trait.functions_by_name {
                let id = checked.functions[idx as usize];
                let prev = methods.insert(name.to_owned(), id);
                if prev.is_some() {
                    // duplicate function, find the correct function in the impl functions for the span
                    let span = trait_impl
                        .base
                        .functions
                        .iter()
                        .find_map(|&(span, other_id)| (other_id == id).then_some(span))
                        .unwrap();
                    compiler
                        .errors
                        .emit_err(Error::DuplicateDefinition.at_span(span.in_mod(module)));
                }
            }
            inherent_trait_impls
                .entry(trait_id)
                .or_default()
                .push(checked);
        }
    }
    ResolvedTypeDef {
        def: resolved_def,
        module,
        methods,
        generics,
        inherent_trait_impls,
    }
}
