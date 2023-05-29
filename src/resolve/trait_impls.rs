use crate::{dmap::{DHashMap, self}, ast::{TypeId, TraitId, self}, types::Primitive};

use super::types::{Type, SymbolTable};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum GenericType {
    Id(TypeId),
    Primitive(Primitive),
}

#[derive(Debug)]
pub struct ResolvedTraitImpl {
    pub trait_id: TraitId,
    pub impl_generic_count: u8,
    pub trait_generics: Vec<Type>,
    pub type_generics: Vec<Type>,
    pub functions: Vec<ast::FunctionId>,
}


#[derive(Debug)]
pub struct TraitImpls {
    by_type: DHashMap<GenericType, Vec<ResolvedTraitImpl>>,
}
impl TraitImpls {
    pub fn new() -> Self {
        Self {
            by_type: dmap::new(),
        }
    }

    pub fn add_impl(&mut self, impl_ty: GenericType, resolved_impl: ResolvedTraitImpl) {
        self.by_type.entry(impl_ty).or_default().push(resolved_impl);
    }

    pub fn from_type(&self, symbols: &SymbolTable, ty: GenericType, function_name: &str) -> TraitMethodResult {
        let Some(impls) = self.by_type.get(&ty) else { return TraitMethodResult::None };
        for trait_impl in impls {
            let trait_def = symbols.get_trait(trait_impl.trait_id);
            if let Some((func_index, trait_def_func_header)) = trait_def.functions.get(function_name) {
                return TraitMethodResult::Found {
                    func: trait_impl.functions[*func_index as usize],
                    impl_generic_count: trait_impl.impl_generic_count,
                };
            }
        }
        TraitMethodResult::None
    }
}

pub enum TraitMethodResult {
    Found {
        func: ast::FunctionId,
        impl_generic_count: u8,
    },
    Multiple,
    None,
}
