use id::{ModuleId, TypeId};
use span::TSpan;
use types::{Primitive, Type};

use crate::{
    compiler::{CheckedTrait, Generics},
    parser::ast::FunctionId,
    Compiler,
};

use super::{LocalTypeIds, TypeInfo, TypeInfoOrIdx, TypeTable};

pub enum Candidates<'a> {
    None,
    Multiple,
    Unique(&'a Impl),
}

#[derive(Debug, Clone, Copy)]
pub enum BaseType {
    Invalid,
    Primitive(Primitive),
    TypeId(TypeId),
    Pointer,
    Tuple,
    Array { count: u32 },
}

pub fn get_impl_candidates<'t>(
    ty: TypeInfo,
    types: &TypeTable,
    _generics: &Generics,
    checked: &'t CheckedTrait,
) -> Candidates<'t> {
    let mut found = None;
    for (i, trait_impl) in checked.impls.iter().enumerate() {
        if trait_impl.impl_ty.matches_type_info(ty, types) {
            if found.is_some() {
                return Candidates::Multiple;
            }
            found = Some(i);
        }
    }
    if let Some(found) = found {
        Candidates::Unique(&checked.impls[found])
    } else {
        Candidates::None
    }
}

#[derive(Debug)]
pub enum ImplTree {
    Any { generic: u8 },
    Base(BaseType, Box<[ImplTree]>),
}
impl ImplTree {
    pub fn from_type(ty: &Type, compiler: &mut Compiler) -> Self {
        match ty {
            Type::Invalid => Self::Base(BaseType::Invalid, Box::new([])),
            &Type::Primitive(p) => Self::Base(BaseType::Primitive(p), Box::new([])),
            Type::DefId { id, generics } => Self::Base(
                BaseType::TypeId(*id),
                generics
                    .iter()
                    .map(|g| Self::from_type(g, compiler))
                    .collect(),
            ),
            Type::Pointer(pointee) => Self::Base(
                BaseType::Pointer,
                Box::new([Self::from_type(pointee, compiler)]),
            ),
            Type::Array(b) => Self::Base(
                BaseType::Array { count: b.1 },
                Box::new([Self::from_type(&b.0, compiler)]),
            ),
            Type::Tuple(elements) => Self::Base(
                BaseType::Tuple,
                elements
                    .iter()
                    .map(|e| Self::from_type(e, compiler))
                    .collect(),
            ),
            &Type::Generic(generic) => Self::Any { generic },
            Type::LocalEnum(_) => unreachable!(),
            Type::Function(_) => todo!(),
        }
    }

    pub fn matches_type(&self, ty: &Type, impl_generics: &mut [Type]) -> bool {
        match self {
            &Self::Any { generic } => {
                impl_generics[generic as usize] = ty.clone();
                return true;
            }
            Self::Base(base_type, args) => match ty {
                Type::Invalid => return true,
                Type::Primitive(p) => {
                    if let BaseType::Primitive(base_p) = base_type {
                        return p == base_p;
                    }
                }
                Type::DefId { id, generics } => {
                    if let BaseType::TypeId(base_id) = base_type {
                        if id != base_id {
                            return false;
                        }
                        debug_assert_eq!(generics.len(), args.len());
                        for (generic, base_type) in generics.iter().zip(args.iter()) {
                            if !base_type.matches_type(generic, impl_generics) {
                                return false;
                            }
                        }
                        return true;
                    }
                }
                Type::Pointer(pointee) => {
                    if let BaseType::Pointer = base_type {
                        return args[0].matches_type(pointee, impl_generics);
                    }
                }
                Type::Tuple(elems) => {
                    let BaseType::Tuple = base_type else {
                        return false;
                    };
                    if args.len() != elems.len() {
                        return false;
                    }
                    for (elem, base_type) in elems.iter().zip(args) {
                        if !base_type.matches_type(elem, impl_generics) {
                            return false;
                        }
                    }
                    return true;
                }
                Type::Array(b) => {
                    let (elem, count) = &**b;
                    let &BaseType::Array { count: base_count } = base_type else {
                        return false;
                    };
                    if *count != base_count {
                        return false;
                    }
                    args[0].matches_type(elem, impl_generics);
                }
                Type::Generic(_) | Type::LocalEnum(_) => return false,
                Type::Function(_) => return false,
            },
        }
        false
    }

    pub fn matches_type_info(&self, ty: TypeInfo, types: &TypeTable) -> bool {
        match self {
            Self::Any { .. } => true,
            Self::Base(base_type, args) => {
                // TODO: pass info about which type doesn't implement a trait on error
                match ty {
                    TypeInfo::Invalid | TypeInfo::Unknown => true,
                    TypeInfo::UnknownSatisfying { .. } => todo!("handle multiple requirements"),
                    TypeInfo::Primitive(p) => {
                        let &BaseType::Primitive(base_p) = base_type else {
                            return false;
                        };
                        p == base_p
                    }
                    TypeInfo::TypeDef(id, def_generics) => {
                        let &BaseType::TypeId(base_id) = base_type else {
                            return false;
                        };
                        if id != base_id {
                            return false;
                        }
                        debug_assert_eq!(def_generics.count as usize, args.len());
                        for (arg, impl_tree) in def_generics.iter().zip(args) {
                            if !impl_tree.matches_type_info(types[arg], types) {
                                return false;
                            }
                        }
                        true
                    }
                    TypeInfo::Pointer(pointee) => {
                        if !matches!(base_type, BaseType::Pointer) {
                            return false;
                        }
                        let [pointee_tree] = &**args else {
                            unreachable!()
                        };
                        pointee_tree.matches_type_info(types[pointee], types)
                    }
                    TypeInfo::Tuple(elems) => {
                        if !matches!(base_type, BaseType::Tuple)
                            || args.len() != elems.count as usize
                        {
                            return false;
                        }
                        for (arg, impl_tree) in elems.iter().zip(args) {
                            if !impl_tree.matches_type_info(types[arg], types) {
                                return false;
                            }
                        }
                        true
                    }
                    TypeInfo::Array { element, count } => {
                        let &BaseType::Array { count: base_count } = base_type else {
                            return false;
                        };
                        if count.is_some_and(|count| count != base_count) {
                            return false;
                        }
                        let [elem_tree] = &**args else { unreachable!() };
                        elem_tree.matches_type_info(types[element], types)
                    }
                    TypeInfo::Enum(_) => false, // TODO: auto impl some traits for local enums
                    TypeInfo::Integer => matches!(base_type, BaseType::Primitive(p) if p.is_int()),
                    TypeInfo::Float => matches!(base_type, BaseType::Primitive(p) if p.is_float()),
                    TypeInfo::Generic(_)
                    | TypeInfo::TypeItem { .. }
                    | TypeInfo::TraitItem { .. }
                    | TypeInfo::FunctionItem { .. }
                    | TypeInfo::ModuleItem { .. }
                    | TypeInfo::MethodItem { .. }
                    | TypeInfo::TraitMethodItem { .. }
                    | TypeInfo::EnumVariantItem { .. } => false,
                }
            }
        }
    }

    pub fn instantiate(&self, impl_generics: LocalTypeIds, types: &mut TypeTable) -> TypeInfoOrIdx {
        match self {
            &Self::Any { generic } => {
                TypeInfoOrIdx::Idx(impl_generics.nth(generic.into()).unwrap())
            }
            Self::Base(base, args) => TypeInfoOrIdx::TypeInfo(match *base {
                BaseType::Invalid => TypeInfo::Invalid,
                BaseType::Primitive(p) => TypeInfo::Primitive(p),
                BaseType::TypeId(id) => {
                    let generic_infos = types.add_multiple_unknown(args.len() as _);
                    for (tree, r) in args.iter().zip(generic_infos.iter()) {
                        let info_or_idx = tree.instantiate(impl_generics, types);
                        types.replace(r, info_or_idx);
                    }
                    TypeInfo::TypeDef(id, generic_infos)
                }
                BaseType::Pointer => {
                    let pointee = args[0].instantiate(impl_generics, types);
                    TypeInfo::Pointer(types.add_info_or_idx(pointee))
                }
                BaseType::Tuple => {
                    let elems = types.add_multiple_unknown(args.len() as _);
                    for (arg, r) in args.iter().zip(elems.iter()) {
                        let info = arg.instantiate(impl_generics, types);
                        types.replace(r, info);
                    }
                    TypeInfo::Tuple(elems)
                }
                BaseType::Array { count } => {
                    let [elem_ty] = &**args else { unreachable!() };
                    let elem = elem_ty.instantiate(impl_generics, types);

                    TypeInfo::Array {
                        element: types.add_info_or_idx(elem),
                        count: Some(count),
                    }
                }
            }),
        }
    }
}

#[derive(Debug)]
pub struct Impl {
    pub generics: Generics,
    pub impl_ty: ImplTree,
    pub impl_module: ModuleId,
    pub functions: Vec<FunctionId>,
}
impl Impl {
    /// returns the instantiated impl_ty and the impl_generics
    pub fn instantiate(
        &self,
        trait_generics: LocalTypeIds,
        types: &mut TypeTable,
        span: TSpan,
    ) -> TypeInfoOrIdx {
        assert_eq!(trait_generics.count, 0, "TODO: handle generic traits");
        let impl_generics = self.generics.instantiate(types, span);
        let impl_ty = self.impl_ty.instantiate(impl_generics, types);
        impl_ty
    }
}
