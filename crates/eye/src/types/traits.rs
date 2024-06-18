use id::{ModuleId, TypeId};
use types::{Primitive, Type};

use crate::{compiler::CheckedTrait, error::Error, parser::ast::FunctionId, Compiler};

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
    checked: &'t CheckedTrait,
) -> Candidates<'t> {
    eprintln!("getting impls for {:?}: {checked:?}", ty);
    let mut maybe_count = 0;
    let mut found = None;
    for (i, trait_impl) in checked.impls.iter().enumerate() {
        eprintln!("\tchecking {trait_impl:?}");
        match trait_impl.impl_ty.matches_type(ty, types) {
            Decision::Yes => {
                eprintln!("\t -> match!");
                if found.is_some() {
                    return Candidates::Multiple;
                }
                found = Some(i);
            }
            Decision::Maybe => {
                eprintln!("\t -> maybe");
                maybe_count += 1;
            }
            Decision::No => {
                eprintln!("\t -> mismatch");
            }
        }
    }
    if maybe_count != 0 {
        return Candidates::Multiple;
    }
    if let Some(found) = found {
        Candidates::Unique(&checked.impls[found])
    } else {
        Candidates::None
    }
}

enum InstanceType {
    Generic(u8),
    Base(BaseType, Vec<InstanceType>),
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
            Type::DefId {
                id,
                generics: Some(generics),
            } => Self::Base(
                BaseType::TypeId(*id),
                generics
                    .iter()
                    .map(|g| Self::from_type(g, compiler))
                    .collect(),
            ),
            &Type::DefId { id, generics: None } => {
                let expected = compiler.get_resolved_type_def(id).generic_count;
                // TODO: error spans
                compiler.errors.emit_err(
                    Error::InvalidGenericCount { expected, found: 0 }.at_span(span::Span::MISSING),
                );
                Self::Base(BaseType::Invalid, Box::new([]))
            }
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
        }
    }
}
enum Decision {
    Yes,
    No,
    Maybe,
}
impl ImplTree {
    fn matches_type(&self, ty: TypeInfo, types: &TypeTable) -> Decision {
        match self {
            Self::Any { .. } => Decision::Yes,
            Self::Base(base_type, args) => {
                // TODO: pass info about which type doesn't implement a trait on error
                match ty {
                    TypeInfo::Invalid => return Decision::Yes,
                    TypeInfo::Unknown => return Decision::Yes,
                    TypeInfo::UnknownSatisfying { .. } => todo!("handle multiple requirements"),
                    TypeInfo::Primitive(p) => {
                        if let &BaseType::Primitive(base_p) = base_type {
                            if p == base_p {
                                return Decision::Yes;
                            }
                        }
                    }
                    TypeInfo::TypeDef(id, generics) => {
                        if let &BaseType::TypeId(base_id) = base_type {
                            if id != base_id {
                                return Decision::No;
                            }
                            debug_assert_eq!(generics.count as usize, args.len());
                            let mut decision = Decision::Yes;
                            for (arg, impl_tree) in generics.iter().zip(args) {
                                match impl_tree.matches_type(types[arg], types) {
                                    Decision::No => return Decision::No,
                                    Decision::Maybe => decision = Decision::Maybe,
                                    Decision::Yes => {}
                                }
                            }
                            return decision;
                        }
                    }
                    TypeInfo::Pointer(pointee) => {
                        if matches!(base_type, BaseType::Pointer) {
                            debug_assert_eq!(args.len(), 1);
                            return args[0].matches_type(types[pointee], types);
                        }
                    }
                    TypeInfo::Tuple(elems) => {
                        if matches!(base_type, BaseType::Tuple)
                            && args.len() == elems.count as usize
                        {
                            let mut decision = Decision::Yes;
                            for (arg, impl_tree) in elems.iter().zip(args) {
                                match impl_tree.matches_type(types[arg], types) {
                                    Decision::No => return Decision::No,
                                    Decision::Maybe => decision = Decision::Maybe,
                                    Decision::Yes => {}
                                }
                            }
                            return decision;
                        }
                    }
                    TypeInfo::Array { element, count } => {
                        if let &BaseType::Array { count: base_count } = base_type {
                            let decision = if let Some(count) = count {
                                if count != base_count {
                                    return Decision::No;
                                }
                                Decision::Yes
                            } else {
                                Decision::Maybe
                            };
                            debug_assert_eq!(args.len(), 1);
                            return match args[0].matches_type(types[element], types) {
                                Decision::Yes => decision,
                                d @ (Decision::Maybe | Decision::No) => d,
                            };
                        }
                    }
                    TypeInfo::Enum(_) => return Decision::No, // TODO: auto impl some traits for local enums
                    TypeInfo::Integer | TypeInfo::Float => {
                        todo!("handle impls for <integer>/<float>")
                    }
                    TypeInfo::Generic(_) => todo!("check traits of generics"),
                    TypeInfo::TypeItem { .. }
                    | TypeInfo::TraitItem { .. }
                    | TypeInfo::FunctionItem { .. }
                    | TypeInfo::ModuleItem { .. }
                    | TypeInfo::MethodItem { .. }
                    | TypeInfo::TraitMethodItem { .. }
                    | TypeInfo::EnumVariantItem { .. } => {
                        return Decision::No;
                    }
                }
                Decision::No
            }
        }
    }

    fn instantiate(&self, impl_generics: LocalTypeIds, types: &mut TypeTable) -> TypeInfoOrIdx {
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
                BaseType::Tuple => todo!(),
                BaseType::Array { count: _ } => todo!(),
            }),
        }
    }
}

#[derive(Debug)]
pub struct Impl {
    pub generic_count: u8,
    pub impl_ty: ImplTree,
    pub impl_module: ModuleId,
    pub functions: Vec<FunctionId>,
}
impl Impl {
    pub fn instantiate(
        &self,
        trait_generics: LocalTypeIds,
        impl_generics: LocalTypeIds,
        types: &mut TypeTable,
    ) -> TypeInfoOrIdx {
        dbg!(types[trait_generics.nth(0).unwrap()]);
        assert_eq!(trait_generics.count, 1, "TODO: handle generic traits");
        self.impl_ty.instantiate(impl_generics, types)
    }
}
