use std::ops::Index;

use crate::{types::{Primitive, Layout}, ast::TypeId, resolve::types::{Type, ResolvedTypeDef, Enum}};

#[derive(Debug)]
pub struct IrTypes {
    types: Vec<IrType>,
    generics: TypeRefs,
}
impl IrTypes {
    pub fn new() -> Self {
        Self {
            types: vec![],
            generics: TypeRefs::EMPTY,
        }
    }
    pub fn new_with(types: Vec<IrType>, generics: TypeRefs) -> Self {
        Self { types, generics }
    }
    pub fn instantiate_generic(&mut self, i: u8, ty: IrType) {
        let i = self.generics.nth(i as _);
        self.types[i.idx()] = ty;
    }
    pub fn generics(&self) -> TypeRefs {
        self.generics
    }

    /*
    fn info_to_ty(&mut self, info: TypeInfo, types: &TypeTable) -> IrType {
        match info {
            TypeInfo::Int => IrType::Primitive(Primitive::I32),
            TypeInfo::Float => IrType::Primitive(Primitive::F32),
            TypeInfo::Primitive(p) => IrType::Primitive(p),
            TypeInfo::Resolved(id, generics) => {
                let generic_idx = self.types.len();
                self.types.extend(std::iter::repeat(IrType::Primitive(Primitive::Unit)).take(generics.len()));
                
                for (i, ty) in generics.iter().enumerate() {
                    self.types[generic_idx + i] = self.info_to_ty(types.get(ty), types);
                }

                IrType::Id(id, TypeRefs { idx: generic_idx as _, count: generics.len() as _ })
            }
            TypeInfo::Pointer(pointee) => IrType::Ptr(self.add_info(types.get(pointee), types)),
            TypeInfo::Array(Some(count), elem) => IrType::Array(self.add_info(types.get(elem), types), count),
            TypeInfo::Enum(variants) => {
                let ordinal_ty = Enum::int_ty_from_variant_count(variants.count()).map_or(Primitive::Unit, Into::into);
                let mut layout = Layout::EMPTY;
                for (_name, arg_types) in types.get_enum_variants(variants) {
                    let mut variant_layout = Layout::EMPTY;
                    for ty in arg_types.iter() {
                        todo!("enum arg irgen")
                        //variant_layout.accumulate(self.info_to_ty(types[ty], types).layout(self, |id| ))
                    }
                }
                IrType::Primitive(ordinal_ty)
            }
            TypeInfo::Tuple(elems, _) => {
                let elems_idx = self.types.len();
                self.types.extend(std::iter::repeat(IrType::Primitive(Primitive::Unit)).take(elems.len()));
                for (i, ty) in elems.iter().enumerate() {
                    self.types[elems_idx + i] = self.info_to_ty(types.get(ty), types);
                }
                IrType::Tuple(TypeRefs { idx: elems_idx as _, count: elems.len() as _ })
            }
            TypeInfo::Generic(i) => self.generic_instances[i as usize],
            TypeInfo::Unknown => IrType::Primitive(Primitive::Unit),
            TypeInfo::Array(None, _) | TypeInfo::Invalid
            | TypeInfo::SymbolItem(_) | TypeInfo::MethodItem { .. } 
            | TypeInfo::LocalTypeItem(_)
                => panic!("Invalid type supplied while buiding ir: {info:?}"),
        }
    }
    fn add_info(&mut self, info: TypeInfo, types: &TypeTable) -> TypeRef {
        let ty = self.info_to_ty(info, types);
        self.add(ty)
    }
    */
    pub fn add(&mut self, ty: IrType) -> TypeRef {
        self.types.push(ty);
        TypeRef((self.types.len() - 1) as u32)
    }
    pub fn add_ptr_ty(&mut self, pointee: TypeRef) -> TypeRef {
        self.add(IrType::Ptr(pointee))
    }
    pub fn add_multiple(&mut self, types: impl IntoIterator<Item = IrType>) -> TypeRefs {
        let start = self.types.len();
        self.types.extend(types);
        TypeRefs { idx: start as _, count: (self.types.len() - start) as _ }
    }
    pub fn replace(&mut self, idx: TypeRef, ty: IrType) {
        self.types[idx.idx()] = ty;
    }
    pub fn from_resolved(&mut self, ty: &Type, on_generic: TypeRefs) -> IrType {
        let add_tuple = |s: &mut IrTypes, elems: &[Type]| -> TypeRefs {
            let idx = s.types.len() as u32;
            s.types.extend((0..elems.len()).map(|_| IrType::Primitive(Primitive::Unit)));

            for (i, ty) in elems.iter().enumerate() {
                s.types[idx as usize + i] = s.from_resolved(ty, on_generic);
            }
            TypeRefs { idx, count: elems.len() as _ }
        };
        match ty {
            Type::Prim(p) => IrType::Primitive(*p),
            Type::Id(id, generics) => {
                let generic_idx = self.types.len() as u32;
                self.types.extend(std::iter::repeat(IrType::Primitive(Primitive::Never)).take(generics.len()));
                
                for (i, ty) in generics.iter().enumerate() {
                    self.types[generic_idx as usize + i] = self.from_resolved(ty, on_generic);
                }
                IrType::Id(*id, TypeRefs { idx: generic_idx, count: generics.len() as _ })
            }
            Type::Pointer(inner) => {
                let inner = self.from_resolved(inner, on_generic);
                IrType::Ptr(self.add(inner))
            }
            Type::Array(b) => {
                let elem_ty = self.from_resolved(&b.0, on_generic);
                IrType::Array(self.add(elem_ty), b.1)
            }
            Type::Tuple(elems) => {
                IrType::Tuple(add_tuple(self, elems))
            }
            Type::Generic(i) => IrType::Ref(on_generic.nth(*i as _)),
            Type::LocalEnum(variants) => {
                let idx = self.types.len() as u32;
                self.types.extend(std::iter::repeat(IrType::Primitive(Primitive::Never)).take(variants.len()));

                for (i, args) in variants.iter().enumerate() {
                    self.types[idx as usize + i] = IrType::Tuple(add_tuple(self, args));
                }

                IrType::Enum(TypeRefs { idx, count: variants.len() as _ })
            }
            Type::Invalid => unreachable!("invalid 'Type' encountered during irgen"),
        }
    }
    pub fn layout<'a, F: Fn(TypeId) -> &'a ResolvedTypeDef + Copy>(&'a self, ty: IrType, get_type: F) -> Layout {
        ty.layout(self, get_type)
    }
}

impl Index<TypeRef> for IrTypes {
    type Output = IrType;

    fn index(&self, index: TypeRef) -> &Self::Output {
        match &self.types[index.0 as usize] {
            IrType::Ref(r) => &self[*r],
            other => other
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum IrType {
    Primitive(Primitive),
    Id(TypeId, TypeRefs),
    Ptr(TypeRef),
    Array(TypeRef, u32),
    Tuple(TypeRefs),
    Enum(TypeRefs),  /// TypeRefs should point to tuples of arguments
    
    Const(ConstIrType),

    Ref(TypeRef), // just refers to a different index
}
impl IrType {
    /// Checks if the type is a type of the provided id and ignores generics.
    pub fn is_id(&self, id: TypeId) -> bool {
        match self {
            Self::Id(my_id, _) => *my_id == id,
            Self::Ref(_) => panic!("is_id used on a Ref type"),
            _ => false,
        }
    }
    pub fn layout<'a>(self, types: &IrTypes, get_type: impl Fn(TypeId) -> &'a ResolvedTypeDef + Copy) -> Layout {
        match self {
            IrType::Primitive(p) => p.layout(),
            IrType::Id(id, generics) => {
                // PERF: heap allocation + recalculation of enum layout
                let generics: Vec<_> = generics.iter().map(|ty| types[ty].as_resolved_type(types)).collect();
                get_type(id).layout(get_type, &generics)
            }
            IrType::Ptr(_) => Layout::PTR,
            IrType::Array(elem_ty, count) => Layout::array(types[elem_ty].layout(types, get_type), count),
            IrType::Tuple(elems) => {
                let mut layout = Layout { size: 0, alignment: 1 };
                for ty in elems.iter() {
                    let ty = &types[ty];
                    layout.accumulate(ty.layout(types, get_type));
                }
                layout
            }
            IrType::Enum(variants) => {
                let tag_layout = Enum::int_ty_from_variant_count(variants.len() as u32)
                    .map_or(Layout::EMPTY, |ty| Primitive::from(ty).layout());
                let mut layout = tag_layout;

                for variant in variants.iter() {
                    let IrType::Tuple(args) = types[variant] else { panic!("invalid IrType found") };
                    let mut variant_layout = tag_layout;
                    for arg in args.iter() {
                        variant_layout.accumulate(types[arg].layout(types, get_type));
                    }
                    layout.add_variant(variant_layout);
                }
                layout
            }
            IrType::Const(_) => todo!("const IrType layout"),
            IrType::Ref(r) => types[r].layout(types, get_type),
        }
    }
    pub fn as_resolved_type(self, types: &IrTypes) -> Type {
        match self {
            IrType::Primitive(p) => Type::Prim(p),
            IrType::Id(id, generics) => Type::Id(
                id,
                generics
                    .iter()
                    .map(|ty| types[ty].as_resolved_type(types))
                    .collect()
            ),
            IrType::Ptr(pointee) => Type::Pointer(Box::new(types[pointee].as_resolved_type(types))),
            IrType::Array(member, count) => Type::Array(Box::new((
                types[member].as_resolved_type(types),
                count
            ))),
            IrType::Tuple(members) => Type::Tuple(
                members
                    .iter()
                    .map(|ty| types[ty].as_resolved_type(types))
                    .collect()
            ),
            IrType::Enum(variants) => Type::LocalEnum(
                variants.iter()
                    .map(|variant| {
                        let IrType::Tuple(args) = types[variant] else { unreachable!() };
                        args.iter()
                            .map(|ty| types[ty].as_resolved_type(types))
                            .collect()
                    })
                    .collect()
            ),
            IrType::Const(_) => todo!("Const IrType as Type"),
            IrType::Ref(idx) => types[idx].as_resolved_type(types),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ConstIrType {
    Int,
    Float,
    Enum,
    Type,
}

#[derive(Clone, Copy, Debug)]
pub struct TypeRef(u32);
impl TypeRef {
    pub const NONE: Self = Self(u32::MAX);

    pub fn new(idx: u32) -> Self {
        Self(idx)
    }
    pub fn is_present(self) -> bool {
        self.0 != u32::MAX
    }
    pub fn idx(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug)]
pub struct TypeRefs { pub idx: u32, pub count: u32 }
impl TypeRefs {
    pub const EMPTY: Self = Self { idx: 0, count: 0 };
    
    pub fn iter(self) -> impl Iterator<Item = TypeRef> {
        (self.idx .. self.idx + self.count).map(TypeRef)
    }
    pub fn len(self) -> usize {
        self.count as usize
    }
    pub fn nth(self, idx: u32) -> TypeRef {
        debug_assert!(idx < self.count);
        TypeRef(self.idx + idx)
    }
}
