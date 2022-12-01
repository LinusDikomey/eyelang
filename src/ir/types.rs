use std::ops::Index;

use crate::{types::{Primitive, Layout}, ast::TypeId, resolve::{type_info::{TypeInfo, TypeTable}, types::{Enum, Type, ResolvedTypeDef}, self}};

#[derive(Debug)]
pub struct IrTypes {
    types: Vec<IrType>,
    generic_instances: Vec<IrType>,
}
impl IrTypes {
    pub fn new(generic_instances: Vec<IrType>) -> Self {
        Self {
            types: Vec::new(),
            generic_instances,
        }
    }
    pub fn add_generic_instance_ty(&mut self, ty: IrType) {
        self.generic_instances.push(ty);
    }
    pub fn add(&mut self, ty: IrType) -> TypeRef {
        self.types.push(ty);
        TypeRef((self.types.len() - 1) as u32)
    }
    pub fn info_to_ty(&mut self, info: TypeInfo, types: &TypeTable) -> IrType {
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
            TypeInfo::Enum(names) => IrType::Primitive(Enum::int_ty_from_variant_count(names.count()).into()),
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
    pub fn resolved_to_ty(&mut self, ty: &Type, on_generic: impl Fn(u8) -> TypeRef + Copy) -> IrType {
        match ty {
            resolve::types::Type::Prim(p) => IrType::Primitive(*p),
            resolve::types::Type::Id(id, generics) => {
                let generic_idx = self.types.len() as u32;
                self.types.extend(std::iter::repeat(IrType::Primitive(Primitive::Unit)).take(generics.len()));
                
                for (i, ty) in generics.iter().enumerate() {
                    self.types[i] = self.resolved_to_ty(ty, |i| TypeRef(generic_idx + i as u32));
                }
                IrType::Id(*id, TypeRefs { idx: generic_idx, count: generics.len() as _ })
            }
            resolve::types::Type::Pointer(inner) => {
                let inner = self.resolved_to_ty(inner, on_generic);
                IrType::Ptr(self.add(inner))
            }
            resolve::types::Type::Array(b) => {
                let elem_ty = self.resolved_to_ty(&b.0, on_generic);
                IrType::Array(self.add(elem_ty), b.1)
            }
            resolve::types::Type::Enum(variants) => IrType::Primitive(
                Enum::int_ty_from_variant_count(variants.len() as _).into()
            ),
            resolve::types::Type::Tuple(elems) => {
                let idx = self.types.len() as u32;
                self.types.extend((0..elems.len()).map(|_| IrType::Primitive(Primitive::Unit)));

                for (i, ty) in elems.iter().enumerate() {
                    self.types[i] = self.resolved_to_ty(ty, on_generic);
                }
                IrType::Tuple(TypeRefs { idx, count: elems.len() as _ })
            }
            resolve::types::Type::Generic(i) => IrType::Ref(on_generic(*i)),
            resolve::types::Type::Invalid => unreachable!("invalid 'Type' encountered during irgen"),
        }
    }
    pub fn add_info(&mut self, info: TypeInfo, types: &TypeTable) -> TypeRef {
        let ty = self.info_to_ty(info, types);
        self.add(ty)
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
    
    Ref(TypeRef), // just refers to a different index
}
impl IrType {
    pub fn layout<'a>(self, types: &IrTypes, get_type: impl Fn(TypeId) -> &'a ResolvedTypeDef + Copy) -> Layout {
        match self {
            IrType::Primitive(p) => p.layout(),
            IrType::Id(id, generics) => {
                let generics: Vec<_> = generics.iter().map(|ty| types[ty].as_resolved_type(types)).collect();
                get_type(id).layout(get_type, &generics)
            }
            IrType::Ptr(_) => Layout { size: 8, alignment: 8 },
            IrType::Array(elem_ty, size) => {
                let elem_layout = types[elem_ty].layout(types, get_type);
                Layout {
                    size: elem_layout.size * size as u64,
                    alignment: elem_layout.alignment,
                }
            }
            IrType::Tuple(elems) => {
                let mut layout = Layout { size: 0, alignment: 1 };
                for ty in elems.iter() {
                    let ty = &types[ty];
                    layout = layout.accumulate(ty.layout(types, get_type));
                }
                layout
            }
            IrType::Ref(r) => types[r].layout(types, get_type),
        }
    }
    pub fn as_resolved_type(self, types: &IrTypes) -> Type {
        match self {
            IrType::Primitive(p) => Type::Prim(p),
            IrType::Id(id, generics) => Type::Id(id, generics.iter().map(|ty| types[ty].as_resolved_type(types)).collect()),
            IrType::Ptr(pointee) => Type::Pointer(Box::new(types[pointee].as_resolved_type(types))),
            IrType::Array(member, count) => Type::Array(Box::new((types[member].as_resolved_type(types), count))),
            IrType::Tuple(members) => Type::Tuple(members.iter().map(|ty| types[ty].as_resolved_type(types)).collect()),
            IrType::Ref(idx) => types[idx].as_resolved_type(types),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct TypeRef(u32);
impl TypeRef {
    pub const NONE: Self = Self(u32::MAX);

    pub fn is_present(self) -> bool {
        self.0 != u32::MAX
    }
}

#[derive(Clone, Copy, Debug)]
pub struct TypeRefs { idx: u32, count: u32 }
impl TypeRefs {
    pub const EMPTY: Self = Self { idx: 0, count: 0 };
    
    pub fn iter(self) -> impl Iterator<Item = TypeRef> {
        (self.idx .. self.idx + self.count).map(TypeRef)
    }
    pub fn len(self) -> usize {
        self.count as usize
    }
    pub fn _nth(self, idx: u32) -> TypeRef {
        debug_assert!(idx < self.count);
        TypeRef(self.idx + idx)
    }
}