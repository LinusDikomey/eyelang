use std::ops::Index;

use crate::{types::{Primitive, Layout}, ast::TypeId, resolve::{type_info::{TypeInfo, TypeTable}, types::Enum}};

use super::Module;



#[derive(Debug)]
pub struct IrTypes {
    types: Vec<IrType>,
}
impl IrTypes {
    pub fn new() -> Self {
        Self {
            types: Vec::new(),
        }
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
                let generic_idx = self.types.len() as u32;
                self.types.extend(std::iter::repeat(IrType::Primitive(Primitive::Unit)).take(generics.len()));
                
                for (i, ty) in generics.iter().enumerate() {
                    self.types[i] = self.info_to_ty(types.get(ty), types);
                }

                IrType::Id(id, TypeRefs { idx: generic_idx, count: generics.len() as _ })
            }
            TypeInfo::Pointer(pointee) => IrType::Ptr(self.add_info(types.get(pointee), types)),
            TypeInfo::Array(Some(count), elem) => IrType::Array(self.add_info(types.get(elem), types), count),
            TypeInfo::Enum(names) => IrType::Primitive(Enum::int_ty_from_variant_count(names.count()).into()),
            TypeInfo::Tuple(elems, _) => {
                let elems_idx = self.types.len() as u32;
                self.types.extend(std::iter::repeat(IrType::Primitive(Primitive::Unit)).take(elems.len()));
                for (i, ty) in elems.iter().enumerate() {
                    self.types[i] = self.info_to_ty(types.get(ty), types);
                }
                IrType::Tuple(TypeRefs { idx: elems_idx, count: elems.len() as _ })
            }
            TypeInfo::Unknown => IrType::Primitive(Primitive::Unit),
            TypeInfo::Array(None, _) | TypeInfo::Invalid | TypeInfo::Generic(_)
            | TypeInfo::SymbolItem(_) | TypeInfo::MethodItem { .. } 
            | TypeInfo::EnumItem(_, _) | TypeInfo::LocalTypeItem(_)
                => panic!("Invalid type supplied while buiding ir: {info:?}"),
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
        &self.types[index.0 as usize]
    }
}
impl Index<TypeRefs> for IrTypes {
    type Output = [IrType];

    fn index(&self, index: TypeRefs) -> &Self::Output {
        &self.types[index.idx as usize .. index.idx as usize + index.count as usize]
    }
}

#[derive(Clone, Copy, Debug)]
pub enum IrType {
    Primitive(Primitive),
    Id(TypeId, TypeRefs),
    Ptr(TypeRef),
    Array(TypeRef, u32),
    Tuple(TypeRefs),
}
impl IrType {
    pub fn layout(self, types: &IrTypes, module: &Module) -> Layout {
        match self {
            IrType::Primitive(p) => p.layout(),
            IrType::Id(id, generics) => {
                module.types[id.idx()].1.layout(
                    |id| &module.types[id.idx()].1,
                    |i| types[generics.nth(i as _)].layout(types, module)
                )
            }
            IrType::Ptr(_) => Layout { size: 8, alignment: 8 },
            IrType::Array(elem_ty, size) => {
                let elem_layout = types[elem_ty].layout(types, module);
                Layout {
                    size: elem_layout.size * size as u64,
                    alignment: elem_layout.alignment,
                }
            }
            IrType::Tuple(elems) => {
                let mut layout = Layout { size: 0, alignment: 1 };
                for ty in &types[elems] {
                    layout = layout.accumulate(ty.layout(types, module));
                }
                layout
            }
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