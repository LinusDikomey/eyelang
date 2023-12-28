use id::TypeId;
use types::{Type, Primitive};

id::id!(LocalTypeId);

#[derive(Debug)]
pub struct TypeTable {
    types: Vec<TypeInfoOrIdx>,
}
impl TypeTable {
    pub fn new() -> Self {
        Self {
            types: Vec::new(),
        }
    }

    pub fn from_resolved(&mut self, ty: &Type) -> LocalTypeId {
        let info = self.info_from_resolved(ty);
        let id = LocalTypeId(self.types.len() as _);
        self.types.push(TypeInfoOrIdx::TypeInfo(info));
        id
    }

    pub fn add_unknown(&mut self) -> LocalTypeId {
        let id = LocalTypeId(self.types.len() as _);
        self.types.push(TypeInfoOrIdx::TypeInfo(TypeInfo::Unknown));
        id
    }

    pub fn info_from_resolved(&mut self, ty: &Type) -> TypeInfo {
        match ty {
            &Type::Primitive(p) => TypeInfo::Primitive(p),
            Type::DefId { id, generics } => {
                let start = self.types.len() as u32;
                let count = generics.len();
                self.types.extend(std::iter::once(TypeInfoOrIdx::Idx(LocalTypeId(0))).take(count));
                let generics_ids = TypeIds { start, count: count as u32 };
                for (resolved, id) in generics.iter().zip(generics_ids.iter()) {
                    self.types[id.idx()] = TypeInfoOrIdx::TypeInfo(self.info_from_resolved(resolved));
                }
                TypeInfo::TypeDef(*id, generics_ids)
            }
            Type::Pointer(inner) => TypeInfo::Pointer(self.from_resolved(inner)),
            Type::Array(b) => {
                let (elem_ty, count) = &**b;
                let element = self.from_resolved(elem_ty);
                TypeInfo::Array { element, count: Some(*count) }
            }
            Type::Tuple(elements) => {
                let start = self.types.len() as u32;
                let element_ids = TypeIds { start, count: elements.len() as _ };
                for (element, id) in elements.iter().zip(element_ids.iter()) {
                    self.types[id.idx()] = TypeInfoOrIdx::TypeInfo(self.info_from_resolved(element));
                }
                TypeInfo::Tuple(element_ids)
            }
            _ => todo!(),
        }
    }

    pub fn unify(&mut self, mut a: LocalTypeId, mut b: LocalTypeId) {
        let a_ty = loop {
            match self.types[a.idx()] {
                TypeInfoOrIdx::Idx(idx) => a = idx,
                TypeInfoOrIdx::TypeInfo(ty) => break ty,
            }
        };
        let b_ty = loop {
            match self.types[b.idx()] {
                TypeInfoOrIdx::Idx(idx) => b = idx,
                TypeInfoOrIdx::TypeInfo(ty) => break ty,
            }
        };
        if a == b {
            // a and b point to the same indices
            return;
        }
        self.types[b.idx()] = TypeInfoOrIdx::Idx(a);
        let new = unify(a_ty, b_ty, self);
        self.types[a.idx()] = TypeInfoOrIdx::TypeInfo(new);
    }

    pub fn specify(&mut self, mut a: LocalTypeId, info: TypeInfo) {
        let a_ty = loop {
            match self.types[a.idx()] {
                TypeInfoOrIdx::Idx(idx) => a = idx,
                TypeInfoOrIdx::TypeInfo(info) => break info,
            }
        };
        self.types[a.idx()] = TypeInfoOrIdx::TypeInfo(unify(a_ty, info, self));
    }
}

#[derive(Debug)]
enum TypeInfoOrIdx {
    TypeInfo(TypeInfo),
    Idx(LocalTypeId),
}

fn unify(a: TypeInfo, b: TypeInfo, types: &mut TypeTable) -> TypeInfo {
    use TypeInfo::*;
    match (a, b) {
        (Unknown, _) => b,
        (_, Unknown) => a,
        (Primitive(p_a), Primitive(p_b)) if p_a == p_b => a,
        (TypeDef(id_a, generics_a), TypeDef(id_b, generics_b)) if id_a == id_b => {
            debug_assert_eq!(generics_a.count, generics_b.count);
            for (a, b) in generics_a.iter().zip(generics_b.iter()) {
                types.unify(a, b);
            }
            a
        }
        _ => panic!("can't unify types"),
    }
}

#[derive(Debug, Clone, Copy)]
struct TypeIds {
    start: u32,
    count: u32,
}
impl TypeIds {
    fn iter(self) -> impl Iterator<Item = LocalTypeId> {
        (self.start .. self.start + self.count).map(LocalTypeId)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TypeInfo {
    Unknown,
    Primitive(Primitive),
    Integer,
    TypeDef(TypeId, TypeIds),
    Pointer(LocalTypeId),
    Array {
        element: LocalTypeId,
        count: Option<u32>,
    },
    Tuple(TypeIds),
    Invalid,
}
