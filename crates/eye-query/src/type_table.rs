use id::{TypeId, ModuleId};
use types::{Type, Primitive};

use crate::parser::ast;

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
            Type::Invalid => TypeInfo::Invalid,
            &Type::Primitive(p) => TypeInfo::Primitive(p),
            Type::DefId { id, generics } => {
                let start = self.types.len() as u32;
                if let Some(generics) = generics {
                    let count = generics.len();
                    self.types.extend(std::iter::once(TypeInfoOrIdx::Idx(LocalTypeId(0))).take(count));
                    let generics_ids = LocalTypeIds { start, count: count as u32 };
                    for (resolved, id) in generics.iter().zip(generics_ids.iter()) {
                        self.types[id.idx()] = TypeInfoOrIdx::TypeInfo(self.info_from_resolved(resolved));
                    }
                    TypeInfo::TypeDef(*id, generics_ids)
                } else {
                    todo!("handle omitted generics or throw error?");
                }
            }
            Type::Pointer(inner) => TypeInfo::Pointer(self.from_resolved(inner)),
            Type::Array(b) => {
                let (elem_ty, count) = &**b;
                let element = self.from_resolved(elem_ty);
                TypeInfo::Array { element, count: Some(*count) }
            }
            Type::Tuple(elements) => {
                let start = self.types.len() as u32;
                let element_ids = LocalTypeIds { start, count: elements.len() as _ };
                for (element, id) in elements.iter().zip(element_ids.iter()) {
                    self.types[id.idx()] = TypeInfoOrIdx::TypeInfo(self.info_from_resolved(element));
                }
                TypeInfo::Tuple(element_ids)
            }
            Type::Generic(_) => todo!("generics"),
            Type::LocalEnum(_) => todo!("local enum infos"),
            Type::TraitSelf => todo!("trait self"),
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
    use types::Primitive as P;
    match (a, b) {
        (t, Unknown | Primitive(P::Never)) | (Unknown | Primitive(P::Never), t) => t,
        (Primitive(p_a), Primitive(p_b)) if p_a == p_b => a,
        (Invalid, _) | (_, Invalid) => Invalid,
        (Primitive(t), Integer) | (Integer, Primitive(t)) if t.is_int() => Primitive(t),
        (Primitive(t), Float) | (Float, Primitive(t)) if t.is_float() => Primitive(t),
        (TypeDef(id_a, generics_a), TypeDef(id_b, generics_b)) if id_a == id_b => {
            debug_assert_eq!(generics_a.count, generics_b.count);
            for (a, b) in generics_a.iter().zip(generics_b.iter()) {
                types.unify(a, b);
            }
            a
        }
        (TypeDef(id, generics), Enum { idx, count }) | (Enum { idx, count }, TypeDef(id, generics)) => {
            _ = (id, generics, idx, count);
            todo!("unify with enums (requires symbol access)")
        }
        (Enum { idx: a, count: c_a }, Enum { idx: b, count: c_b }) => {
            _ = (a, c_a, b, c_b);
            todo!("unify enums")
        }
        (Pointer(a), Pointer(b)) => {
            types.unify(a, b);
            Pointer(a)
        }
        (Array { element: a, count: c_a }, Array { element: b, count: c_b }) => {
            types.unify(a, b);
            let count = match (c_a, c_b) {
                (Some(c), None) | (None, Some(c)) => Some(c),
                (None, None) => None,
                (Some(a), Some(b)) => if a == b {
                    Some(a)
                } else {
                    panic!("can't unify types");
                }
            };
            Array { element: a, count }
        }
        (Tuple(a), Tuple(b)) => {
            // TODO: reintroduce tuple count mode
            if a.count != b.count {
                panic!("can't unify types");
            }
            for (a, b) in a.iter().zip(b.iter()) {
                types.unify(a, b);
            }
            Tuple(a)
        }
        (
            FunctionItem { module: a_m, function: a_f, generics: a_g },
            FunctionItem { module: b_m, function: b_f, generics: b_g },
        ) if a_m == b_m && a_f == b_f => {
            debug_assert_eq!(a_g.count, b_g.count, "invalid generics count, incorrect type info constructed");
            for (a, b) in a_g.iter().zip(b_g.iter()) {
                types.unify(a, b);
            }
            a
        }
        (
            MethodItem { module: a_m, function: a_f, generics: a_g, this_ty: a_t },
            MethodItem { module: b_m, function: b_f, generics: b_g, this_ty: b_t },
        ) if a_m == b_m && a_f == b_f => {
            types.unify(a_t, b_t);
            for (a, b) in a_g.iter().zip(b_g.iter()) {
                types.unify(a, b);
            }
            a
        }
        (Generic(a), Generic(b)) if a == b => Generic(a),
        _ => panic!("can't unify types {a:?} {b:?}"),
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LocalTypeIds {
    start: u32,
    count: u32,
}
impl LocalTypeIds {
    fn iter(self) -> impl Iterator<Item = LocalTypeId> {
        (self.start .. self.start + self.count).map(LocalTypeId)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TypeInfo {
    Unknown,
    Primitive(Primitive),
    Integer,
    Float,
    TypeDef(TypeId, LocalTypeIds),
    Pointer(LocalTypeId),
    Array {
        element: LocalTypeId,
        count: Option<u32>,
    },
    Enum {
        idx: u32,
        count: u32,
    },
    Tuple(LocalTypeIds),
    FunctionItem {
        module: ModuleId,
        function: ast::FunctionId,
        generics: LocalTypeIds,
    },
    MethodItem {
        module: ModuleId,
        function: ast::FunctionId,
        generics: LocalTypeIds,
        this_ty: LocalTypeId,
    },
    Generic(u8),
    Invalid,
}
