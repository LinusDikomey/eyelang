use std::ops::Index;

use id::{ModuleId, TypeId};
use span::Span;
use types::{Primitive, Type};

use crate::{
    compiler::Def,
    error::{Error, Errors},
    parser::ast,
    Compiler,
};

id::id!(LocalTypeId);

#[derive(Debug, Clone)]
pub struct TypeTable {
    types: Vec<TypeInfoOrIdx>,
}
impl Index<LocalTypeId> for TypeTable {
    type Output = TypeInfo;
    fn index(&self, mut index: LocalTypeId) -> &Self::Output {
        loop {
            match &self.types[index.idx()] {
                &TypeInfoOrIdx::Idx(new_index) => {
                    debug_assert_ne!(new_index, index);
                    index = new_index;
                }
                TypeInfoOrIdx::TypeInfo(info) => return info,
            }
        }
    }
}
impl TypeTable {
    pub fn new() -> Self {
        Self { types: Vec::new() }
    }

    pub fn add(&mut self, info: TypeInfo) -> LocalTypeId {
        let id = LocalTypeId(self.types.len() as _);
        self.types.push(TypeInfoOrIdx::TypeInfo(info));
        id
    }

    pub fn add_info_or_idx(&mut self, info_or_idx: TypeInfoOrIdx) -> LocalTypeId {
        match info_or_idx {
            TypeInfoOrIdx::Idx(idx) => idx,
            TypeInfoOrIdx::TypeInfo(info) => self.add(info),
        }
    }

    pub fn add_unknown(&mut self) -> LocalTypeId {
        let id = LocalTypeId(self.types.len() as _);
        self.types.push(TypeInfoOrIdx::TypeInfo(TypeInfo::Unknown));
        id
    }

    pub fn to_resolved(&self, info: TypeInfo) -> Type {
        match info {
            TypeInfo::Primitive(p) => Type::Primitive(p),
            TypeInfo::Unknown | TypeInfo::Integer | TypeInfo::Float => unreachable!(),
            TypeInfo::Pointer(pointee) => Type::Pointer(Box::new(self.to_resolved(self[pointee]))),
            TypeInfo::TypeDef(id, generics) => Type::DefId {
                id,
                generics: Some(
                    generics
                        .iter()
                        .map(|generic| self.to_resolved(self[generic]))
                        .collect(),
                ),
            },
            TypeInfo::Invalid => Type::Invalid,
            _ => todo!("type to resolved: {info:?}"),
        }
    }

    pub fn add_multiple(&mut self, infos: impl IntoIterator<Item = TypeInfo>) -> LocalTypeIds {
        let start = self.types.len();
        self.types
            .extend(infos.into_iter().map(TypeInfoOrIdx::TypeInfo));
        let count = self.types.len() - start;
        LocalTypeIds {
            start: start as _,
            count: count as _,
        }
    }

    pub fn add_multiple_info_or_idx(
        &mut self,
        infos: impl IntoIterator<Item = TypeInfoOrIdx>,
    ) -> LocalTypeIds {
        let start = self.types.len();
        self.types.extend(infos.into_iter());
        let count = self.types.len() - start;
        LocalTypeIds {
            start: start as _,
            count: count as _,
        }
    }

    pub fn add_multiple_unknown(&mut self, count: u32) -> LocalTypeIds {
        let start = self.types.len() as _;
        self.types.extend(
            std::iter::repeat(TypeInfoOrIdx::TypeInfo(TypeInfo::Unknown)).take(count as usize),
        );
        LocalTypeIds { start, count }
    }

    pub fn replace(&mut self, id: LocalTypeId, info_or_idx: TypeInfoOrIdx) {
        debug_assert!(
            !matches!(info_or_idx, TypeInfoOrIdx::Idx(idx) if idx == id),
            "created recursive reference",
        );
        self.types[id.idx()] = info_or_idx;
    }

    pub fn generic_info_from_resolved(&mut self, compiler: &mut Compiler, ty: &Type) -> TypeInfo {
        let ty = self.from_generic_resolved_internal(compiler, ty, None);
        let TypeInfoOrIdx::TypeInfo(info) = ty else {
            // we can't get back a generic since we don't pass in any generics
            unreachable!()
        };
        info
    }

    pub fn info_from_resolved(&mut self, compiler: &mut Compiler, ty: &Type) -> TypeInfo {
        let ty = self.from_generic_resolved(compiler, ty, LocalTypeIds::EMPTY);
        let TypeInfoOrIdx::TypeInfo(info) = ty else {
            // we can't get back a generic since we don't pass in any generics
            unreachable!()
        };
        info
    }

    pub fn from_generic_resolved(
        &mut self,
        compiler: &mut Compiler,
        ty: &Type,
        generics: LocalTypeIds,
    ) -> TypeInfoOrIdx {
        self.from_generic_resolved_internal(compiler, ty, Some(generics))
    }
    /// Only produces an Index instead of a TypeInfo when the Type is Type::Generic
    /// generics: None will produce generic TypeInfos for generic functions
    fn from_generic_resolved_internal(
        &mut self,
        compiler: &mut Compiler,
        ty: &Type,
        generics: Option<LocalTypeIds>,
    ) -> TypeInfoOrIdx {
        let info = match ty {
            Type::Invalid => TypeInfo::Invalid,
            &Type::Primitive(p) => TypeInfo::Primitive(p),
            Type::DefId {
                id,
                generics: inner_generics,
            } => {
                if let Some(inner_generics) = inner_generics {
                    let count = inner_generics.len();
                    let generics_ids = self.add_multiple_unknown(count as u32);
                    for (resolved, id) in inner_generics.iter().zip(generics_ids.iter()) {
                        let ty = self.from_generic_resolved_internal(compiler, resolved, generics);
                        self.replace(id, ty)
                    }
                    TypeInfo::TypeDef(*id, generics_ids)
                } else {
                    let resolved = compiler.get_resolved_type_def(*id);
                    let generics = self.add_multiple_unknown(resolved.generic_count.into());
                    TypeInfo::TypeDef(*id, generics)
                }
            }
            Type::Pointer(pointee) => {
                let pointee = self.from_generic_resolved_internal(compiler, pointee, generics);
                let pointee = self.add_info_or_idx(pointee);
                TypeInfo::Pointer(pointee)
            }
            Type::Array(b) => {
                let (elem_ty, count) = &**b;
                let element = self.from_generic_resolved_internal(compiler, elem_ty, generics);
                let element = self.add_info_or_idx(element);
                TypeInfo::Array {
                    element,
                    count: Some(*count),
                }
            }
            Type::Tuple(elements) => {
                let element_ids = self.add_multiple_unknown(elements.len() as _);
                for (element, id) in elements.iter().zip(element_ids.iter()) {
                    self.types[id.idx()] =
                        self.from_generic_resolved_internal(compiler, element, generics);
                }
                TypeInfo::Tuple(element_ids)
            }
            &Type::Generic(i) => match generics {
                Some(generics) => return TypeInfoOrIdx::Idx(generics.nth(i.into()).unwrap()),
                None => TypeInfo::Generic(i),
            },
            Type::LocalEnum(_) => todo!("local enum infos"),
            Type::TraitSelf => todo!("trait self"),
        };
        TypeInfoOrIdx::TypeInfo(info)
    }

    pub fn info_from_unresolved(
        &mut self,
        ty: &types::UnresolvedType,
        compiler: &mut crate::Compiler,
        module: ModuleId,
        scope: ast::ScopeId,
    ) -> TypeInfo {
        match ty {
            types::UnresolvedType::Primitive { ty, .. } => TypeInfo::Primitive(*ty),
            types::UnresolvedType::Unresolved(path, generics) => {
                assert!(
                    generics.is_none(),
                    "TODO: implement generics for type paths"
                ); // TODO
                let def = compiler.resolve_path(module, scope, *path);
                match def {
                    Def::Invalid => TypeInfo::Invalid,
                    Def::Type(ty) => self.info_from_resolved(compiler, &ty),
                    Def::ConstValue(_)
                    | Def::Module(_)
                    | Def::Global(_, _)
                    | Def::Function(_, _) => {
                        compiler
                            .errors
                            .emit_err(Error::TypeExpected.at_span(path.span().in_mod(module)));
                        TypeInfo::Invalid
                    }
                }
            }
            types::UnresolvedType::Pointer(b) => {
                let (pointee, _) = &**b;
                let pointee = self.info_from_unresolved(pointee, compiler, module, scope);
                TypeInfo::Pointer(self.add(pointee))
            }
            types::UnresolvedType::Array(b) => {
                let (elem, count, _) = &**b;
                let elem = self.info_from_unresolved(elem, compiler, module, scope);
                TypeInfo::Array {
                    element: self.add(elem),
                    count: *count,
                }
            }
            types::UnresolvedType::Tuple(elems, _) => {
                let ids = LocalTypeIds {
                    start: self.types.len() as _,
                    count: elems.len() as _,
                };
                self.types.extend(
                    std::iter::repeat(TypeInfoOrIdx::TypeInfo(TypeInfo::Unknown)).take(elems.len()),
                );

                for (id, unresolved) in ids.iter().zip(elems) {
                    let info = self.info_from_unresolved(unresolved, compiler, module, scope);
                    self.types[id.idx()] = TypeInfoOrIdx::TypeInfo(info);
                }

                TypeInfo::Tuple(ids)
            }
            types::UnresolvedType::Infer(_) => TypeInfo::Unknown,
        }
    }

    pub fn unify(
        &mut self,
        mut a: LocalTypeId,
        mut b: LocalTypeId,
        errors: &mut Errors,
        span: impl FnOnce() -> Span,
    ) {
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
        let new = unify(a_ty, b_ty, self).unwrap_or_else(|| {
            let mut expected = String::new();
            self.type_to_string(a_ty, &mut expected);
            let mut found = String::new();
            self.type_to_string(b_ty, &mut found);
            errors.emit_err(Error::MismatchedType { expected, found }.at_span(span()));
            TypeInfo::Invalid
        });
        self.types[a.idx()] = TypeInfoOrIdx::TypeInfo(new);
    }

    fn try_unify(&mut self, mut a: LocalTypeId, mut b: LocalTypeId) -> bool {
        let original_b = b;
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
        a == b
            || unify(a_ty, b_ty, self)
                .inspect(|_| {
                    self.types[b.idx()] = TypeInfoOrIdx::Idx(a);
                    self.types[original_b.idx()] = TypeInfoOrIdx::Idx(a);
                })
                .is_some()
    }

    pub fn specify(
        &mut self,
        mut a: LocalTypeId,
        info: TypeInfo,
        errors: &mut Errors,
        span: impl FnOnce() -> Span,
    ) {
        let a_ty = loop {
            match self.types[a.idx()] {
                TypeInfoOrIdx::Idx(idx) => a = idx,
                TypeInfoOrIdx::TypeInfo(info) => break info,
            }
        };
        let info = unify(a_ty, info, self).unwrap_or_else(|| {
            let mut expected = String::new();
            self.type_to_string(a_ty, &mut expected);
            let mut found = String::new();
            self.type_to_string(info, &mut found);
            errors.emit_err(Error::MismatchedType { expected, found }.at_span(span()));
            TypeInfo::Invalid
        });
        self.types[a.idx()] = TypeInfoOrIdx::TypeInfo(info);
    }

    pub fn invalidate(&mut self, mut ty: LocalTypeId) {
        loop {
            match self.types[ty.idx()] {
                TypeInfoOrIdx::Idx(idx) => ty = idx,
                TypeInfoOrIdx::TypeInfo(ref mut info) => {
                    *info = TypeInfo::Invalid;
                    break;
                }
            }
        }
    }

    pub fn dump_type(&self, ty: LocalTypeId) {
        let mut s = String::new();
        self.type_to_string(self[ty], &mut s);
        eprint!("{s}");
    }

    pub fn type_to_string(&self, ty: TypeInfo, s: &mut String) {
        use std::fmt::Write;
        // TODO: some of these types could be described better if they could look up symbols
        match ty {
            TypeInfo::Unknown => s.push_str("<unknown>"),
            TypeInfo::Primitive(p) => s.push_str(p.into()),
            TypeInfo::Integer => s.push_str("<integer>"),
            TypeInfo::Float => s.push_str("<float>"),
            TypeInfo::TypeDef(_, _) => s.push_str("<type def>"),
            TypeInfo::Pointer(pointee) => {
                s.push('*');
                self.type_to_string(self[pointee], s);
            }
            TypeInfo::Array { element, count } => {
                s.push('[');
                self.type_to_string(self[element], s);
                s.push_str("; ");
                if let Some(count) = count {
                    write!(s, "{}]", count).unwrap();
                } else {
                    s.push_str("_]");
                }
            }
            TypeInfo::Enum { .. } => s.push_str("<enum>"), // TODO: display variants
            TypeInfo::Tuple(members) => {
                s.push('(');
                let mut first = true;
                for member in members.iter() {
                    if first {
                        first = false;
                    } else {
                        s.push_str(", ");
                    }
                    self.type_to_string(self[member], s);
                }
                if members.iter().count() == 1 {
                    s.push_str(",)");
                } else {
                    s.push(')');
                }
            }
            TypeInfo::TypeItem { ty } => {
                s.push_str("<type item: (");
                self.type_to_string(self[ty], s);
                s.push_str(")>");
            }
            TypeInfo::FunctionItem { .. } => {
                s.push_str("<function item>");
            }
            TypeInfo::ModuleItem(_) => {
                s.push_str("<module item>");
            }
            TypeInfo::MethodItem { .. } => {
                s.push_str("<method item>");
            }
            TypeInfo::Generic(i) => write!(s, "<generic #{i}>").unwrap(),
            TypeInfo::Invalid => s.push_str("<invalid>"),
        }
    }

    pub fn get_info_or_idx(&self, info_or_idx: TypeInfoOrIdx) -> TypeInfo {
        match info_or_idx {
            TypeInfoOrIdx::TypeInfo(info) => info,
            TypeInfoOrIdx::Idx(idx) => self[idx],
        }
    }

    pub fn type_infos_mut(&mut self) -> impl Iterator<Item = &mut TypeInfo> {
        self.types.iter_mut().filter_map(|ty| match ty {
            TypeInfoOrIdx::TypeInfo(info) => Some(info),
            TypeInfoOrIdx::Idx(_) => None,
        })
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TypeInfoOrIdx {
    TypeInfo(TypeInfo),
    Idx(LocalTypeId),
}

fn unify(a: TypeInfo, b: TypeInfo, types: &mut TypeTable) -> Option<TypeInfo> {
    use types::Primitive as P;
    use TypeInfo::*;
    Some(match (a, b) {
        (t, Unknown | Primitive(P::Never)) | (Unknown | Primitive(P::Never), t) => t,
        (Primitive(p_a), Primitive(p_b)) if p_a == p_b => a,
        (Invalid, _) | (_, Invalid) => Invalid,
        (Integer, Integer) => Integer,
        (Float, Float) => Float,
        (Primitive(t), Integer) | (Integer, Primitive(t)) if t.is_int() => Primitive(t),
        (Primitive(t), Float) | (Float, Primitive(t)) if t.is_float() => Primitive(t),
        (TypeDef(id_a, generics_a), TypeDef(id_b, generics_b)) if id_a == id_b => {
            debug_assert_eq!(generics_a.count, generics_b.count);
            for (a, b) in generics_a.iter().zip(generics_b.iter()) {
                if !types.try_unify(a, b) {
                    return None;
                }
            }
            a
        }
        (TypeDef(id, generics), Enum { idx, count })
        | (Enum { idx, count }, TypeDef(id, generics)) => {
            _ = (id, generics, idx, count);
            todo!("unify with enums (requires symbol access)")
        }
        (Enum { idx: a, count: c_a }, Enum { idx: b, count: c_b }) => {
            _ = (a, c_a, b, c_b);
            todo!("unify enums")
        }
        (Pointer(a), Pointer(b)) => {
            if !types.try_unify(a, b) {
                return None;
            }
            Pointer(a)
        }
        (
            Array {
                element: a,
                count: c_a,
            },
            Array {
                element: b,
                count: c_b,
            },
        ) => {
            if !types.try_unify(a, b) {
                return None;
            }
            let count = match (c_a, c_b) {
                (Some(c), None) | (None, Some(c)) => Some(c),
                (None, None) => None,
                (Some(a), Some(b)) => {
                    if a == b {
                        Some(a)
                    } else {
                        return None;
                    }
                }
            };
            Array { element: a, count }
        }
        (Tuple(a), Tuple(b)) => {
            // TODO: reintroduce tuple count mode
            if a.count != b.count {
                return None;
            }
            for (a, b) in a.iter().zip(b.iter()) {
                if !types.try_unify(a, b) {
                    return None;
                }
            }
            Tuple(a)
        }
        (TypeItem { ty: a_ty }, TypeItem { ty: b_ty }) => {
            if !types.try_unify(a_ty, b_ty) {
                return None;
            }
            a
        }
        (
            FunctionItem {
                module: a_m,
                function: a_f,
                generics: a_g,
            },
            FunctionItem {
                module: b_m,
                function: b_f,
                generics: b_g,
            },
        ) if a_m == b_m && a_f == b_f => {
            debug_assert_eq!(
                a_g.count, b_g.count,
                "invalid generics count, incorrect type info constructed"
            );
            for (a, b) in a_g.iter().zip(b_g.iter()) {
                if !types.try_unify(a, b) {
                    return None;
                }
            }
            a
        }
        (
            MethodItem {
                module: a_m,
                function: a_f,
                generics: a_g,
                this_ty: a_t,
            },
            MethodItem {
                module: b_m,
                function: b_f,
                generics: b_g,
                this_ty: b_t,
            },
        ) if a_m == b_m && a_f == b_f => {
            if !types.try_unify(a_t, b_t) {
                return None;
            }
            for (a, b) in a_g.iter().zip(b_g.iter()) {
                types.try_unify(a, b);
            }
            a
        }
        (Generic(a), Generic(b)) if a == b => Generic(a),
        _ => return None,
    })
}

#[derive(Debug, Clone, Copy)]
pub struct LocalTypeIds {
    start: u32,
    pub count: u32,
}
impl LocalTypeIds {
    pub const EMPTY: Self = Self { start: 0, count: 0 };

    pub fn iter(self) -> impl Iterator<Item = LocalTypeId> {
        (self.start..self.start + self.count).map(LocalTypeId)
    }

    pub fn nth(self, i: u32) -> Option<LocalTypeId> {
        (i < self.count).then_some(LocalTypeId(self.start + i))
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
    TypeItem {
        ty: LocalTypeId,
    },
    FunctionItem {
        module: ModuleId,
        function: ast::FunctionId,
        generics: LocalTypeIds,
    },
    ModuleItem(ModuleId),
    MethodItem {
        module: ModuleId,
        function: ast::FunctionId,
        generics: LocalTypeIds,
        this_ty: LocalTypeId,
    },
    Generic(u8),
    Invalid,
}
impl From<Primitive> for TypeInfo {
    fn from(value: Primitive) -> Self {
        TypeInfo::Primitive(value)
    }
}
