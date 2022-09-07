use std::{ops::Index, borrow::Cow};

use crate::{error::*, ast::ModuleId, span::{TSpan, Span}};
use super::{*, gen::TypingCtx};

/// Type inference debugging
fn ty_dbg<D: std::fmt::Debug>(msg: &str, d: D) -> D {
    if crate::DEBUG_INFER.load(std::sync::atomic::Ordering::Relaxed) {
        println!("[TypeInfer] {msg}: {d:?}");
    }
    d
}

#[derive(Clone, Debug)]
pub struct TypeTable {
    types: Vec<TypeInfo>,
    indices: Vec<TypeIdx>,
    names: Vec<String>,
}
impl TypeTable {
    pub fn new() -> Self {
        ty_dbg("Creating type table", ());
        Self {
            types: Vec::new(),
            indices: Vec::new(),
            names: Vec::new(),
        }
    }

    pub fn get_type(&self, idx: TypeTableIndex) -> TypeInfo {
        let type_idx = self.indices[idx.idx()];
        self.types[type_idx.get()]
    }
    
    pub fn update_type(&mut self, idx: TypeTableIndex, info: TypeInfo) {
        self.types[self.indices[idx.idx()].get()] = info;
    }

    // Points a to the index that b is pointing to
    pub fn point_to(&mut self, a: TypeTableIndex, b: TypeTableIndex) {
        self.indices[a.idx()] = self.indices[b.idx()];
    }

    pub fn add(&mut self, info: TypeInfo) -> TypeTableIndex {
        let type_idx = TypeIdx(self.types.len() as u32);
        self.types.push(info);
        let table_idx = TypeTableIndex(self.indices.len() as u32);
        self.indices.push(type_idx);
        ty_dbg("Adding", &(info, type_idx));
        table_idx
    }

    pub fn add_info_or_idx(&mut self, ty: TypeInfoOrIndex) -> TypeTableIndex {
        match ty {
            TypeInfoOrIndex::Info(info) => self.add(info),
            TypeInfoOrIndex::Index(idx) => idx
        }
    }

    pub fn add_multiple(&mut self, infos: impl IntoIterator<Item = TypeInfo>) -> TypeTableIndices {
        let infos = infos.into_iter();
        let start_ty_idx = self.types.len() as u32;
        self.types.extend(infos);
        let count = (self.types.len() - start_ty_idx as usize) as u32;
        let idx = self.indices.len() as u32;
        self.indices.extend((start_ty_idx .. start_ty_idx+count).map(TypeIdx));
        TypeTableIndices { idx, count }
    }
    pub fn add_multiple_info_or_index(&mut self, types: impl IntoIterator<Item = TypeInfoOrIndex>)
    -> TypeTableIndices {
        let types = types.into_iter();
        let idx = self.indices.len() as u32;
        let mut count = 0;
        for ty in types {
            count += 1;
            let idx = match ty {
                TypeInfoOrIndex::Info(info) => {
                    let idx = TypeIdx(self.types.len() as u32);
                    self.types.push(info);
                    idx
                }
                TypeInfoOrIndex::Index(idx) => {
                    self.indices[idx.idx()]
                }
            };
            self.indices.push(idx);
        }
        TypeTableIndices { idx, count }
    }

    pub fn add_unknown(&mut self) -> TypeTableIndex {
        self.add(TypeInfo::Unknown)
    }

    pub fn specify(&mut self, idx: TypeTableIndex, other: TypeInfo, errors: &mut Errors, span: Span, ctx: &TypingCtx) {
        let prev = self.get_type(idx);
        ty_dbg("Specifying", (prev, idx, other));
        let ty = merge_twosided(prev, other, self, ctx).unwrap_or_else(|| {
            errors.emit_span(Error::MismatchedType {
                expected: prev.to_string(self, ctx).into_owned(),
                found: other.to_string(self, ctx).into_owned()
            }, span);
            TypeInfo::Invalid
        });
        self.update_type(idx, ty);
    }
    pub fn specify_or_merge(
        &mut self,
        idx: TypeTableIndex,
        other: TypeInfoOrIndex,
        errors: &mut Errors,
        module: ModuleId,
        span: TSpan,
        ctx: &TypingCtx,
    ) {
        match other {
            TypeInfoOrIndex::Info(info) => self.specify(idx, info, errors, span.in_mod(module), ctx),
            TypeInfoOrIndex::Index(other_idx) => self.merge(idx, other_idx, errors, module, span, ctx),
        }
    }

    pub fn merge(&mut self, a: TypeTableIndex, b: TypeTableIndex,
        errors: &mut Errors, module: ModuleId, span: TSpan, ctx: &TypingCtx
    ) {
        let a_idx = self.indices[a.idx()];
        let a_ty = self.types[a_idx.get()];
        let b_idx = &mut self.indices[b.idx()];
        let prev_b_ty = self.types[b_idx.get()];
        ty_dbg("Merging ...", ((a_ty, a_idx, a), (prev_b_ty, *b_idx, b)));
        *b_idx = a_idx; // make b point to a's type


        // merge b's previous type into a
        self.types[a_idx.get()] = match merge_twosided(a_ty, prev_b_ty, self, ctx) {
            Some(ty) => ty_dbg("\t... merged", ty),
            None => {
                ty_dbg("\t... failed to merge", span);
                errors.emit_span(Error::MismatchedType {
                    expected: a_ty.to_string(self, ctx).into_owned(),
                    found: prev_b_ty.to_string(self, ctx).into_owned()
                }, span.in_mod(module));
                TypeInfo::Invalid
            }
        }
    }

    pub fn add_names(&mut self, names: impl IntoIterator<Item = String>) -> TypeTableNames {
        let idx = self.names.len();
        self.names.extend(names);
        TypeTableNames { idx: idx as u32, count: (self.names.len() - idx) as u32 }
    }
    pub fn _remove_names(&mut self, names: TypeTableNames) {
        self.names.drain(names.idx as usize .. names.idx as usize + names.count as usize);
    }

    pub fn get_names(&self, names: TypeTableNames) -> &[String] {
        &self.names[names.idx as usize .. names.idx as usize + names.count as usize]
    }
    #[must_use = "Range should be used to update"]
    pub fn extend_names(&mut self, idx: TypeTableNames, names: impl IntoIterator<Item = String>) -> TypeTableNames {
        let prev_len = self.names.len();
        let insert_at = idx.idx as usize + idx.count as usize;
        self.names.splice(insert_at..insert_at, names);
        TypeTableNames { idx: idx.idx, count: idx.count + (self.names.len() - prev_len) as u32 }
    }

    pub fn finalize(self) -> FinalTypeTable {
        let types = self.indices.iter()
            .map(|&i| self.types[i.0 as usize].finalize(&self))
            .collect();
        FinalTypeTable { types }
    }
}
impl Index<TypeTableIndex> for TypeTable {
    type Output = TypeInfo;

    fn index(&self, index: TypeTableIndex) -> &Self::Output {
        &self.types[self.indices[index.idx()].0 as usize]
    }
}
impl Drop for TypeTable {
    fn drop(&mut self) {
        ty_dbg("Dropping Type Table: ", self);
    }
}

#[derive(Clone, Copy, Debug)]
pub struct TypeTableIndex(pub u32);
impl TypeTableIndex {
    pub const NONE: Self = Self(u32::MAX);
    pub fn idx(self) -> usize { self.0 as usize }
    pub fn is_present(self) -> bool { self.0 != u32::MAX }
}

#[derive(Clone, Copy, Debug)]
pub struct TypeTableIndices {
    idx: u32,
    count: u32
}
impl TypeTableIndices {
    pub const EMPTY: Self = Self { idx: 0, count: 0 };

    pub fn iter(self) -> impl Iterator<Item = TypeTableIndex> {
        (self.idx .. self.idx + self.count).map(TypeTableIndex)
    }
    pub fn nth(self, index: usize) -> TypeTableIndex {
        assert!(index < self.count as usize);
        TypeTableIndex(self.idx + index as u32)
    }
    pub fn len(self) -> usize { self.count as usize }
}

#[derive(Clone, Copy, Debug)]
pub struct TypeTableNames {
    idx: u32,
    count: u32
}

#[derive(Debug)]
pub struct FinalTypeTable {
    types: Vec<Type>
}
impl FinalTypeTable {
    pub fn get(&self, idx: TypeTableIndex) -> &Type {
        assert!(idx.0 != u32::MAX, "Tried to get none-type table index");
        // for generic types this will get a bit more complicated but the base
        // principle of indexing into the Vec should stay
        &self.types[idx.idx()]
    }
}
impl Index<TypeTableIndex> for FinalTypeTable {
    type Output = Type;

    fn index(&self, index: TypeTableIndex) -> &Self::Output {
        &self.types[index.idx()]
    }
}

#[derive(Clone, Copy, Debug)]
struct TypeIdx(u32);
impl TypeIdx {
    fn get(self) -> usize {
        self.0 as usize
    }
}


/// A type that may not be (completely) known yet.
#[derive(Clone, Copy, Debug)]
pub enum TypeInfo {
    Unknown,
    Int,
    Float,
    Primitive(Primitive),
    Resolved(SymbolKey, TypeTableIndices),
    Pointer(TypeTableIndex),
    Array(Option<u32>, TypeTableIndex),
    Enum(TypeTableNames),
    Tuple(TypeTableIndices),
    Symbol, // compile time Symbol like a function, type or trait
    Generic(u8), // a type that is not instanciated to a specific type yet.
    Invalid,
}
impl TypeInfo {
    pub const UNIT: Self = Self::Primitive(Primitive::Unit);
    
    fn to_string(&self, types: &TypeTable, ctx: &TypingCtx) -> Cow<'static, str> {
        match self {
            TypeInfo::Unknown => "<unknown>".into(),
            TypeInfo::Int => "<integer>".into(),
            TypeInfo::Float => "<float>".into(),
            TypeInfo::Primitive(p) => Into::<&'static str>::into(*p).into(),
            TypeInfo::Resolved(id, generics) => {
                let mut generics_string = String::new();
                if generics.count > 0 {
                    generics_string.push('<');
                    for (i, generic) in generics.iter().enumerate() {
                        let generic = types[generic];
                        generics_string += &*generic.to_string(types, ctx);
                        if i != generics.len() - 1 {
                            generics_string += ", ";
                        }
                    }
                    generics_string.push('>');
                }
                format!("{}{}", ctx.get_type(*id), generics_string).into()
            }
            TypeInfo::Pointer(inner) => format!("*{}", types[*inner].to_string(types, ctx)).into(),
            TypeInfo::Array(count, inner) => format!("[{}; {}]",
                types[*inner].to_string(types, ctx),
                count.map_or("_".to_owned(), |c| c.to_string())
            ).into(),
            TypeInfo::Enum(variants) => {
                let mut s = "[".to_owned();
                for (i, t) in types.get_names(*variants).iter().enumerate() {
                    s += t;
                    if i != variants.count as usize - 1 {
                        s += ", ";
                    }
                }
                s.push(']');
                s.into()
            }
            TypeInfo::Tuple(_) => todo!(),
            TypeInfo::Symbol => todo!(),
            TypeInfo::Generic(_) => todo!(),
            TypeInfo::Invalid => todo!(),
        }
    }
    pub fn is_invalid(&self) -> bool {
        matches!(self, TypeInfo::Invalid)
    }
    fn finalize(self, types: &TypeTable) -> Type {
        match self {
            Self::Unknown | Self::Invalid => Type::Prim(Primitive::Unit),
            Self::Int => Type::Prim(Primitive::I32),
            Self::Float => Type::Prim(Primitive::F32),
            Self::Primitive(p) => Type::Prim(p),
            Self::Resolved(id, generics) => {
                let generic_types = generics.iter()
                    .map(|ty| types.get_type(ty).finalize(types))
                    .collect();
                Type::Id(id, generic_types)
            }
            Self::Pointer(inner) => Type::Pointer(Box::new(types.get_type(inner).finalize(types))),
            Self::Array(size, inner) => {
                let inner = types.get_type(inner).finalize(types);
                size.map_or(
                    Type::Prim(Primitive::Unit),
                    |size| Type::Array(Box::new((inner, size)))
                )
            }
            Self::Enum(idx) => {
                Type::Enum(types.get_names(idx).to_vec())
            }
            Self::Tuple(indices) => {
                Type::Tuple(indices.iter().map(|ty| types.get_type(ty).finalize(types)).collect())
            }
            Self::Symbol => {
                Type::Symbol
            }
            Self::Generic(i) => Type::Generic(i),
        }
    }
}

fn merge_twosided(ty: TypeInfo, other: TypeInfo, types: &mut TypeTable, ctx: &TypingCtx) -> Option<TypeInfo> {
    match merge_onesided(ty, other, types, ctx) {
        Some(t) => Some(t),
        None => merge_onesided(other, ty, types, ctx)
    }
}

/// merge the types and return the merged type
fn merge_onesided(ty: TypeInfo, other: TypeInfo, types: &mut TypeTable, ctx: &TypingCtx) -> Option<TypeInfo> {
    use TypeInfo::*;
    match ty {
        Unknown => Some(other),
        Primitive(crate::types::Primitive::Never) => Some(other),
        Int => {
            match other {
                Int => Some(other),
                Primitive(p) if p.as_int().is_some() => Some(other),
                Unknown => Some(Int),
                _ => None
            }
        }
        Float => {
            match other {
                Float => Some(other),
                Primitive(p) if p.as_float().is_some() => Some(other),
                Unknown => Some(Float),
                _ => None
            }
        }
        Primitive(prim) => {
            if let Primitive(other) = other {
                prim == other
            } else { false }
                .then_some(ty)
        }
        Resolved(id, generics) => {
            if let Resolved(other, other_generics) = other {
                id == other && {
                    debug_assert_eq!(generics.count, other_generics.count);
                    generics.iter()
                        .zip(other_generics.iter())
                        .map(|(a, b)| {
                            let new = merge_onesided(types[a], types[b], types, ctx)?;
                            types.update_type(a, new);
                            types.point_to(b, a);
                            Some(())
                        })
                        .all(|v| v.is_some())
                }
            } else if let TypeDef::Enum(def) = ctx.get_type(id) {
                if let Enum(names) = other {
                    !types.get_names(names).iter()
                        .any(|name| !def.variants.contains_key(name))
                } else { false }
            } else { false }
                .then_some(ty)
        }
        Pointer(inner) => {
            let Pointer(other_inner) = other else { return None };
            let new_inner = merge_onesided(types.get_type(inner), types.get_type(other_inner), types, ctx)?;
            types.update_type(inner, new_inner);
            types.point_to(other_inner, inner);
            Some(Pointer(inner))
        }
        Array(size, inner) => {
            let Array(other_size, other_inner) = other else { return None };
    
            let new_inner = merge_onesided(types.get_type(inner), types.get_type(other_inner), types, ctx)?;
            types.update_type(inner, new_inner);
            types.point_to(other_inner, inner);
            
            let new_size = match (size, other_size) {
                (Some(a), Some(b)) if a == b => Some(a),
                (Some(size), None) | (None, Some(size)) => Some(size),
                (None, None) => None,
                _ => return None
            };
            Some(Array(new_size, inner))
                
        }
        Enum(names) => {
            let Enum(other_names) = other else { return None };
            let a = types.get_names(names);
            let b = types.get_names(other_names);
            let new_variants: Vec<_> = b.iter().filter(|s| !a.contains(s)).cloned().collect();
            ty_dbg("New variants after merging", (&new_variants, a, b));
            let merged_variants = types.extend_names(names, new_variants);
            Some(Enum(merged_variants))
        }
        Tuple(elems) => {
            let Tuple(other_elems) = other else { return None };
            if elems.count != other_elems.count { return None }
            for (a, b) in elems.iter().zip(other_elems.iter()) {
                let new_a = merge_onesided(types.get_type(a), types.get_type(b), types, ctx)?;
                types.update_type(a, new_a);
                types.point_to(b, a);
            }
            Some(ty)
        
        }
        Symbol => if let Symbol = other {
            Some(ty)
        } else {
            None
        }
        Generic(i) => if let Generic(j) = other {
            if i == j {
                Some(ty)
            } else {
                None
            }
        } else {
            None
        }
        Invalid => Some(Invalid), // invalid type 'spreading'
    }
}
