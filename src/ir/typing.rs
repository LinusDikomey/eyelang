use std::ops::Index;

use crate::{error::*, ast::{ModuleId, TSpan}, lexer::Span};
use super::*;

/// Type inference debugging
fn ty_dbg<D: std::fmt::Debug>(msg: &str, d: D) -> D {
    #[cfg(feature = "debug_types")]
    println!("[TypeInfer] {msg}: {d:?}");
    #[cfg(not(feature = "debug_types"))]
    { _ = msg; }
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
    fn point_to(&mut self, a: TypeTableIndex, b: TypeTableIndex) {
        self.indices[a.idx()] = self.indices[b.idx()];
    }

    pub fn add(&mut self, info: TypeInfo) -> TypeTableIndex {
        let type_idx = TypeIdx::new(self.types.len());
        self.types.push(info);
        let table_idx = TypeTableIndex::new(self.indices.len() as u32);
        self.indices.push(type_idx);
        ty_dbg("Adding", &(info, type_idx));
        table_idx
    }

    pub fn add_unknown(&mut self) -> TypeTableIndex {
        self.add(TypeInfo::Unknown)
    }

    pub fn specify(&mut self, idx: TypeTableIndex, other: TypeInfo, errors: &mut Errors, span: Span) {
        let prev = self.get_type(idx);
        ty_dbg("Specifying", (prev, idx, other));
        let ty = merge_twosided(prev, other, self).unwrap_or_else(|err| {
            errors.emit_span(err, span);
            TypeInfo::Invalid
        });
        self.update_type(idx, ty);
    }

    pub fn merge(&mut self, a: TypeTableIndex, b: TypeTableIndex, errors: &mut Errors, module: ModuleId, span: TSpan) {
        let a_idx = self.indices[a.idx()];
        let a_ty = self.types[a_idx.get()];
        let b_idx = &mut self.indices[b.idx()];
        let prev_b_ty = self.types[b_idx.get()];
        ty_dbg("Merging", (a_ty, prev_b_ty, a_idx, *b_idx));
        *b_idx = a_idx; // make b point to a's type


        // merge b's previous type into a
        self.types[a_idx.get()] = match merge_twosided(a_ty, prev_b_ty, self) {
            Ok(ty) => ty,
            Err(err) => {
                errors.emit_span(err,span.in_mod(module));
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
    fn new(idx: usize) -> Self {
        Self(idx as u32)
    }
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
    Resolved(SymbolKey),
    Pointer(TypeTableIndex),
    Array(Option<u32>, TypeTableIndex),
    Enum(TypeTableNames),
    Invalid,
}
impl TypeInfo {
    pub fn is_invalid(&self) -> bool {
        matches!(self, TypeInfo::Invalid)
    }
    fn finalize(self, types: &TypeTable) -> Type {
        match self {
            Self::Unknown | Self::Invalid => Type::Prim(Primitive::Unit),
            Self::Int => Type::Prim(Primitive::I32),
            Self::Float => Type::Prim(Primitive::F32),
            Self::Primitive(p) => Type::Prim(p),
            Self::Resolved(id) => Type::Id(id),
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
        }
    }
}

fn merge_twosided(ty: TypeInfo, other: TypeInfo, types: &mut TypeTable) -> Result<TypeInfo, Error> {
    match merge_onesided(ty, other, types) {
        Ok(t) => Ok(t),
        Err(_) => merge_onesided(other, ty, types)
    }
}

/// merge the types and return the merged type
fn merge_onesided(ty: TypeInfo, other: TypeInfo, types: &mut TypeTable) -> Result<TypeInfo, Error> {
    use TypeInfo::*;
    match ty {
        Unknown => Ok(other),
        Int => {
            match other {
                Int => Ok(other),
                Primitive(p) if p.as_int().is_some() => Ok(other),
                Unknown => Ok(Int),
                _ => Err(Error::MismatchedType)
            }
        }
        Float => {
            match other {
                Float => Ok(other),
                Primitive(p) if p.as_float().is_some() => Ok(other),
                Unknown => Ok(Float),
                _ => Err(Error::MismatchedType)
            }
        }
        Primitive(prim) => {
            if let Primitive(other) = other {
                prim == other
            } else { false }
                .then(|| ty)
                .ok_or(Error::MismatchedType)
        } | Resolved(id) => {
            if let Resolved(other) = other {
                id == other
            } else { false }
                .then(|| ty)
                .ok_or(Error::MismatchedType)
        }
        Pointer(inner) => {
            match other {
                Pointer(other_inner) => {
                    let new_inner = merge_onesided(types.get_type(inner), types.get_type(other_inner), types)?;
                    types.update_type(inner, new_inner);
                    types.point_to(other_inner, inner);
                    Ok(Pointer(inner))
                }
                _ => Err(Error::MismatchedType)
            }
        }
        Array(size, inner) => {
            match other {
                Array(other_size, other_inner) => {
                    let new_inner = merge_onesided(types.get_type(inner), types.get_type(other_inner), types)?;
                    types.update_type(inner, new_inner);
                    types.point_to(other_inner, inner);
                    
                    let new_size = match (size, other_size) {
                        (Some(a), Some(b)) if a == b => Some(a),
                        (Some(size), None) | (None, Some(size)) => Some(size),
                        (None, None) => None,
                        _ => return Err(Error::MismatchedType)
                    };
                    Ok(Array(new_size, inner))
                }
                _ => Err(Error::MismatchedType)
            }
        }
        Enum(names) => {
            if let Enum(other_names) = other {
                let a = types.get_names(names);
                let b = types.get_names(other_names);
                let new_variants: Vec<_> = b.iter().filter(|s| !a.contains(s)).cloned().collect();
                let new_variants = types.extend_names(names, new_variants);
                Ok(Enum(new_variants))
            } else {
                Err(Error::MismatchedType)
            }
        }
        Invalid => Ok(Invalid), // invalid type 'spreading'
    }
}
