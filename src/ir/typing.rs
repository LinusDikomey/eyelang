use crate::{error::*, ast::ModuleId};
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
    indices: Vec<TypeIdx>
}
impl TypeTable {
    pub fn new() -> Self {
        ty_dbg("Creating type table", ());
        Self {
            types: Vec::new(),
            indices: Vec::new()
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

    pub fn specify(&mut self, idx: TypeTableIndex, other: TypeInfo, errors: &mut Errors, module: ModuleId) {
        let prev = self.get_type(idx);
        ty_dbg("Specifying", (prev, idx, other));
        let ty = merge_twosided(prev, other, self).unwrap_or_else(|err| {
            errors.emit(err, 0, 0, module);
            TypeInfo::Invalid
        });
        self.update_type(idx, ty);
    }

    pub fn merge(&mut self, a: TypeTableIndex, b: TypeTableIndex, errors: &mut Errors, module: ModuleId) {
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
                errors.emit(err, 0, 0, module);
                TypeInfo::Invalid
            }
        }
    }

    pub fn finalize(self) -> FinalTypeTable {
        let types = self.indices.iter()
            .map(|&i| self.types[i.0 as usize].finalize(&self))
            .collect();
        FinalTypeTable { types }
    }
}

pub struct FinalTypeTable {
    types: Vec<Type>
}
impl FinalTypeTable {
    pub fn get(&self, idx: TypeTableIndex) -> Type {
        assert!(idx.0 != u32::MAX, "Tried to get none-type table index");
        // for generic types this will get a bit more complicated but the base
        // principle of indexing into the Vec should stay
        self.types[idx.idx()]
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
    Invalid,
}
impl TypeInfo {
    fn finalize(self, types: &TypeTable) -> Type {
        match self {
            Self::Unknown | Self::Invalid => Type::Base(BaseType::Prim(Primitive::Unit)),
            Self::Int => Type::Base(BaseType::Prim(Primitive::I32)),
            Self::Float => Type::Base(BaseType::Prim(Primitive::F32)),
            Self::Primitive(p) => Type::Base(BaseType::Prim(p)),
            Self::Resolved(id) => Type::Base(BaseType::Id(id)),
            Self::Pointer(inner) => {
                let inner = types.get_type(inner).finalize(types);
                inner.pointer_to().expect("A pointer was too large. TODO: handle this properly")
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
                _ => Err(Error::IntExpected)
            }
        }
        Float => {
            match other {
                Float => Ok(other),
                Primitive(p) if p.as_float().is_some() => Ok(other),
                Unknown => Ok(Float),
                _ => Err(Error::FloatExpected)
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
                    //TODO: if the type hasn't changed, no new type has to be added
                    types.update_type(inner, new_inner);
                    types.point_to(other_inner, inner);
                    Ok(Pointer(inner))
                }
                _ => Err(Error::MismatchedType)
            }
        }
        Invalid => Ok(Invalid), // invalid type 'spreading'
    }
}
