use crate::error::*;
use super::*;

#[derive(Clone, Debug)]
pub struct TypeTable {
    types: Vec<TypeInfo>,
    indices: Vec<TypeIdx>
}
impl TypeTable {
    pub fn new() -> Self {
        Self {
            types: Vec::new(),
            indices: Vec::new()
        }
    }

    pub fn get_type(&self, idx: TypeTableIndex) -> (TypeInfo, TypeIdx) {
        let type_idx = self.indices[idx.idx()];
        (self.types[type_idx.get()], type_idx)
    }

    pub fn add(&mut self, info: TypeInfo) -> TypeTableIndex {
        let type_idx = TypeIdx::new(self.types.len());
        self.types.push(info);
        let table_idx = TypeTableIndex::new(self.indices.len() as u32);
        self.indices.push(type_idx);
        table_idx
    }

    pub fn specify(&mut self, idx: TypeTableIndex, info: TypeInfo, errors: &mut Errors) {
        let idx = idx.idx();
        let type_idx = self.indices[idx];
        let ty = &mut self.types[type_idx.get()];
        *ty = match ty.merge(info) {
            Ok(ty) => ty,
            Err(err) => {
                errors.emit(err, 0, 0);
                TypeInfo::Invalid
            }
        };
    }

    pub fn merge(&mut self, a: TypeTableIndex, b: TypeTableIndex, errors: &mut Errors) {
        let a_idx = self.indices[a.idx()];
        let b_idx = &mut self.indices[b.idx()];
        let prev_b_ty = self.types[b_idx.get()];
        *b_idx = a_idx; // make b point to a's type

        let a_ty = &mut self.types[a_idx.get()];
        // merge b's previous type into a
        *a_ty = match a_ty.merge(prev_b_ty) {
            Ok(ty) => ty,
            Err(err) => {
                errors.emit(err, 0, 0);
                TypeInfo::Invalid
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct TypeIdx(u32);
impl TypeIdx {
    fn new(idx: usize) -> Self {
        Self(idx as u32)
    }
    fn get(&self) -> usize {
        self.0 as usize
    }
}


/// A type that may not be (completely) known yet. 
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TypeInfo {
    Unknown,
    Int,
    Float,
    Func(SymbolKey),
    Type(SymbolKey),
    Primitive(Primitive),
    Resolved(SymbolKey),
    Invalid,
}
impl fmt::Display for TypeInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeInfo::Unknown => write!(f, "{{unknown}}"),
            TypeInfo::Int => write!(f, "{{int}}"),
            TypeInfo::Float => write!(f, "{{float}}"),
            TypeInfo::Func(key) => write!(f, "{{func {}}}", key.idx()),
            TypeInfo::Type(key) => write!(f, "{{type-type {}}}", key.idx()),
            TypeInfo::Primitive(p) => write!(f, "{p}"),
            TypeInfo::Resolved(key) => write!(f, "{{type {}}}", key.idx()),
            TypeInfo::Invalid => write!(f, "{{invalid}}"),
        }
    }
}
impl TypeInfo {
    fn merge(&self, other: TypeInfo) -> Result<Self, Error> {
        self.merge_is_other(other, false)
    }

    fn merge_is_other(&self, other: TypeInfo, is_other: bool) -> Result<Self, Error> {
        let res = match self {
            Self::Unknown => Ok(other),
            Self::Int => {
                match other {
                    Self::Int => Ok(other),
                    Self::Primitive(p) if p.as_int().is_some() => Ok(other),
                    Self::Unknown => Ok(Self::Int),
                    _ => Err(Error::IntExpected)
                }
            }
            Self::Float => {
                match other {
                    Self::Float => Ok(other),
                    Self::Primitive(p) if p.as_float().is_some() => Ok(other),
                    Self::Unknown => Ok(Self::Float),
                    _ => Err(Error::FloatExpected)
                }
            }
            TypeInfo::Primitive(_) | TypeInfo::Resolved(_) | TypeInfo::Func(_) | TypeInfo::Type(_) => {
                (other == *self)
                    .then(|| *self)
                    .ok_or(Error::MismatchedType)
            }
            TypeInfo::Invalid => Ok(*self), // invalid type 'spreading'
        };
        match res {
            Ok(t) => Ok(t),
            Err(err) => if is_other {
                crate::log!("Merge failed {self:?} {other:?}");
                Err(err)
            } else {
                other.merge_is_other(*self, true)
            }
        }
    }
}
impl From<TypeRef> for TypeInfo {
    fn from(ty: TypeRef) -> Self {
        match ty {
            TypeRef::Primitive(p) => Self::Primitive(p),
            TypeRef::Resolved(r) => Self::Resolved(r),
            TypeRef::Invalid => Self::Invalid,
        }
    }
}