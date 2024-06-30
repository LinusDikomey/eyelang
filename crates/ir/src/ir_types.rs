use std::{num::NonZeroU64, ops::Index};

use crate::Layout;

#[derive(Debug)]
pub struct IrTypes {
    types: Vec<IrType>,
}
impl IrTypes {
    pub fn new() -> Self {
        Self { types: vec![] }
    }

    pub fn add(&mut self, ty: IrType) -> TypeRef {
        self.types.push(ty);
        TypeRef((self.types.len() - 1) as u32)
    }

    pub fn add_multiple(&mut self, types: impl IntoIterator<Item = IrType>) -> TypeRefs {
        let start = self.types.len();
        self.types.extend(types);
        TypeRefs {
            idx: start as _,
            count: (self.types.len() - start) as _,
        }
    }

    pub fn replace(&mut self, idx: TypeRef, ty: IrType) {
        self.types[idx.idx()] = ty;
    }

    pub fn layout(&self, ty: IrType) -> Layout {
        match ty {
            IrType::Unit | IrType::Const(_) | IrType::Array(_, 0) => Layout::EMPTY,
            IrType::U1 | IrType::I8 | IrType::U8 => Layout {
                size: 1,
                align: NonZeroU64::new(1).unwrap(),
            },
            IrType::I16 | IrType::U16 => Layout {
                size: 2,
                align: NonZeroU64::new(2).unwrap(),
            },
            IrType::I32 | IrType::U32 | IrType::F32 => Layout {
                size: 4,
                align: NonZeroU64::new(4).unwrap(),
            },
            IrType::I64 | IrType::U64 | IrType::F64 => Layout {
                size: 8,
                align: NonZeroU64::new(8).unwrap(),
            },
            IrType::I128 | IrType::U128 => Layout {
                size: 16,
                align: NonZeroU64::new(16).unwrap(),
            },
            IrType::Ptr => Layout::PTR,
            IrType::Array(elem, count) => Layout::array(self.layout(self[elem]), count as u64),
            IrType::Tuple(elems) => {
                let mut layout = Layout::EMPTY;
                for elem in elems.iter() {
                    layout.accumulate(self.layout(self[elem]));
                }
                layout
            }
        }
    }

    pub fn are_equal(&self, a: IrType, b: IrType) -> bool {
        match a {
            IrType::Unit => matches!(b, IrType::Unit),
            IrType::I8 => matches!(b, IrType::I8),
            IrType::I16 => matches!(b, IrType::I16),
            IrType::I32 => matches!(b, IrType::I32),
            IrType::I64 => matches!(b, IrType::I64),
            IrType::I128 => matches!(b, IrType::I128),
            IrType::U8 => matches!(b, IrType::U8),
            IrType::U16 => matches!(b, IrType::U16),
            IrType::U32 => matches!(b, IrType::U32),
            IrType::U64 => matches!(b, IrType::U64),
            IrType::U128 => matches!(b, IrType::U128),
            IrType::F32 => matches!(b, IrType::F32),
            IrType::F64 => matches!(b, IrType::F64),
            IrType::U1 => matches!(b, IrType::U1),
            IrType::Ptr => matches!(b, IrType::Ptr),
            IrType::Array(elem_a, size_a) => {
                let IrType::Array(elem_b, size_b) = b else {
                    return false;
                };
                if size_a != size_b {
                    return false;
                }
                return self.are_equal(self[elem_a], self[elem_b]);
            }
            IrType::Tuple(a) => {
                let IrType::Tuple(b) = b else { return false };
                if a.count != b.count {
                    return false;
                }
                a.iter()
                    .zip(b.iter())
                    .all(|(a, b)| self.are_equal(self[a], self[b]))
            }
            IrType::Const(a) => {
                let IrType::Const(b) = b else {
                    return false;
                };
                a == b
            }
        }
    }
}

impl Index<TypeRef> for IrTypes {
    type Output = IrType;

    fn index(&self, index: TypeRef) -> &Self::Output {
        &self.types[index.0 as usize]
    }
}

#[derive(Clone, Copy, Debug)]
pub enum IrType {
    // ---------- scalar types ----------
    Unit,
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
    F32,
    F64,
    U1,
    Ptr,

    // ---------- aggregate types ----------
    Array(TypeRef, u32),
    Tuple(TypeRefs),

    /// constant type, used only during const evaluation (might get removed)
    Const(ConstIrType),
}
impl IrType {
    pub fn is_int(self) -> bool {
        use IrType as T;
        matches!(self, |T::I8| T::I16
            | T::I32
            | T::I64
            | T::I128
            | T::U8
            | T::U16
            | T::U32
            | T::U64
            | T::U128
            | T::U1)
    }

    pub fn is_unsigned_int(self) -> bool {
        use IrType as T;
        matches!(self, |T::U8| T::U16 | T::U32 | T::U64 | T::U128 | T::U1)
    }

    pub fn is_signed_int(self) -> bool {
        use IrType as T;
        matches!(self, |T::I8| T::I16 | T::I32 | T::I64 | T::I128)
    }

    pub fn is_float(self) -> bool {
        matches!(self, IrType::F32 | IrType::F64)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstIrType {
    Int,
    Float,
    Enum,
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
    pub fn to_bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }
    pub fn from_bytes(bytes: [u8; 4]) -> Self {
        Self(u32::from_le_bytes(bytes))
    }
}

#[derive(Clone, Copy, Debug)]
pub struct TypeRefs {
    pub idx: u32,
    pub count: u32,
}
impl From<TypeRef> for TypeRefs {
    fn from(value: TypeRef) -> Self {
        Self {
            idx: value.0,
            count: 1,
        }
    }
}
impl TypeRefs {
    pub const EMPTY: Self = Self { idx: 0, count: 0 };

    pub fn is_empty(self) -> bool {
        self.count == 0
    }

    pub fn from_single(r: TypeRef) -> Self {
        Self { idx: r.0, count: 1 }
    }

    pub fn iter(self) -> impl Iterator<Item = TypeRef> {
        (self.idx..self.idx + self.count).map(TypeRef)
    }

    pub fn len(self) -> usize {
        self.count as usize
    }

    pub fn nth(self, idx: u32) -> TypeRef {
        debug_assert!(idx < self.count);
        TypeRef(self.idx + idx)
    }

    pub fn to_bytes(self) -> [u8; 8] {
        let a = self.idx.to_le_bytes();
        let b = self.count.to_le_bytes();
        [a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]]
    }

    pub fn from_bytes(bytes: [u8; 8]) -> Self {
        let mut a = [0; 4];
        a.copy_from_slice(&bytes[0..4]);
        let idx = u32::from_le_bytes(a);
        a.copy_from_slice(&bytes[4..8]);
        let count = u32::from_le_bytes(a);
        Self { idx, count }
    }
}
