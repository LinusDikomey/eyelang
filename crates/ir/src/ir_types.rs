use std::ops::Index;


#[derive(Debug)]
pub struct IrTypes {
    types: Vec<IrType>,
}
impl IrTypes {
    pub fn new() -> Self {
        Self {
            types: vec![],
        }
    }

    pub fn add(&mut self, ty: IrType) -> TypeRef {
        self.types.push(ty);
        TypeRef((self.types.len() - 1) as u32)
    }

    pub fn add_multiple(&mut self, types: impl IntoIterator<Item = IrType>) -> TypeRefs {
        let start = self.types.len();
        self.types.extend(types);
        TypeRefs { idx: start as _, count: (self.types.len() - start) as _ }
    }

    pub fn replace(&mut self, idx: TypeRef, ty: IrType) {
        self.types[idx.idx()] = ty;
    }
    
    /*
    #[allow(clippy::wrong_self_convention)]
    pub fn from_resolved(&mut self, ty: &Type, on_generic: TypeRefs) -> IrType {
        let add_tuple = |s: &mut IrTypes, elems: &[Type]| -> TypeRefs {
            let idx = s.types.len() as u32;
            s.types.extend((0..elems.len()).map(|_| IrType::Primitive(Primitive::Unit)));

            for (i, ty) in elems.iter().enumerate() {
                s.types[idx as usize + i] = s.from_resolved(ty, on_generic);
            }
            TypeRefs { idx, count: elems.len() as _ }
        };
        match ty {
            Type::Prim(p) => IrType::Primitive(*p),
            Type::Id(id, generics) => {
                let generic_idx = self.types.len() as u32;
                self.types.extend(std::iter::repeat(IrType::Primitive(Primitive::Never)).take(generics.len()));
                
                for (i, ty) in generics.iter().enumerate() {
                    self.types[generic_idx as usize + i] = self.from_resolved(ty, on_generic);
                }
                IrType::Id(*id, TypeRefs { idx: generic_idx, count: generics.len() as _ })
            }
            Type::Pointer(inner) => {
                let inner = self.from_resolved(inner, on_generic);
                IrType::Ptr(self.add(inner))
            }
            Type::Array(b) => {
                let elem_ty = self.from_resolved(&b.0, on_generic);
                IrType::Array(self.add(elem_ty), b.1)
            }
            Type::Tuple(elems) => {
                IrType::Tuple(add_tuple(self, elems))
            }
            Type::Generic(i) => IrType::Ref(on_generic.nth(*i as _)),
            Type::LocalEnum(variants) => {
                let idx = self.types.len() as u32;
                self.types.extend(std::iter::repeat(IrType::Primitive(Primitive::Never)).take(variants.len()));

                for (i, args) in variants.iter().enumerate() {
                    self.types[idx as usize + i] = IrType::Tuple(add_tuple(self, args));
                }

                IrType::Enum(TypeRefs { idx, count: variants.len() as _ })
            }
            Type::TraitSelf => unreachable!(),
            Type::Invalid => unreachable!("invalid 'Type' encountered during irgen"),
        }
    }

    pub fn layout<'a, F: Fn(TypeId) -> &'a ResolvedTypeDef + Copy>(&'a self, ty: IrType, get_type: F) -> Layout {
        ty.layout(self, get_type)
    }
    */
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
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
    F32, F64,
    U1,
    Unit,
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
        matches!(
            self,
            | T::I8 | T::I16 | T::I32 | T::I64 | T::I128
            | T::U8 | T::U16 | T::U32 | T::U64 | T::U128
            | T::U1
        )
    }

    pub fn is_unsigned_int(self) -> bool {
        use IrType as T;
        matches!(
            self,
            | T::U8 | T::U16 | T::U32 | T::U64 | T::U128
            | T::U1
        )
    }

    pub fn is_signed_int(self) -> bool {
        use IrType as T;
        matches!(
            self,
            | T::I8 | T::I16 | T::I32 | T::I64 | T::I128
        )
    }

    pub fn is_float(self) -> bool {
        matches!(self, IrType::F32 | IrType::F64)
    }
}

#[derive(Clone, Copy, Debug)]
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
}

#[derive(Clone, Copy, Debug)]
pub struct TypeRefs { pub idx: u32, pub count: u32 }
impl TypeRefs {
    pub const EMPTY: Self = Self { idx: 0, count: 0 };

    pub fn is_empty(self) -> bool {
        self.count == 0
    }

    pub fn from_single(r: TypeRef) -> Self {
        Self { idx: r.0, count: 1 }
    }
    
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
