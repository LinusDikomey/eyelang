use core::fmt;

use crate::Primitive;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Primitive(Primitive),
    DefId {
        id: id::TypeId,
        generics: Box<[Type]>,
    },
    Pointer(Box<Type>),
    Array(Box<(Type, u32)>),
    Tuple(Box<[Type]>),
    /// A generic type that will be replaced by a concrete type in generic instantiations.
    Generic(u8),
    /// a local enum that will only be created from inference
    LocalEnum(Box<[Box<[Type]>]>),
    Function(FunctionType),
    /// Self type (only used in trait definitions)
    Invalid,
}
impl Type {
    /*
    pub fn layout<'a>(&self, ctx: impl Fn(TypeDefId) -> &'a ResolvedTypeDef + Copy, generics: &[Type]) -> Layout {
        match self {
            Type::Prim(p) => p.layout(),
            Type::Id(key, generics) => ctx(*key).layout(
                ctx,
                generics
                    .iter()
                    .map(|ty| ty.instantiate_generics(generics))
                    .collect::<Vec<_>>()
                    .as_slice()
                ),
            Type::Pointer(_) => Layout::PTR,
            Type::Array(b) => {
                let (ty, size) = &**b;
                Layout::array(ty.layout(ctx, generics), *size)
            }
            Type::Tuple(tuple) => {
                let mut l = Layout::EMPTY;
                for ty in tuple {
                    l.accumulate(ty.layout(ctx, generics));
                }
                l
            }
            Type::Generic(idx) => generics[*idx as usize].layout(ctx, generics),
            Type::LocalEnum(variants) => {
                let tag_layout = Enum::int_ty_from_variant_count(variants.len() as _)
                    .map_or(Layout::EMPTY, |int_ty| Primitive::from(int_ty).layout());
                let mut layout = tag_layout;
                for variant in variants {
                    let mut variant_layout = tag_layout;
                    for arg in variant {
                        variant_layout.accumulate(arg.layout(ctx, generics));
                    }
                    layout.add_variant(variant_layout);
                }
                layout
            }
            Type::TraitSelf => unreachable!("TraitSelf should always be replaced in concrete instances"),
            Type::Invalid => Layout::EMPTY,
        }
    }
    */

    pub fn instantiate_generics(&self, generics: &[Type]) -> Self {
        match self {
            Type::Primitive(p) => Type::Primitive(*p),
            Type::DefId {
                id,
                generics: ty_generics,
            } => Type::DefId {
                id: *id,
                generics: ty_generics
                    .iter()
                    .map(|ty| ty.instantiate_generics(generics))
                    .collect(),
            },
            Type::Pointer(inner) => Type::Pointer(Box::new(inner.instantiate_generics(generics))),
            Type::Array(b) => {
                let (inner, count) = &**b;
                Type::Array(Box::new((inner.instantiate_generics(generics), *count)))
            }
            Type::Tuple(types) => Type::Tuple(
                types
                    .iter()
                    .map(|ty| ty.instantiate_generics(generics))
                    .collect(),
            ),
            Type::Generic(idx) => generics[*idx as usize].clone(),
            Type::LocalEnum(variants) => Type::LocalEnum(
                variants
                    .iter()
                    .map(|variant| {
                        variant
                            .iter()
                            .map(|ty| ty.instantiate_generics(generics))
                            .collect()
                    })
                    .collect(),
            ),
            Type::Function(f) => Type::Function(FunctionType {
                params: f
                    .params
                    .iter()
                    .map(|ty| ty.instantiate_generics(generics))
                    .collect(),
                return_type: Box::new(f.return_type.instantiate_generics(generics)),
            }),
            Type::Invalid => Type::Invalid,
        }
    }

    pub fn is_same_as(
        &self,
        other: &Type,
        a_generics: &[Type],
        b_generics: &[Type],
    ) -> Result<bool, ()> {
        let l = if let &Self::Generic(i) = self {
            &a_generics[i as usize]
        } else {
            self
        };
        let r = if let &Self::Generic(i) = other {
            &b_generics[i as usize]
        } else {
            other
        };

        Ok(match (l, r) {
            (Self::Invalid, _) | (_, Self::Invalid) => return Err(()),
            (Self::Primitive(a), Self::Primitive(b)) => a == b,
            (
                Self::DefId {
                    id: a,
                    generics: a_generics,
                },
                Self::DefId {
                    id: b,
                    generics: b_generics,
                },
            ) => {
                assert_eq!(a_generics.len(), b_generics.len());
                if a != b {
                    return Ok(false);
                }
                for (a, b) in a_generics.iter().zip(b_generics) {
                    if !a.is_same_as(b, a_generics, b_generics)? {
                        return Ok(false);
                    }
                }
                true
            }
            (Self::Pointer(a), Self::Pointer(b)) => a.is_same_as(b, a_generics, b_generics)?,
            (Self::Array(a), Self::Array(b)) => {
                a.0.is_same_as(&b.0, a_generics, b_generics)? && a.1 == b.1
            }
            (Self::Tuple(a), Self::Tuple(b)) => {
                if a.len() != b.len() {
                    return Ok(false);
                }
                for (a, b) in a.iter().zip(b) {
                    if !a.is_same_as(b, a_generics, b_generics)? {
                        return Ok(false);
                    }
                }
                true
            }
            (Self::Generic(a), Self::Generic(b)) => a == b,
            (Self::LocalEnum(_), Self::LocalEnum(_)) => unreachable!(),
            (Self::Function(a), Self::Function(b)) => a.is_same_as(b, a_generics, b_generics)?,
            _ => false,
        })
    }
}
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Primitive(p) => write!(f, "{}", <&str>::from(*p)),
            Type::DefId { id, generics } => {
                write!(f, "TypeId({})", id.idx())?;
                if !generics.is_empty() {
                    write!(f, "[")?;
                    for (i, generic) in generics.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{generic}")?;
                    }
                    write!(f, "]")?;
                }
                Ok(())
            }
            Type::Pointer(pointee) => write!(f, "*{pointee}"),
            Type::Array(b) => {
                let (elem, count) = &**b;
                write!(f, "[{elem}; {count}]")
            }
            Type::Tuple(elems) => {
                write!(f, "(")?;
                for (i, elem) in elems.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{elem}")?;
                }
                if elems.len() == 1 {
                    write!(f, ",)")
                } else {
                    write!(f, ")")
                }
            }
            Type::Generic(i) => write!(f, "<generic #{i}>"),
            Type::LocalEnum(_) => write!(f, "LocalEnum: TODO: write"),
            Type::Function(func) => {
                write!(f, "fn(")?;
                for (i, param) in func.params.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{param}")?;
                }
                write!(f, ") -> {}", func.return_type)
            }
            Type::Invalid => write!(f, "<invalid>"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FunctionType {
    pub params: Box<[Type]>,
    pub return_type: Box<Type>,
}
impl FunctionType {
    pub fn is_same_as(
        &self,
        b: &Self,
        a_generics: &[Type],
        b_generics: &[Type],
    ) -> Result<bool, ()> {
        if self.params.len() != b.params.len() {
            return Ok(false);
        }
        for (a, b) in self.params.iter().zip(&b.params) {
            if !a.is_same_as(b, a_generics, b_generics)? {
                return Ok(false);
            }
        }
        self.return_type
            .is_same_as(&b.return_type, a_generics, b_generics)
    }
}
