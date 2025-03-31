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
    LocalEnum(Box<[(u32, Box<[Type]>)]>),
    Function(FunctionType),
    /// Self type (only used in trait definitions)
    Invalid,
}
impl Type {
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
                    .map(|(ordinal, variant)| {
                        (
                            *ordinal,
                            variant
                                .iter()
                                .map(|ty| ty.instantiate_generics(generics))
                                .collect(),
                        )
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

    pub fn instantiate_matches(&self, instance: &Type, generics: &mut [Type]) -> bool {
        match self {
            &Self::Generic(i) => {
                generics[i as usize] = instance.clone();
                true
            }
            Self::Invalid => true,
            Self::Primitive(a) => matches!(instance, Self::Primitive(b) if a == b),
            Self::DefId {
                id: a,
                generics: a_generics,
            } => {
                let Self::DefId {
                    id: b,
                    generics: b_generics,
                } = instance
                else {
                    return false;
                };
                a == b
                    && a_generics
                        .iter()
                        .zip(b_generics)
                        .all(|(a, b)| a.instantiate_matches(b, generics))
            }
            Self::Pointer(a) => {
                matches!(instance, Self::Pointer(b) if a.instantiate_matches(b, generics))
            }
            Self::Array(a) => {
                let Self::Array(b) = instance else {
                    return false;
                };
                a.1 == b.1 && a.0.instantiate_matches(&b.0, generics)
            }
            Self::Tuple(a) => {
                let Self::Tuple(b) = instance else {
                    return false;
                };
                a.len() == b.len()
                    && a.iter()
                        .zip(b)
                        .all(|(a, b)| a.instantiate_matches(b, generics))
            }
            Self::LocalEnum(_) => unreachable!("impl types can't be LocalEnum"),
            Self::Function(a) => {
                let Self::Function(b) = instance else {
                    return false;
                };
                a.params.len() == b.params.len()
                    && a.return_type.instantiate_matches(&b.return_type, generics)
                    && a.params
                        .iter()
                        .zip(&b.params)
                        .all(|(a, b)| a.instantiate_matches(b, generics))
            }
        }
    }

    pub fn is_same_as(&self, other: &Type) -> Result<bool, InvalidTypeError> {
        Ok(match (self, other) {
            (Self::Invalid, _) | (_, Self::Invalid) => return Err(InvalidTypeError),
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
                    if !a.is_same_as(b)? {
                        return Ok(false);
                    }
                }
                true
            }
            (Self::Pointer(a), Self::Pointer(b)) => a.is_same_as(b)?,
            (Self::Array(a), Self::Array(b)) => a.0.is_same_as(&b.0)? && a.1 == b.1,
            (Self::Tuple(a), Self::Tuple(b)) => {
                if a.len() != b.len() {
                    return Ok(false);
                }
                for (a, b) in a.iter().zip(b) {
                    if !a.is_same_as(b)? {
                        return Ok(false);
                    }
                }
                true
            }
            (Self::Generic(a), Self::Generic(b)) => a == b,
            (Self::LocalEnum(_), Self::LocalEnum(_)) => unreachable!(),
            (Self::Function(a), Self::Function(b)) => a.is_same_as(b)?,
            _ => false,
        })
    }

    pub fn uninhabited(&self) -> Result<bool, InvalidTypeError> {
        Ok(match self {
            Self::Primitive(Primitive::Never) => true,
            Self::Primitive(_) => false,
            Self::DefId { .. } => false, // TODO
            Self::Pointer(_) => false,
            Self::Array(arr) => arr.1 != 0 && arr.0.uninhabited()?,
            Self::Tuple(fields) => fields
                .iter()
                .try_fold(false, |b, field| Ok(b || field.uninhabited()?))?,
            Self::Generic(_) => false, // TODO
            Self::LocalEnum(variants) => variants.iter().try_fold(true, |b, (_, args)| {
                Ok(b && args
                    .iter()
                    .try_fold(false, |b, arg| Ok(b || arg.uninhabited()?))?)
            })?,
            Self::Function(_) => false,
            Self::Invalid => return Err(InvalidTypeError),
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
    pub fn is_same_as(&self, b: &Self) -> Result<bool, InvalidTypeError> {
        if self.params.len() != b.params.len() {
            return Ok(false);
        }
        for (a, b) in self.params.iter().zip(&b.params) {
            if !a.is_same_as(b)? {
                return Ok(false);
            }
        }
        self.return_type.is_same_as(&b.return_type)
    }
}

pub struct InvalidTypeError;
