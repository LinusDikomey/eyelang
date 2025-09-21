mod intern;

use core::fmt;

use parser::ast::Primitive;

use crate::compiler::Generics;

id::id!(Type);
id::id!(BaseType);
impl Default for BaseType {
    fn default() -> Self {
        Self(0)
    }
}

macro_rules! builtin_types {
    ($count: literal $($name: ident = $size: literal)* @generic: $($generic_name: ident = $generics: expr,)*) => {

        #[derive(Clone, Copy, PartialEq, Eq, Debug)]
        pub enum BuiltinType {
            $($name,)*
            $($generic_name,)*
        }
        impl BuiltinType {
            pub const COUNT: u32 = $count;
            pub const VARIANTS: [Self; $count] = [
                $(Self::$name,)*
                $(Self::$generic_name,)*
            ];

            pub fn size(self) -> Option<u64> {
                match self {
                    $(Self::$name => Some($size),)*
                    _ => None,
                }
            }

            pub fn generics(self) -> Generics {
                match self {
                    $(Self::$generic_name => Generics::new($generics),)*
                    _ => Generics::EMPTY,
                }
            }
        }
        #[allow(non_upper_case_globals)]
        impl BaseType {
            $( pub const $name: Self = Self(BuiltinType::$name as u32); )*
            $( pub const $generic_name: Self = Self(BuiltinType::$generic_name as u32); )*
        }
        #[allow(non_upper_case_globals)]
        impl Type {
            $( pub const $name: Self = Self(BuiltinType::$name as u32); )*
        }
    };
}

builtin_types! {
    17

    Invalid = 0
    I8 = 1
    U8 = 1
    I16 = 2
    U16 = 2
    I32 = 4
    U32 = 4
    I64 = 8
    U64 = 8
    I128 = 16
    U128 = 16
    F32 = 4
    F64 = 8

    @generic:
    Tuple = vec![("elems".into(), vec![])],
    Pointer = vec![("pointee".into(), vec![])],
    Function = vec![
        ("return_type".into(), vec![]),
        ("args".into(), vec![]), // TODO: vararg generics or handle function separately
    ],
    Array = vec![
        ("element".into(), vec![]),
        ("count".into(), vec![]), // TODO: specify type of generic parameters
    ],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeFull<'a> {
    Instance(BaseType, &'a [Type]),
    Generic(u8),
    LocalEnum(&'a [(u32, Box<[Type]>)]),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeOld {
    Primitive(Primitive),
    DefId {
        id: Type,
        generics: Box<[TypeOld]>,
    },
    Pointer(Box<TypeOld>),
    Array(Box<(TypeOld, u32)>),
    Tuple(Box<[TypeOld]>),
    /// A generic type that will be replaced by a concrete type in generic instantiations.
    Generic(u8),
    /// a local enum that will only be created from inference
    LocalEnum(Box<[(u32, Box<[TypeOld]>)]>),
    Function(FunctionType),
    Invalid,
}
impl TypeOld {
    pub fn instantiate_generics(&self, generics: &[TypeOld]) -> Self {
        match self {
            TypeOld::Primitive(p) => TypeOld::Primitive(*p),
            TypeOld::DefId {
                id,
                generics: ty_generics,
            } => TypeOld::DefId {
                id: *id,
                generics: ty_generics
                    .iter()
                    .map(|ty| ty.instantiate_generics(generics))
                    .collect(),
            },
            TypeOld::Pointer(inner) => {
                TypeOld::Pointer(Box::new(inner.instantiate_generics(generics)))
            }
            TypeOld::Array(b) => {
                let (inner, count) = &**b;
                TypeOld::Array(Box::new((inner.instantiate_generics(generics), *count)))
            }
            TypeOld::Tuple(types) => TypeOld::Tuple(
                types
                    .iter()
                    .map(|ty| ty.instantiate_generics(generics))
                    .collect(),
            ),
            TypeOld::Generic(idx) => generics[*idx as usize].clone(),
            TypeOld::LocalEnum(variants) => TypeOld::LocalEnum(
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
            TypeOld::Function(f) => TypeOld::Function(FunctionType {
                params: f
                    .params
                    .iter()
                    .map(|ty| ty.instantiate_generics(generics))
                    .collect(),
                return_type: Box::new(f.return_type.instantiate_generics(generics)),
            }),
            TypeOld::Invalid => TypeOld::Invalid,
        }
    }

    pub fn instantiate_matches(&self, instance: &TypeOld, generics: &mut [TypeOld]) -> bool {
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

    pub fn is_same_as(&self, other: &TypeOld) -> Result<bool, InvalidTypeError> {
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
}
impl fmt::Display for TypeOld {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeOld::Primitive(p) => write!(f, "{}", <&str>::from(*p)),
            TypeOld::DefId { id, generics } => {
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
            TypeOld::Pointer(pointee) => write!(f, "*{pointee}"),
            TypeOld::Array(b) => {
                let (elem, count) = &**b;
                write!(f, "[{elem}; {count}]")
            }
            TypeOld::Tuple(elems) => {
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
            TypeOld::Generic(i) => write!(f, "<generic #{i}>"),
            TypeOld::LocalEnum(_) => write!(f, "LocalEnum: TODO: write"),
            TypeOld::Function(func) => {
                write!(f, "fn(")?;
                for (i, param) in func.params.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{param}")?;
                }
                write!(f, ") -> {}", func.return_type)
            }
            TypeOld::Invalid => write!(f, "<invalid>"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FunctionType {
    pub params: Box<[TypeOld]>,
    pub return_type: Box<TypeOld>,
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
