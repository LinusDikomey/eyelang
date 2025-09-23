mod intern;

pub use intern::Types;

use core::fmt;

use parser::ast::{FloatType, IntType, Primitive};

use crate::compiler::Generics;

id::id!(Type);
impl Type {
    pub fn is_same_as(self, other: Type) -> Result<bool, InvalidTypeError> {
        if self == Type::Invalid || other == Type::Invalid {
            Err(InvalidTypeError)
        } else {
            Ok(self == other)
        }
    }
}

impl From<Primitive> for Type {
    fn from(value: Primitive) -> Self {
        match value {
            Primitive::I8 => Self::I8,
            Primitive::I16 => Self::I16,
            Primitive::I32 => Self::I32,
            Primitive::I64 => Self::I64,
            Primitive::I128 => Self::I128,
            Primitive::U8 => Self::U8,
            Primitive::U16 => Self::U16,
            Primitive::U32 => Self::U32,
            Primitive::U64 => Self::U64,
            Primitive::U128 => Self::U128,
            Primitive::F32 => Self::F32,
            Primitive::F64 => Self::F64,
            Primitive::Type => Self::Type,
        }
    }
}
id::id!(BaseType);
impl BaseType {
    pub fn is_int(self) -> bool {
        self.as_int().is_some()
    }

    pub fn as_int(self) -> Option<IntType> {
        Some(match self {
            Self::I8 => IntType::I8,
            Self::I16 => IntType::I16,
            Self::I32 => IntType::I32,
            Self::I64 => IntType::I64,
            Self::I128 => IntType::I128,
            Self::U8 => IntType::U8,
            Self::U16 => IntType::U16,
            Self::U32 => IntType::U32,
            Self::U64 => IntType::U64,
            Self::U128 => IntType::U128,
            _ => return None,
        })
    }

    pub fn is_float(self) -> bool {
        self.as_float().is_some()
    }

    pub fn as_float(self) -> Option<FloatType> {
        Some(match self {
            Self::F32 => FloatType::F32,
            Self::F64 => FloatType::F64,
            _ => return None,
        })
    }
}
impl From<Primitive> for BaseType {
    fn from(value: Primitive) -> Self {
        match value {
            Primitive::I8 => Self::I8,
            Primitive::I16 => Self::I16,
            Primitive::I32 => Self::I32,
            Primitive::I64 => Self::I64,
            Primitive::I128 => Self::I128,
            Primitive::U8 => Self::U8,
            Primitive::U16 => Self::U16,
            Primitive::U32 => Self::U32,
            Primitive::U64 => Self::U64,
            Primitive::U128 => Self::U128,
            Primitive::F32 => Self::F32,
            Primitive::F64 => Self::F64,
            Primitive::Type => Self::Type,
        }
    }
}
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

            pub fn name(self) -> &'static str {
                match self {
                    $( Self::$name => stringify!($name), )*
                    $( Self::$generic_name => stringify!($generic_name), )*
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
    19

    Invalid = 0
    Unit = 0 // this is just an empty tuple but this alias is added so that no interning is needed for unit
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
    Type = 9

    @generic:
    Tuple = vec![("elems".into(), vec![])],
    Array = vec![
        ("element".into(), vec![]),
        ("count".into(), vec![]), // TODO: specify type of generic parameters
    ],
    Pointer = vec![("pointee".into(), vec![])],
    Function = vec![
        ("return_type".into(), vec![]),
        ("args".into(), vec![]), // TODO: vararg generics or handle function separately
    ],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeFull<'a> {
    Instance(BaseType, &'a [Type]),
    Generic(u8),
    LocalEnum(&'a [(u32, Box<[Type]>)]),
    Const(u64),
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
    pub params: Box<[Type]>,
    pub return_type: Type,
}
impl FunctionType {
    pub fn is_same_as(&self, b: &Self) -> Result<bool, InvalidTypeError> {
        if self.params.len() != b.params.len() {
            return Ok(false);
        }
        for (&a, &b) in self.params.iter().zip(&b.params) {
            if !a.is_same_as(b)? {
                return Ok(false);
            }
        }
        self.return_type.is_same_as(b.return_type)
    }
}

pub struct InvalidTypeError;
