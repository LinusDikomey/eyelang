mod intern;

pub use intern::Types;

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
    Const(u64),
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
