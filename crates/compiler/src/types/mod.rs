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
macro_rules! primitive_impl {
    ($impl_for: ident; ints: $($int: ident)*; floats: $($float: ident)*; other: $($other: ident)*;) => {
        impl $impl_for {
            pub fn is_int(self) -> bool {
                self.as_int().is_some()
            }

            pub fn as_int(self) -> Option<IntType> {
                Some(match self {
                    $(Self::$int => IntType::$int,)*
                    _ => return None,
                })
            }

            pub fn is_float(self) -> bool {
                self.as_float().is_some()
            }

            pub fn as_float(self) -> Option<FloatType> {
                Some(match self {
                    $(Self::$float => FloatType::$float,)*
                    _ => return None,
                })
            }
        }
        impl From<Primitive> for $impl_for {
            fn from(value: Primitive) -> Self {
                match value {
                    $(Primitive::$int => Self::$int,)*
                    $(Primitive::$float => Self::$float,)*
                    $(Primitive::$other=> Self::$other,)*
                }
            }
        }
    };
}
macro_rules! primitive_impls {
    ($($impl_for: ident)*) => {
        $(
            primitive_impl! {
                $impl_for;
                ints: I8 U8 I16 U16 I32 U32 I64 U64 I128 U128;
                floats: F32 F64;
                other: Type;
            }
        )*
    };
}
primitive_impls! { Type BaseType }

id::id!(BaseType);

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

#[derive(Clone, Copy, Debug)]
pub struct InvalidTypeError;
