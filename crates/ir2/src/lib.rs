use std::{
    fmt,
    marker::PhantomData,
    num::NonZeroU64,
    ops::{Deref, Index},
};

use color_format::cwrite;

pub mod builder;
pub mod dialect;

mod argument;
mod environment;

pub use argument::{Argument, IntoArgs};
pub use environment::Environment;

pub struct ModuleOf<I>(ModuleId, PhantomData<*const I>);
impl<I> ModuleOf<I> {
    pub fn id(self) -> ModuleId {
        self.0
    }
}
impl<I: Inst> Deref for ModuleOf<I> {
    type Target = I::InstTable;

    fn deref(&self) -> &Self::Target {
        I::inst_table(self)
    }
}
impl<I> Clone for ModuleOf<I> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<I> Copy for ModuleOf<I> {}
impl<I> From<ModuleOf<I>> for ModuleId {
    fn from(value: ModuleOf<I>) -> Self {
        value.0
    }
}

pub struct Module {
    name: Box<str>,
    functions: Vec<Function>,
    globals: Vec<Global>,
}
impl Index<LocalFunctionId> for Module {
    type Output = Function;

    fn index(&self, index: LocalFunctionId) -> &Self::Output {
        &self.functions[index.0 as usize]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ModuleId(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LocalFunctionId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FunctionId {
    pub module: ModuleId,
    pub function: LocalFunctionId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GlobalId {
    pub module: ModuleId,
    pub idx: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypeId(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PrimitiveId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Ref(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BlockId(u32);

pub struct Function {
    pub name: Box<str>,
    pub types: Types,
    pub params: Vec<Parameter>,
    pub varargs: bool,
    pub terminator: bool,
    pub return_type: Option<TypeId>,
    pub ir: Option<FunctionIr>,
}
impl Function {
    pub fn new(
        name: impl Into<Box<str>>,
        types: Types,
        params: Vec<TypeId>,
        return_type: TypeId,
        ir: FunctionIr,
    ) -> Self {
        Self {
            name: name.into(),
            types,
            params: params.iter().map(|_| Parameter::Ref).collect(),
            varargs: false,
            terminator: false,
            return_type: Some(return_type),
            ir: Some(ir),
        }
    }
}

pub struct Global {
    name: Box<str>,
    align: u64,
    value: Box<[u8]>,
}

pub struct PrimitiveInfo {
    pub name: Box<str>,
    pub size: u64,
    pub align: NonZeroU64,
}

pub struct Types {
    types: Vec<Type>,
}
impl Types {
    pub fn new() -> Self {
        Self { types: Vec::new() }
    }

    pub fn add(&mut self, ty: impl Into<Type>) -> TypeId {
        let id = TypeId(self.types.len() as _);
        self.types.push(ty.into());
        id
    }

    pub fn display_type<'a>(
        &'a self,
        ty: TypeId,
        primitives: &'a [PrimitiveInfo],
    ) -> impl fmt::Display + use<'a> {
        TypeDisplay {
            types: self,
            primitives,
            id: ty,
        }
    }
}
impl Index<TypeId> for Types {
    type Output = Type;

    fn index(&self, index: TypeId) -> &Self::Output {
        &self.types[index.0 as usize]
    }
}

struct TypeDisplay<'a> {
    types: &'a Types,
    primitives: &'a [PrimitiveInfo],
    id: TypeId,
}
impl fmt::Display for TypeDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.types[self.id] {
            Type::Primitive(primitive_id) => {
                cwrite!(f, "#m<{}>", self.primitives[primitive_id.0 as usize].name)
            }
            Type::Tuple { idx, count } => {
                write!(f, "(")?;
                for i in idx..idx + count {
                    if i != idx {
                        write!(f, ", ")?;
                    }
                    let display = TypeDisplay {
                        types: self.types,
                        primitives: self.primitives,
                        id: TypeId(i),
                    };
                    write!(f, "{display}")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Default for Types {
    fn default() -> Self {
        Self::new()
    }
}

pub enum Type {
    Primitive(PrimitiveId),

    Tuple { idx: u32, count: u32 },
}

pub struct FunctionIr {
    blocks: Vec<BlockInfo>,
    insts: Vec<Instruction>,
    extra: Vec<u32>,
}
impl FunctionIr {
    pub fn block_ids(&self) -> impl Iterator<Item = BlockId> {
        (0..self.blocks.len() as u32).map(BlockId)
    }

    pub fn get_block(&self, id: BlockId) -> impl Iterator<Item = (Ref, &Instruction)> + use<'_> {
        let block = &self.blocks[id.0 as usize];
        (block.idx..block.idx + block.len).map(|i| (Ref(i), &self.insts[i as usize]))
    }

    pub fn extra(&self) -> &[u32] {
        &self.extra
    }
}

struct BlockInfo {
    arg_count: u32,
    idx: u32,
    len: u32,
}

pub struct Instruction {
    function: FunctionId,
    args: [u32; 2],
    ty: TypeId,
}
impl Instruction {
    pub fn module(&self) -> ModuleId {
        self.function.module
    }

    pub fn function(&self) -> LocalFunctionId {
        self.function.function
    }

    pub fn args<'a>(
        &'a self,
        params: &'a [Parameter],
        extra: &'a [u32],
    ) -> impl Iterator<Item = Argument> + use<'a> {
        decode_args(&self.args, params, extra)
    }

    pub fn as_module<I: Inst>(&self, m: ModuleOf<I>) -> Option<TypedInstruction<I>> {
        (self.module() == m.0).then(|| TypedInstruction {
            inst: self.function.function.try_into().unwrap(),
            args: self.args,
            ty: self.ty,
        })
    }
}

fn decode_args<'a>(
    args: &'a [u32; 2],
    params: &'a [Parameter],
    extra: &'a [u32],
) -> impl Iterator<Item = Argument> + use<'a> {
    let count: usize = params.iter().map(|p| p.slot_count()).sum();
    let mut args = if count <= 2 {
        &args[..count]
    } else {
        let i = args[0] as usize;
        &extra[i..i + count]
    }
    .iter()
    .copied();

    let mut arg = move || args.next().unwrap();

    params.iter().map(move |param| match param {
        Parameter::Ref => Argument::Ref(Ref(arg())),
        Parameter::BlockId => Argument::Block(BlockId(arg())),
        Parameter::Int => Argument::Int(arg()),
        Parameter::TypeId => Argument::TypeId(TypeId(arg())),
        Parameter::FunctionId => Argument::FunctionId(FunctionId {
            module: ModuleId(arg()),
            function: LocalFunctionId(arg()),
        }),
        Parameter::GlobalId => Argument::GlobalId(GlobalId {
            module: ModuleId(arg()),
            idx: arg(),
        }),
    })
}

pub struct TypedInstruction<I: Inst> {
    inst: I,
    args: [u32; 2],
    ty: TypeId,
}
impl<I: Inst> TypedInstruction<I> {
    pub fn op(&self) -> I {
        self.inst
    }

    pub fn args<'a>(&'a self, extra: &'a [u32]) -> impl Iterator<Item = Argument> + use<'a, I> {
        let params = self.inst.params();
        decode_args(&self.args, params, extra)
    }
}

pub trait Inst: TryFrom<LocalFunctionId, Error = InvalidInstruction> + Copy {
    const MODULE_NAME: &'static str;

    type InstTable: 'static;

    fn functions() -> Vec<Function>;
    fn inst_table(module: &ModuleOf<Self>) -> &Self::InstTable;
    fn params(self) -> &'static [Parameter];
}

#[macro_export]
macro_rules! primitives {
    ($($primitive: ident = $size: literal)*) => {
        pub enum Primitive {
            $($primitive,)*
        }
        impl Primitive {
            pub fn id(self) -> $crate::PrimitiveId {
                $crate::PrimitiveId(self as u32)
            }

            pub fn create_infos() -> ::std::vec::Vec<$crate::PrimitiveInfo> {
                ::std::vec![
                    $($crate::PrimitiveInfo {
                        name: stringify!($primitive).into(),
                        size: $size,
                        align: ::core::num::NonZeroU64::new($size.max(1)).unwrap(),
                    }),*
                ]
            }
        }
        impl From<Primitive> for $crate::Type {
            fn from(value: Primitive) -> Self {
                Self::Primitive(value.id())
            }
        }
    };
}

pub type Int = u32;

#[derive(Debug, Clone, Copy)]
pub enum Parameter {
    Ref,
    BlockId,
    Int,
    TypeId,
    FunctionId,
    GlobalId,
}
impl Parameter {
    pub fn slot_count(self) -> usize {
        match self {
            Parameter::Ref | Parameter::BlockId | Parameter::Int | Parameter::TypeId => 1,
            Parameter::FunctionId | Parameter::GlobalId => 2,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct InvalidInstruction;

#[doc(hidden)]
pub use strum::FromRepr as __FromRepr;

#[macro_export]
macro_rules! instructions {
    ($module_name: ident $name: literal $table_name: ident $($instruction: ident $($arg_name: ident: $arg: ident)* $(!terminator $terminator_val: literal)?; )*) => {
        #[derive(Debug, Clone, Copy, $crate::__FromRepr)]
        pub enum $module_name {
            $($instruction,)*
        }

        #[repr(transparent)]
        #[derive(Debug, Clone, Copy)]
        pub struct $table_name<T>(T);
        #[allow(non_snake_case)]
        impl $table_name<$crate::ModuleOf<$module_name>> {
            $(
                #[inline]
                pub fn $instruction(self, $($arg_name: $crate::$arg),*) -> ($crate::FunctionId, impl $crate::IntoArgs) {
                    let id = $crate::FunctionId {
                        module: self.0.id(),
                        function: $module_name::$instruction.into(),
                    };
                    let args = ($($arg_name,)*);
                    (id, args)
                }
            )*
        }
        impl $crate::Inst for $module_name {
            const MODULE_NAME: &'static ::core::primitive::str = $name;

            type InstTable = $table_name<$crate::ModuleOf<Self>>;

            fn functions() -> ::std::vec::Vec<$crate::Function> {
                ::std::vec![
                    $(
                        {
                            let terminator = false $(|| $terminator_val)?;
                            $crate::Function {
                                name: stringify!($instruction).into(),
                                types: $crate::Types::new(),
                                params: vec![ $( $crate::Parameter::$arg, )* ],
                                varargs: false,
                                terminator,
                                return_type: None,
                                ir: None,
                            }
                        },
                    )*
                ]
            }

            fn params(self) -> &'static [$crate::Parameter] {
                match self {
                    $(
                        Self::$instruction => &[$( $crate::Parameter::$arg, )*],
                    )*
                }
            }

            fn inst_table(module: &$crate::ModuleOf<Self>) -> &Self::InstTable {
                unsafe { ::core::mem::transmute(module) }
            }

        }
        impl $module_name {
            pub fn id(self) -> $crate::LocalFunctionId {
                $crate::LocalFunctionId(self as u32)
            }

        }
        impl From<$module_name> for $crate::LocalFunctionId {
            fn from(value: $module_name) -> Self {
                Self(value as u32)
            }
        }
        impl ::core::convert::TryFrom<$crate::LocalFunctionId> for $module_name {
            type Error = $crate::InvalidInstruction;

            fn try_from(value: $crate::LocalFunctionId) -> ::core::result::Result<Self, Self::Error> {
                Self::from_repr(value.0 as usize).ok_or($crate::InvalidInstruction)
            }
        }

    };
}
