use std::{
    any::type_name,
    arch, fmt,
    marker::PhantomData,
    num::NonZeroU64,
    ops::{Deref, Index},
};

use color_format::cwrite;

pub mod block_graph;
pub mod builder;
pub mod dialect;

mod argument;
mod bitmap;
mod builtins;
mod display;
mod environment;

pub use argument::{Argument, IntoArgs};
pub use bitmap::Bitmap;
pub use block_graph::BlockGraph;
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
impl Module {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn functions(&self) -> &[Function] {
        &self.functions
    }

    pub fn globals(&self) -> &[Global] {
        &self.globals
    }
}
impl Index<LocalFunctionId> for Module {
    type Output = Function;

    fn index(&self, index: LocalFunctionId) -> &Self::Output {
        &self.functions[index.0 as usize]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ModuleId(u32);
impl ModuleId {
    pub const BUILTINS: Self = Self(0);
}

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
pub struct TypeIds {
    idx: u32,
    count: u32,
}
impl TypeIds {
    pub fn count(self) -> u32 {
        self.count
    }

    pub fn iter(self) -> impl Iterator<Item = TypeId> {
        (self.idx..self.idx + self.count).map(TypeId)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PrimitiveId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Ref(u32);
impl Ref {
    pub fn idx(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Refs {
    idx: u32,
    count: u32,
}
impl Refs {
    pub fn nth(self, n: u32) -> Ref {
        assert!(
            n < self.count,
            "Refs index out of range, {n} >= {}",
            self.count
        );
        Ref(self.idx + n)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BlockId(u32);
impl BlockId {
    pub const ENTRY: Self = Self(0);

    pub fn idx(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy)]
pub struct BlockTarget<'a>(pub BlockId, pub &'a [Ref]);

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
            params: params.iter().copied().map(Parameter::RefOf).collect(),
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

    pub fn add_multiple(&mut self, types: impl IntoIterator<Item = Type>) -> TypeIds {
        let idx = self.types.len() as u32;
        self.types.extend(types);
        let count = self.types.len() as u32 - idx;
        TypeIds { idx, count }
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

    pub fn is_zero_sized(&self, ty: Type, primitives: &[PrimitiveInfo]) -> bool {
        match ty {
            Type::Primitive(primitive_id) => primitives[primitive_id.0 as usize].size == 0,
            Type::Array(_, 0) => true,
            Type::Array(elem, _) => self.is_zero_sized(self[elem], primitives),
            Type::Tuple(elems) => elems
                .iter()
                .all(|elem| self.is_zero_sized(self[elem], primitives)),
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
            Type::Array(elem, count) => {
                let elem_display = TypeDisplay {
                    types: self.types,
                    primitives: self.primitives,
                    id: elem,
                };
                cwrite!(f, "[{elem_display}; #y<{count}>]")
            }
            Type::Tuple(elems) => {
                write!(f, "(")?;
                for i in elems.idx..elems.idx + elems.count {
                    if i != elems.idx {
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

#[derive(Debug, Clone, Copy)]
pub enum Type {
    Primitive(PrimitiveId),
    Array(TypeId, u32),
    Tuple(TypeIds),
}

pub struct FunctionIr {
    blocks: Vec<BlockInfo>,
    insts: Vec<Instruction>,
    extra: Vec<u32>,
}
impl FunctionIr {
    pub fn block_ids(&self) -> impl ExactSizeIterator<Item = BlockId> {
        (0..self.blocks.len() as u32).map(BlockId)
    }

    pub fn block_count(&self) -> u32 {
        self.blocks.len() as _
    }

    pub fn inst_count(&self) -> u32 {
        self.insts.len() as _
    }

    pub fn get_block_args(&self, id: BlockId) -> impl ExactSizeIterator<Item = Ref> {
        let block = &self.blocks[id.0 as usize];
        (block.idx..block.idx + block.arg_count).map(Ref)
    }

    pub fn get_block(&self, id: BlockId) -> impl Iterator<Item = (Ref, &Instruction)> + use<'_> {
        let block = &self.blocks[id.0 as usize];
        let i = block.idx + block.arg_count;
        (i..i + block.len).map(|i| (Ref(i), &self.insts[i as usize]))
    }

    pub fn get_inst(&self, r: Ref) -> &Instruction {
        &self.insts[r.idx()]
    }

    pub fn blocks(&self) -> &[BlockInfo] {
        &self.blocks
    }

    pub fn extra(&self) -> &[u32] {
        &self.extra
    }

    pub fn get_ref_ty(&self, arg: Ref) -> TypeId {
        self.insts[arg.idx()].ty
    }

    pub fn args<'a, I: Inst + 'static>(
        &'a self,
        inst: &'a TypedInstruction<I>,
    ) -> impl Iterator<Item = Argument<'a>> + use<'a, I> {
        inst.args(&self.blocks, &self.extra)
    }

    pub fn args_n<'a, I: Inst + 'static, const N: usize>(
        &'a self,
        inst: &'a TypedInstruction<I>,
    ) -> [Argument<'a>; N] {
        let mut args = self.args(inst);
        let args_array = std::array::from_fn(|_| args.next().expect("not enough args"));
        assert!(args.next().is_none(), "too many args");
        args_array
    }
}

pub struct BlockInfo {
    arg_count: u32,
    idx: u32,
    len: u32,
}

#[derive(Debug)]
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

    pub fn ty(&self) -> TypeId {
        self.ty
    }

    pub fn args<'a>(
        &'a self,
        params: &'a [Parameter],
        blocks: &'a [BlockInfo],
        extra: &'a [u32],
    ) -> impl Iterator<Item = Argument<'a>> + use<'a> {
        decode_args(&self.args, params, blocks, extra)
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
    blocks: &'a [BlockInfo],
    extra: &'a [u32],
) -> impl Iterator<Item = Argument<'a>> + use<'a> {
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
        Parameter::Ref | Parameter::RefOf(_) => Argument::Ref(Ref(arg())),
        Parameter::BlockTarget => {
            let id = BlockId(arg());
            let arg_idx = arg();
            let arg_count = blocks[id.idx()].arg_count;
            let args: &[u32] = &extra[arg_idx as usize..(arg_idx + arg_count) as usize];
            // SAFETY: Ref is repr(transparent)
            let args: &[Ref] = unsafe { std::mem::transmute(args) };
            Argument::BlockTarget(BlockTarget(id, args))
        }
        Parameter::Int => Argument::Int(arg() as u64 | ((arg() as u64) << 32)),
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

    pub fn ty(&self) -> TypeId {
        self.ty
    }

    pub fn args<'a>(
        &'a self,
        blocks: &'a [BlockInfo],
        extra: &'a [u32],
    ) -> impl Iterator<Item = Argument<'a>> + use<'a, I> {
        let params = self.inst.params();
        decode_args(&self.args, params, blocks, extra)
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
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, $crate::__FromRepr)]
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
        impl TryFrom<$crate::PrimitiveId> for Primitive {
            type Error = $crate::InvalidPrimitive;

            fn try_from(value: $crate::PrimitiveId) -> ::core::result::Result<Self, Self::Error> {
                Self::from_repr(value.0 as usize).ok_or($crate::InvalidPrimitive)
            }
        }
    };
}

pub type Int = u64;

#[derive(Debug, Clone, Copy)]
pub enum Parameter {
    Ref,
    RefOf(TypeId),
    BlockTarget,
    Int,
    TypeId,
    FunctionId,
    GlobalId,
}
impl Parameter {
    pub fn slot_count(self) -> usize {
        match self {
            Parameter::Ref | Parameter::RefOf(_) | Parameter::TypeId => 1,
            Parameter::Int
            | Parameter::BlockTarget
            | Parameter::FunctionId
            | Parameter::GlobalId => 2,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct InvalidInstruction;

#[derive(Debug, Clone, Copy)]
pub struct InvalidPrimitive;

#[doc(hidden)]
pub use strum::FromRepr as __FromRepr;

#[macro_export]
macro_rules! lifetime_or_static {
    ($p: path, $lifetime: lifetime) => {
        $lifetime
    };
    () => {
        'static
    };
}

#[macro_export]
macro_rules! instructions {
    ($module_name: ident $name: literal $table_name: ident $($instruction: ident $($arg_name: ident: $arg: ident $(<$life: lifetime>)?)* $(!terminator $terminator_val: literal)?; )*) => {
        #[derive(Debug, Clone, Copy, $crate::__FromRepr, PartialEq, Eq, Hash)]
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
                pub fn $instruction<'a>(self, $($arg_name: $crate::$arg $(<$life>)?),*) -> ($crate::FunctionId, impl $crate::IntoArgs<'a>) where 'a: 'static {
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
