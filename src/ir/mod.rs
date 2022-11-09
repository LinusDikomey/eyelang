use std::fmt;
use color_format::*;
use crate::ast::{self, ModuleId};
use crate::dmap::DHashMap;
use crate::types::Primitive;
use builder::IrBuilder;

pub mod builder;
pub mod eval;
pub mod exhaust;

mod const_val;
pub use const_val::{ConstVal, ConstSymbol};

pub mod display;

mod instruction;
pub use instruction::{Instruction, Tag, Data};

mod typing;
pub use typing::{TypeTable, FinalTypeTable, TypeInfo, TypeTableIndex, TypeTableIndices};

pub enum FunctionOrHeader {
    Func(Function),
    Header(FunctionHeader),
}
impl FunctionOrHeader {
    pub fn header(&self) -> &FunctionHeader {
        match self {
            Self::Func(f) => &f.header,
            Self::Header(header) => header,
        }
    }
}

pub struct GenericFunc {
    pub name: String,
    pub header: FunctionHeader,
    pub def: ast::Function,
    pub generics: Vec<String>,
    pub instantiations: DHashMap<Vec<Type>, SymbolKey>,
    pub module: ModuleId,
}
impl GenericFunc {
    pub fn generic_count(&self) -> u8 {
        self.generics.len() as u8
    }
}

#[derive(Debug)]
pub struct Function {
    pub header: FunctionHeader,
    pub ir: Option<FunctionIr>
}

#[derive(Debug)]
pub struct FunctionIr {
    pub inst: Vec<Instruction>,
    pub extra: Vec<u8>,
    pub types: FinalTypeTable,
    pub blocks: Vec<u32>,
}

pub struct Module {
    pub name: String,
    pub funcs: Vec<Function>,
    pub globals: Vec<(String, Type, Option<ConstVal>)>,
    pub types: Vec<(String, TypeDef)>,
}

const INDEX_OFFSET: u32 = std::mem::variant_count::<RefVal>() as u32;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Ref(u32);
impl Ref {
    pub const UNDEF: Self = Self::val(RefVal::Undef);
    pub const UNIT: Self = Self::val(RefVal::Unit);

    pub const fn val(val: RefVal) -> Self {
        Self(val as u32)
    }
    pub fn index(idx: u32) -> Self {
        Self(INDEX_OFFSET + idx)
    }
    pub fn is_val(self) -> bool { self.0 < INDEX_OFFSET }
    pub fn into_val(self) -> Option<RefVal> {
        self.is_val().then(|| unsafe { std::mem::transmute(self.0 as u8) })
    }
    pub fn is_ref(self) -> bool { !self.is_val() }
    pub fn into_ref(self) -> Option<u32> {
        self.is_ref().then(|| self.0 - INDEX_OFFSET)
    }

    pub fn to_bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }

    pub fn from_bytes(b: [u8; 4]) -> Self {
        Self(u32::from_le_bytes(b))
    }
}
impl fmt::Debug for Ref {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(val) = self.into_val() {
            write!(f, "Val({val})")
        } else if let Some(r) = self.into_ref() {
            write!(f, "Ref({r})")
        } else {
            unreachable!()
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum RefVal {
    True,
    False,
    Unit,
    Undef
}
impl fmt::Display for RefVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RefVal::True => write!(f, "true"),
            RefVal::False => write!(f, "false"),
            //RefVal::Zero => write!(f, "0"),
            //RefVal::One => write!(f, "1"),
            RefVal::Unit => write!(f, "()"),
            RefVal::Undef => write!(f, "undef"),
        }
    }
}


#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BlockIndex(u32);
impl BlockIndex {
    pub fn bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }
}
impl fmt::Display for BlockIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        cwrite!(f, "#b<b{}>", self.0)
    }
}
