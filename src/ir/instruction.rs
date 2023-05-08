use std::fmt;

use color_format::cwrite;
use crate::ast::{TypeId, TraitId, GlobalId, VariantId, self};

use super::{Ref, BlockIndex, types::TypeRef};


#[derive(Debug, Clone, Copy)]
pub struct Instruction {
    pub data: Data,
    pub tag: Tag,
    pub ty: TypeRef,
    pub used: bool
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Tag {
    BlockBegin,
    Ret,
    RetUndef,
    Param,

    Uninit,

    Int,
    LargeInt,
    Float,

    Func,
    TraitFunc,
    Type,
    Trait,
    Module,

    Decl,
    Load,
    Store,
    String,
    Call,
    Neg,
    Not,

    Global,

    Add,
    Sub,
    Mul,
    Div,
    Mod,

    Or,
    And,

    Eq,
    NE,
    LT,
    GT,
    LE,
    GE,

    Member,
    Value,

    EnumTag,
    EnumValueTag,
    EnumVariantMember,
    EnumValueVariantMember,

    Cast,

    Goto,
    Branch,
    Phi,

    Asm,
}
impl Tag {
    pub fn union_data_type(self) -> DataVariant {
        use DataVariant::*;
        match self {
            Tag::BlockBegin | Tag::Param => Int32,
            Tag::Uninit => None,
            Tag::Ret | Tag::Load | Tag::Neg | Tag::Not | Tag::Cast => UnOp,
            Tag::Int => Int,
            Tag::LargeInt => LargeInt,
            Tag::Float => Float,
            Tag::String => String,
            
            Tag::Func => Func,
            Tag::Type => Type,
            Tag::Trait => Trait,
            Tag::TraitFunc => TraitFunc,
            Tag::Decl => TypeTableIdx,
            Tag::Module => Int,

            Tag::RetUndef => None,
            Tag::Call => Call,
            Tag::Global => Global,
            Tag::Store | Tag::Add | Tag::Sub | Tag::Mul | Tag::Div | Tag::Mod
            | Tag::Or | Tag::And    
            | Tag::Eq | Tag::NE | Tag::LT | Tag::GT | Tag::LE | Tag::GE | Tag::Member => BinOp,
            Tag::Value => RefInt,
            Tag::Goto => Block,
            Tag::Branch => Branch,
            Tag::Phi => ExtraBranchRefs,
            Tag::Asm => Asm,

            Tag::EnumTag | Tag::EnumValueTag => UnOp,
            Tag::EnumVariantMember | Tag::EnumValueVariantMember => VariantMember,
        }
    }

    pub fn is_untyped(self) -> bool {
        matches!(self,
            Tag::BlockBegin | Tag::Ret | Tag::RetUndef
            | Tag::Store | Tag::Goto | Tag::Branch | Tag::Asm
        )
    }
    pub fn is_usable(self) -> bool {
        !matches!(self,
            Tag::BlockBegin | Tag::Ret | Tag::RetUndef
            | Tag::Store | Tag::Goto | Tag::Branch | Tag::Asm
        )
    }
    pub fn is_terminator(self) -> bool {
        matches!(self, Tag::Goto | Tag::Branch | Tag::Ret | Tag::RetUndef)
    }
}
impl fmt::Display for Tag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        cwrite!(f, "#b!<{:?}>", self)
    }
}

/// forces size of data to be 8 bytes
const _FORCE_DATA_SIZE: u64 = unsafe { std::mem::transmute(Data { int: 0 }) };

#[derive(Clone, Copy)]
pub union Data {
    pub int32: u32,
    pub int: u64,
    pub extra: u32,
    pub extra_len: (u32, u32),
    pub ty: TypeRef,
    pub float: f64,
    pub un_op: Ref,
    pub bin_op: (Ref, Ref),
    pub ref_int: (Ref, u32),
    pub asm: (u32, u16, u16), // extra_index, length of string, amount of arguments
    pub func_symbol: ast::FunctionId,
    pub type_symbol: TypeId,
    pub trait_symbol: TraitId,
    pub global_symbol: GlobalId,
    pub trait_func: (u32, u32), // extra_index for SymbolKey, func index in trait
    pub variant_member: (Ref, VariantId, u16),
    pub none: (),
    pub block: BlockIndex
}
impl fmt::Debug for Data {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.int })
    }
}

#[derive(Clone, Copy)]
pub enum DataVariant {
    Int,
    Int32,
    LargeInt,
    TypeTableIdx,
    TraitFunc,
    Block,
    Branch,
    String,
    Call,
    ExtraBranchRefs,
    Float,
    UnOp,
    BinOp,
    RefInt,
    Asm,
    Func,
    Type,
    Trait,
    Global,
    VariantMember,
    None,
}
