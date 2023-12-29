use std::fmt;

use color_format::cwrite;

use super::{Ref, BlockIndex, ir_types::TypeRef};


#[derive(Debug, Clone, Copy)]
pub struct Instruction {
    pub data: Data,
    pub tag: Tag,
    pub ty: TypeRef,
    pub used: bool
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
#[allow(unused)] // FIXME: these instructions should be cleaned up if they still aren't used
pub enum Tag {
    BlockBegin,
    Ret,
    Param,

    Uninit,

    Int,
    LargeInt,
    Float,

    Decl,
    Load,
    Store,
    String,
    Call,
    Neg,
    Not,

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
            Tag::Decl => TypeTableIdx,
            Tag::Call => Call,
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

    /// returns true if this instruction yields a value
    pub fn is_usable(self) -> bool {
        !matches!(self,
            Tag::BlockBegin | Tag::Ret
            | Tag::Store | Tag::Goto | Tag::Branch | Tag::Asm
        )
    }
    pub fn is_terminator(self) -> bool {
        matches!(self, Tag::Goto | Tag::Branch | Tag::Ret)
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
    pub variant_member: (Ref, u16, u16),
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
    VariantMember,
    None,
}
