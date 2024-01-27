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
    /// special tag that marks the beginning of a new block, this might not be needed in the future
    BlockBegin,

    /// Get a function parameter. Type has to match the signature
    Param,

    /// decide on the value depending on previously visited block
    Phi,

    // block terminators
    /// return from the current function
    Ret,
    /// jump to another basic block
    Goto,
    /// jump to one of two basic blocks depending on the passed in u1 value
    Branch,

    /// uninitialized value, undefined when used
    Uninit,

    /// extract an element value out of a tuple
    MemberValue,

    /// integer with up to 64 bits in size
    Int,
    /// integer larger than 64 bits, currently always 128 bits
    LargeInt,
    /// float constant, either f32 or f64
    Float,

    // pointer operations
    /// declare a stack variable
    Decl,
    /// load a value from a ptr
    Load,
    /// store a value to a ptr
    Store,
    /// get a member ptr of a ptr to a tuple
    MemberPtr,

    // FIXME: strings should be normal constants
    /// string constant
    String,
    /// call a function
    Call,

    // unary operations
    /// negate an integer or float value
    Neg,
    /// boolean not
    Not,

    // arithmetic binary ops
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    Or,
    And,

    // comparisons
    Eq,
    NE,
    LT,
    GT,
    LE,
    GE,

    Cast,

    Asm,
}
impl Tag {
    pub fn union_data_type(self) -> DataVariant {
        use DataVariant as V;
        match self {
            Tag::BlockBegin | Tag::Param => V::Int32,
            Tag::Uninit => V::None,
            Tag::Ret | Tag::Load | Tag::Neg | Tag::Not | Tag::Cast => V::UnOp,
            Tag::Int => V::Int,
            Tag::LargeInt => V::LargeInt,
            Tag::Float => V::Float,
            Tag::String => V::String,
            Tag::Decl => V::TypeTableIdx,
            Tag::Call => V::Call,
            Tag::MemberPtr => V::MemberPtr,
            Tag::Store | Tag::Add | Tag::Sub | Tag::Mul | Tag::Div | Tag::Mod
            | Tag::Or | Tag::And    
            | Tag::Eq | Tag::NE | Tag::LT | Tag::GT | Tag::LE | Tag::GE => V::BinOp,

            Tag::MemberValue => V::RefInt,
            Tag::Goto => V::Block,
            Tag::Branch => V::Branch,
            Tag::Phi => V::ExtraBranchRefs,
            Tag::Asm => V::Asm,

            //Tag::EnumTag | Tag::EnumValueTag => UnOp,
            //Tag::EnumVariantMember | Tag::EnumValueVariantMember => VariantMember,
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
    /// extra_index, length of string, amount of arguments
    pub asm: (u32, u16, u16),
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
    MemberPtr,
    Branch,
    String,
    Call,
    ExtraBranchRefs,
    Float,
    UnOp,
    BinOp,
    RefInt,
    Asm,
    None,
}
