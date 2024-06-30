use std::fmt;

use color_format::cwrite;

use crate::GlobalId;

use super::{ir_types::TypeRef, BlockIndex, Ref};

#[derive(Debug, Clone, Copy)]
pub struct Instruction {
    pub data: Data,
    pub tag: Tag,
    pub ty: TypeRef,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
#[allow(unused)] // FIXME: these instructions should be cleaned up if they still aren't used
pub enum Tag {
    /// get a pointer to a global
    Global,

    /// Block arg pseudo-instruction to give each block arg a Ref. Will be inserted automatically
    /// and should never be present inside the block itself.
    BlockArg,

    // block terminators
    /// return from the current function
    Ret,
    /// jump to another basic block
    Goto,
    /// jump to one of two basic blocks depending on the passed in u1 value
    Branch,

    /// uninitialized value, undefined when used
    Uninit,

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
    /// extract an element value out of a tuple
    MemberValue,
    /// Get a pointer to an array element. Element type has to be provided along with an index.
    ArrayIndex,

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

    // casts
    CastInt,
    CastFloat,
    CastIntToFloat,
    CastFloatToInt,

    // convert pointers from/to integer
    IntToPtr,
    PtrToInt,

    Asm,
}
impl Tag {
    pub fn union_data_type(self) -> DataVariant {
        use DataVariant as V;
        match self {
            Tag::BlockArg => unreachable!(),
            Tag::Global => V::Global,
            Tag::Uninit => V::None,
            Tag::Ret
            | Tag::Load
            | Tag::Neg
            | Tag::Not
            | Tag::CastInt
            | Tag::CastFloat
            | Tag::CastIntToFloat
            | Tag::CastFloatToInt
            | Tag::IntToPtr
            | Tag::PtrToInt => V::UnOp,
            Tag::Int => V::Int,
            Tag::LargeInt => V::LargeInt,
            Tag::Float => V::Float,
            Tag::String => V::String,
            Tag::Decl => V::TypeTableIdx,
            Tag::Call => V::Call,
            Tag::MemberPtr => V::MemberPtr,
            Tag::ArrayIndex => V::ArrayIndex,
            Tag::Store
            | Tag::Add
            | Tag::Sub
            | Tag::Mul
            | Tag::Div
            | Tag::Mod
            | Tag::Or
            | Tag::And
            | Tag::Eq
            | Tag::NE
            | Tag::LT
            | Tag::GT
            | Tag::LE
            | Tag::GE => V::BinOp,

            Tag::MemberValue => V::RefInt,
            Tag::Goto => V::Goto,
            Tag::Branch => V::Branch,
            Tag::Asm => V::Asm,
            //Tag::EnumTag | Tag::EnumValueTag => UnOp,
            //Tag::EnumVariantMember | Tag::EnumValueVariantMember => VariantMember,
        }
    }

    /// returns true if this instruction yields a value
    pub fn is_usable(self) -> bool {
        !matches!(
            self,
            Tag::Ret | Tag::Store | Tag::Goto | Tag::Branch | Tag::Asm
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
/// Data is encoded "unsafely" in an untagged union so that the Tag can be split from the data for
/// more efficient "SOA" data representation. In reality, this is all still safe since essentially
/// only primitive integers are encoded in here and in the worst case, an invalid index is
/// retrieved which shouldn't cause any unsafety. For this reason, safe getters for the variants
/// are provided for easier access.
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
    pub block_extra: (BlockIndex, u32),
    pub global: GlobalId,
}
impl Data {
    pub fn int(self) -> u64 {
        unsafe { self.int }
    }

    pub fn extra(self) -> u32 {
        unsafe { self.extra }
    }

    pub fn extra_len(self) -> (u32, u32) {
        unsafe { self.extra_len }
    }

    pub fn ty(self) -> TypeRef {
        unsafe { self.ty }
    }

    pub fn float(self) -> f64 {
        unsafe { self.float }
    }

    pub fn un_op(self) -> Ref {
        unsafe { self.un_op }
    }

    pub fn bin_op(self) -> (Ref, Ref) {
        unsafe { self.bin_op }
    }

    pub fn goto<'a>(
        self,
        extra: &'a [u8],
    ) -> (BlockIndex, impl 'a + ExactSizeIterator<Item = Ref>) {
        let (i, n) = self.extra_len();
        let i = i as usize;
        let mut bytes = [0; 4];
        bytes.copy_from_slice(&extra[i..i + 4]);
        let block = BlockIndex::from_bytes(bytes);
        (
            block,
            (0..n).map(move |x| {
                let i = i + 4 + 4 * x as usize;
                bytes.copy_from_slice(&extra[i..i + 4]);
                Ref::from_bytes(bytes)
            }),
        )
    }

    pub fn branch(&self, extra: &[u8]) -> (Ref, BlockIndex, BlockIndex) {
        let (r, i) = unsafe { self.ref_int };
        let mut bytes = [0; 4];
        let i = i as usize;
        bytes.copy_from_slice(&extra[i..i + 4]);
        let a = BlockIndex::from_bytes(bytes);
        bytes.copy_from_slice(&extra[i + 4..i + 8]);
        let b = BlockIndex::from_bytes(bytes);
        (r, a, b)
    }

    pub fn ref_int(self) -> (Ref, u32) {
        unsafe { self.ref_int }
    }

    pub fn phi<'a>(
        &self,
        extra: &'a [u8],
    ) -> impl 'a + ExactSizeIterator<Item = (BlockIndex, Ref)> {
        let (offset, n) = unsafe { self.extra_len };
        (0..n).map(move |i| {
            let c = offset as usize + i as usize * 8;
            let mut b = [0; 4];
            b.copy_from_slice(&extra[c..c + 4]);
            let block = BlockIndex::from_bytes(b);
            b.copy_from_slice(&extra[c + 4..c + 8]);
            let r = Ref::from_bytes(b);
            (block, r)
        })
    }
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
    Global,
    TypeTableIdx,
    Goto,
    MemberPtr,
    ArrayIndex,
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
