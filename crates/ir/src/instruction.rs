use std::fmt;

use color_format::cwrite;

use crate::{FunctionId, FunctionIr, GlobalId, TypeRefs};

use super::{ir_types::TypeRef, BlockIndex, Ref};

#[derive(Debug, Clone, Copy)]
pub struct Instruction {
    pub data: Data,
    pub tag: Tag,
    pub ty: TypeRef,
}

macro_rules! un_op_insts {
    ($($name: ident $tag: ident)*) => {
        $(
            pub fn $name(value: Ref, ty: TypeRef) -> Self {
                Self {
                    data: Data { un_op: value },
                    tag: Tag::$tag,
                    ty,
                }
            }
        )*
    };
}

macro_rules! bin_op_insts {
    ($($name: ident $tag: ident)*) => {
        $(
            pub fn $name(l: Ref, r: Ref, ty: TypeRef) -> Self {
                Self {
                    data: Data { bin_op: (l, r) },
                    tag: Tag::$tag,
                    ty,
                }
            }
        )*
    };
}
impl Instruction {
    pub const NOTHING: Self = Self {
        data: Data { none: () },
        tag: Tag::Nothing,
        ty: TypeRef::NONE,
    };

    pub fn int(value: u64, ty: TypeRef) -> Self {
        Self {
            data: Data { int: value },
            tag: Tag::Int,
            ty,
        }
    }

    pub fn float(value: f64, ty: TypeRef) -> Self {
        Self {
            data: Data { float: value },
            tag: Tag::Float,
            ty,
        }
    }

    un_op_insts! {
        ret Ret

        load Load

        neg Neg
        not Not

        int_to_ptr IntToPtr
        ptr_to_int PtrToInt

    }

    bin_op_insts! {
        store Store

        add Add
        sub Sub
        mul Mul
        div Div
        rem Rem

        or Or
        and And

        eq Eq
        ne NE
        lt LT
        gt GT
        le LE
        ge GE
    }

    pub fn visit_refs(&self, ir: &FunctionIr, mut visit: impl FnMut(Ref)) {
        match self.tag.union_data_type() {
            DataVariant::Int
            | DataVariant::LargeInt
            | DataVariant::Float
            | DataVariant::Global
            | DataVariant::TypeTableIdx
            | DataVariant::String
            | DataVariant::None
            | DataVariant::Function => {}
            DataVariant::MemberPtr | DataVariant::RefInt => visit(self.data.ref_int().0),
            DataVariant::RefIntRef => {
                let (r, i) = self.data.ref_int();
                visit(r);
                visit(Ref::from_bytes(
                    ir.extra[i as usize + 4..i as usize + 8].try_into().unwrap(),
                ));
            }
            DataVariant::ArrayIndex => {
                let (array_ptr, _elem_ty, index_ref) = self.data.array_index(&ir.extra);
                visit(array_ptr);
                visit(index_ref);
            }
            DataVariant::Call => {
                let (idx, arg_count) = self.data.extra_len();
                for i in (idx as usize + 8..).step_by(4).take(arg_count as usize) {
                    let r = Ref::from_bytes(ir.extra[i..i + 4].try_into().unwrap());
                    visit(r);
                }
            }
            DataVariant::CallPtr => {
                let (func, _, params) = self.data.call_ptr(&ir.extra);
                visit(func);
                for param in params {
                    visit(param);
                }
            }
            DataVariant::Goto => {
                let (block, extra_idx) = self.data.goto();
                for i in (extra_idx..)
                    .step_by(4)
                    .take(ir.get_block_args(block).count())
                {
                    let r = Ref::from_bytes(ir.extra[i..i + 4].try_into().unwrap());
                    visit(r);
                }
            }
            DataVariant::Branch => {
                let (cond, a, b, extra_idx) = self.data.branch(&ir.extra);
                visit(cond);
                let total_args = ir.get_block_args(a).count() + ir.get_block_args(b).count();
                for i in (extra_idx..).step_by(4).take(total_args) {
                    let r = Ref::from_bytes(ir.extra[i..i + 4].try_into().unwrap());
                    visit(r);
                }
            }
            DataVariant::UnOp => visit(self.data.un_op()),
            DataVariant::BinOp => {
                visit(self.data.bin_op().0);
                visit(self.data.bin_op().1);
            }
            DataVariant::Asm => todo!("handle asm inst in Instruction ref visitor"),
        };
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
#[allow(unused)] // FIXME: these instructions should be cleaned up if they still aren't used
pub enum Tag {
    /// instruction that does nothing. Used as a placeholder and when optimizations delete
    /// instructions and can be safely ignored.
    Nothing,
    /// Block arg pseudo-instruction to give each block arg a Ref. Will be inserted automatically
    /// and should never be present inside the block itself.
    BlockArg,

    /// get a pointer to a global
    Global,

    // block terminators
    /// return from the current function
    Ret,
    /// jump to another basic block
    Goto,
    /// jump to one of two basic blocks depending on the passed in u1 value
    Branch,

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
    /// insert a member into a tuple resulting in a new, modified tuple
    InsertMember,
    /// Get a pointer to an array element. Element type has to be provided along with an index.
    ArrayIndex,

    // FIXME: strings should be normal constants
    /// string constant
    String,
    /// call a function
    Call,
    /// gets a pointer to a function
    FunctionPtr,
    /// calls a function behind a function pointer
    CallPtr,

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
    Rem,

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
            Tag::Nothing => V::None,
            Tag::BlockArg => unreachable!(),
            Tag::Global => V::Global,
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
            | Tag::Rem
            | Tag::Or
            | Tag::And
            | Tag::Eq
            | Tag::NE
            | Tag::LT
            | Tag::GT
            | Tag::LE
            | Tag::GE => V::BinOp,

            Tag::MemberValue => V::RefInt,
            Tag::InsertMember => V::RefIntRef,
            Tag::Goto => V::Goto,
            Tag::Branch => V::Branch,
            Tag::FunctionPtr => V::Function,
            Tag::CallPtr => V::CallPtr,
            Tag::Asm => V::Asm,
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

    pub fn has_side_effect(self) -> bool {
        match self {
            Tag::Nothing
            | Tag::BlockArg
            | Tag::Global
            | Tag::Int
            | Tag::LargeInt
            | Tag::Float
            | Tag::Load
            | Tag::MemberPtr
            | Tag::MemberValue
            | Tag::ArrayIndex
            | Tag::String
            | Tag::FunctionPtr
            | Tag::Neg
            | Tag::Not
            | Tag::Add
            | Tag::Sub
            | Tag::Mul
            | Tag::Div
            | Tag::Rem
            | Tag::Or
            | Tag::And
            | Tag::Eq
            | Tag::NE
            | Tag::LT
            | Tag::GT
            | Tag::LE
            | Tag::GE
            | Tag::CastInt
            | Tag::CastFloat
            | Tag::CastIntToFloat
            | Tag::CastFloatToInt
            | Tag::IntToPtr
            | Tag::PtrToInt => false,
            Tag::InsertMember => false,

            Tag::Ret
            | Tag::Goto
            | Tag::Branch
            | Tag::Decl
            | Tag::Store
            | Tag::Call
            | Tag::CallPtr
            | Tag::Asm => true,
        }
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
    pub function: FunctionId,
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

    pub fn goto(self) -> (BlockIndex, usize) {
        let (block, extra_index) = unsafe { self.block_extra };
        (block, extra_index as usize)
    }

    pub fn function(self) -> FunctionId {
        unsafe { self.function }
    }

    pub fn branch(&self, extra: &[u8]) -> (Ref, BlockIndex, BlockIndex, usize) {
        let (r, i) = self.ref_int();
        let mut bytes = [0; 4];
        let i = i as usize;
        bytes.copy_from_slice(&extra[i..i + 4]);
        let a = BlockIndex::from_bytes(bytes);
        bytes.copy_from_slice(&extra[i + 4..i + 8]);
        let b = BlockIndex::from_bytes(bytes);
        (r, a, b, i + 8)
    }

    pub fn call<'a>(
        &self,
        extra: &'a [u8],
    ) -> (FunctionId, impl 'a + ExactSizeIterator<Item = Ref>) {
        let (start, arg_count) = self.extra_len();
        let start = start as usize;
        let mut bytes = [0; 8];
        bytes.copy_from_slice(&extra[start..start + 8]);
        let func = FunctionId::from_bytes(bytes);
        let args = (0..arg_count).map(move |i| {
            let mut ref_bytes = [0; 4];
            let begin = 8 + start + (4 * i) as usize;
            ref_bytes.copy_from_slice(&extra[begin..begin + 4]);
            Ref::from_bytes(ref_bytes)
        });
        (func, args)
    }

    pub fn call_ptr<'a>(
        &self,
        extra: &'a [u8],
    ) -> (Ref, TypeRefs, impl 'a + ExactSizeIterator<Item = Ref>) {
        let (i, arg_count) = self.extra_len();
        let i = i as usize;
        let func = Ref::from_bytes(extra[i..i + 4].try_into().unwrap());
        let arg_types = TypeRefs::from_bytes(extra[i + 4..i + 12].try_into().unwrap());
        let args = (0..arg_count).map(move |arg| {
            let i = i + 12 + 4 * arg as usize;
            Ref::from_bytes(extra[i..i + 4].try_into().unwrap())
        });
        (func, arg_types, args)
    }

    pub fn ref_int(self) -> (Ref, u32) {
        unsafe { self.ref_int }
    }

    pub fn global(self) -> GlobalId {
        unsafe { self.global }
    }

    pub fn ref_int_ref(self, extra: &[u8]) -> (Ref, u32, Ref) {
        let (r1, i) = self.ref_int();
        let i = i as usize;
        let int = u32::from_le_bytes(extra[i..i + 4].try_into().unwrap());
        let r2 = Ref::from_bytes(extra[i + 4..i + 8].try_into().unwrap());
        (r1, int, r2)
    }

    pub fn array_index(&self, extra: &[u8]) -> (Ref, TypeRef, Ref) {
        let (array_ptr, extra_start) = self.ref_int();
        let i = extra_start as usize;
        let elem_ty = TypeRef::from_bytes(extra[i..i + 4].try_into().unwrap());
        let index_ref = Ref::from_bytes(extra[i + 4..i + 8].try_into().unwrap());
        (array_ptr, elem_ty, index_ref)
    }

    pub fn member_ptr(&self, extra: &[u8]) -> (Ref, TypeRefs, u32) {
        let (ptr, extra_start) = self.ref_int();
        let i = extra_start as usize;
        let elem_refs = TypeRefs::from_bytes(extra[i..i + 8].try_into().unwrap());
        let elem_idx = u32::from_le_bytes(extra[i + 8..i + 12].try_into().unwrap());
        (ptr, elem_refs, elem_idx)
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
    LargeInt,
    Float,
    Global,
    TypeTableIdx,
    MemberPtr,
    ArrayIndex,
    Goto,
    Branch,
    String,
    Call,
    Function,
    CallPtr,
    UnOp,
    BinOp,
    RefInt,
    RefIntRef,
    Asm,
    None,
}
