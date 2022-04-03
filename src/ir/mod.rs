use std::{fmt, num::NonZeroU8};
use colored::{Colorize, ColoredString};
use crate::{types::Primitive, lexer::Span, error::Error};
use typing::FinalTypeTable;

mod gen;
mod typing;

pub use gen::reduce;

use self::typing::{TypeInfo, TypeTable};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BaseType {
    Prim(Primitive),
    Id(SymbolKey)
}
impl fmt::Display for BaseType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BaseType::Prim(p) => write!(f, "{p}"),
            BaseType::Id(id) => write!(f, "{{t{}}}", id.idx()),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Base(BaseType),
    Pointer {
        count: NonZeroU8,
        inner: BaseType
    }
}
impl Type {
    pub fn pointer_to(self) -> Result<Self, Error> {
        Ok(match self {
            Self::Base(inner) => Self::Pointer { count: unsafe { NonZeroU8::new_unchecked(1) }, inner },
            Self::Pointer { count, inner } => {
                if count.get() == u8::MAX {
                    return Err(Error::TooLargePointer);
                }
                Self::Pointer { count: unsafe { count.unchecked_add(1) }, inner }
            }
        })
    }
}
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Base(base) => write!(f, "{base}"),
            Self::Pointer { count, inner } => write!(f, "{}{inner}", "*".repeat(count.get() as usize))
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct SymbolKey(u64);
impl SymbolKey {
    #[inline(always)]
    pub fn idx(&self) -> usize { self.0 as usize }
    pub fn bytes(&self) -> [u8; 8] { self.0.to_le_bytes() }
}

pub struct Function {
    pub name: String,
    pub header: FunctionHeader,
    pub ir: Option<FunctionIr>
}
impl Function {
    pub fn header(&self) -> &FunctionHeader { &self.header }
    pub fn finalize(self) -> FinalFunction {
        FinalFunction {
            name: self.name,
            params: self.header.params.into_iter()
                .map(|(name, ty)| (name, ty.finalize()))
                .collect(),
                varargs: self.header.varargs,
                return_type: self.header.return_type.finalize(),
                ir: self.ir
            }
    }
}
impl fmt::Display for FinalFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, (name, param)) in self.params.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{name} {param}")?;
        }
        writeln!(f, ") -> {}", self.return_type)?;

        if let Some(ir) = &self.ir {
            for (i, inst) in ir.inst.iter().enumerate() {
                if inst.tag == Tag::BlockBegin {
                    writeln!(f, "  {} {}:", "block".purple(), format!("b{}", unsafe { inst.data.int32 }).bright_blue())?;
                    continue;
                }
                write!(f, "    {:>4} = {}", 
                    format!("%{i}").cyan(),
                    inst.display(&ir.extra, &ir.types)
                )?;
                if inst.ty.is_present() {
                    writeln!(f, " :: {}", format!("{}", ir.types.get(inst.ty)).magenta())?;
                } else {
                    writeln!(f)?;
                }
            }   
        }
        Ok(())
    }
}

pub struct FinalFunction {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub varargs: bool,
    pub return_type: Type,
    pub ir: Option<FunctionIr>
}

pub struct FunctionIr {
    pub inst: Vec<Instruction>,
    pub extra: Vec<u8>,
    pub types: FinalTypeTable,
    pub block_count: u32
}

#[derive(Debug, Clone)]
pub struct FunctionHeader {
    pub name: String,
    pub params: Vec<(String, TypeRef)>,
    //pub vararg: Option<(String, TypeRef)>,
    pub varargs: bool,
    pub return_type: TypeRef
}

#[derive(Debug)]
pub enum TypeDef {
    Struct(Struct)
}
impl TypeDef {
    pub fn finalize(self) -> FinalTypeDef {
        match self {
            Self::Struct(struct_) => {
                FinalTypeDef::Struct(FinalStruct {
                    members: struct_.members.into_iter()
                        .map(|(name, member)| (name, member.finalize()))
                        .collect(),
                    name: struct_.name
                })
            }
        }
    }
}
impl fmt::Display for TypeDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let TypeDef::Struct(struct_) = self;
        write!(f, "{struct_}")
    }
}

pub enum FinalTypeDef {
    Struct(FinalStruct)
}

#[derive(Debug, Clone)]
pub struct Struct {
    pub members: Vec<(String, TypeRef)>,
    pub name: String
}
impl fmt::Display for Struct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (name, member) in &self.members {
            writeln!(f, "  {name} {member}")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct FinalStruct {
    pub members: Vec<(String, Type)>,
    pub name: String
}
impl fmt::Display for FinalStruct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (name, member) in &self.members {
            writeln!(f, "  {name} {member}")?;
        }
        Ok(())
    }
}

//TODO: fit type ref into u64 by offsetting symbol key references by the amount of primitives
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeRef {
    Base(BaseType),
    Pointer {
        count: NonZeroU8,
        inner: BaseType
    },
    Invalid,
}
impl TypeRef {
    pub fn into_info(self, types: &mut TypeTable) -> TypeInfo {
        let base_from = |base| {
            match base {
                BaseType::Prim(p) => TypeInfo::Primitive(p),
                BaseType::Id(id) => TypeInfo::Resolved(id),
            }
        };
        match self {
            TypeRef::Base(base) => base_from(base),
            TypeRef::Pointer { count, inner } => {
                let mut current = base_from(inner);
                for _ in 0..count.get() {
                    current = TypeInfo::Pointer(types.add(current))
                }
                current
            }
            TypeRef::Invalid => TypeInfo::Invalid,
        }
    }
    
    pub fn finalize(self) -> Type {
        match self {
            Self::Base(base) => Type::Base(base),
            Self::Pointer { count, inner } => Type::Pointer { count, inner },
            Self::Invalid => 
                panic!("Tried to finalize invalid type. Finalization shouldn't happen with errors present"),
        }
    }
}
impl fmt::Display for TypeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeRef::Base(base) => write!(f, "{base}"),
            TypeRef::Pointer { count, inner } => write!(f, "{}{inner}", "*".repeat(count.get() as usize)),
            TypeRef::Invalid => write!(f, "Invalid")
        }
    }
}

pub struct Module {
    pub name: String,
    pub funcs: Vec<FinalFunction>,
    pub types: Vec<FinalTypeDef>,
}
impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for FinalTypeDef::Struct(struct_) in &self.types {
            let name = &struct_.name;
            writeln!(f, "{begin} {name}\n{}{end} {name}\n",
                struct_,
                begin = "begin type".blue(),
                end  = "end type".blue()
            )?
        }
        for func in &self.funcs {
            let name = func.name.red();
            writeln!(f, "{begin} {name}{}{end} {name}\n",
                func,
                begin = "begin func".blue(),
                end = "end func".blue(),
            )?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Instruction {
    pub data: Data,
    pub tag: Tag,
    pub ty: TypeTableIndex,
    pub span: Span,
    pub used: bool
}
impl Instruction {
    pub fn display(&self, extra: &[u8], types: &FinalTypeTable) -> String {
        format!("{} {}", self.tag, self.display_data(extra, types))
    }

    fn display_data(&self, extra: &[u8], types: &FinalTypeTable) -> ColoredString {
        let write_ref = |r: Ref| {
            if let Some(val) = r.into_val() {
                format!("{val}").yellow()
            } else {
                format!("%{}", r.into_ref().unwrap()).cyan()
            }
        };
        unsafe { match self.tag.union_data_type() {
            DataVariant::Int => self.data.int.to_string().yellow(),
            DataVariant::Int32 => self.data.int32.to_string().yellow(),
            DataVariant::Block => format!("b{}", self.data.int32).bright_blue(),
            DataVariant::LargeInt => {
                let bytes = &extra[
                    self.data.extra as usize
                    .. (self.data.extra + 16) as usize
                ];
                let mut bytes_arr = [0; 16];
                bytes_arr.copy_from_slice(bytes);
                u128::from_le_bytes(bytes_arr).to_string().yellow()
            }
            DataVariant::String => {
                let bytes = &extra[
                    self.data.extra_len.0 as usize
                    .. (self.data.extra_len.0 + self.data.extra_len.1) as usize
                ];
                format!("{bytes:?}").yellow()
            }
            DataVariant::Call => {
                let start = self.data.extra_len.0 as usize;
                let mut bytes = [0; 8];
                bytes.copy_from_slice(&extra[start..start+8]);
                let func = SymbolKey(u64::from_le_bytes(bytes));
                let refs = (0..self.data.extra_len.1).map(|i| {
                    let mut ref_bytes = [0; 4];
                    let begin = 8 + start + (4 * i) as usize;
                    ref_bytes.copy_from_slice(&extra[begin..begin+4]);
                    Ref::from_bytes(ref_bytes)
                });
                let mut s = format!("{}{}(", "f".red(), func.0.to_string().red());
                for (i, r) in refs.enumerate() {
                    if i != 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&write_ref(r).to_string());
                }
                s.push(')');
                s.normal()
            }
            DataVariant::ExtraBranchRefs => {
                let mut s = String::new();
                for i in 0..self.data.extra_len.1 {
                    if i != 0 {
                        s.push_str(", ");
                    }
                    let mut current_bytes = [0; 4];
                    let begin = (self.data.extra_len.0 + i * 8) as usize;
                    current_bytes.copy_from_slice(&extra[begin..begin + 4]);
                    let block = u32::from_le_bytes(current_bytes);
                    current_bytes.copy_from_slice(&extra[begin + 4 .. begin + 8]);
                    current_bytes.copy_from_slice(&extra[begin + 4 .. begin + 8]);
                    let r = Ref::from_bytes(current_bytes);
                    s.push('[');
                    s.push_str(&format!("b{block}").bright_blue().to_string());
                    s.push_str(&write_ref(r).to_string());
                    s.push(']');
                }
                s.normal()
            }
            DataVariant::Float => self.data.float.to_string().yellow(),
            DataVariant::UnOp => write_ref(self.data.un_op),
            DataVariant::BinOp => {
                format!("{}, {}", write_ref(self.data.bin_op.0), write_ref(self.data.bin_op.1)).normal()
            }
            DataVariant::Type => types.get(self.data.ty).to_string().purple(),
            DataVariant::Member => {
                format!("{}, [member {}]", write_ref(self.data.member.0), self.data.member.1).normal()
            }
            DataVariant::Cast => {
                format!("{} as {}", write_ref(self.data.cast.0), self.data.cast.1).normal()
            }
            DataVariant::Branch => {
                let i = self.data.branch.1 as usize;
                let mut bytes = [0; 4];
                bytes.copy_from_slice(&extra[i..i+4]);
                let a = u32::from_le_bytes(bytes);
                bytes.copy_from_slice(&extra[i+4..i+8]);
                let b = u32::from_le_bytes(bytes);
                format!("{} b{a} or b{b}",
                    write_ref(self.data.branch.0),
                    a = a.to_string().bright_blue(),
                    b = b.to_string().bright_blue()
                ).normal()
            }
        }}
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Tag {
    BlockBegin,
    Ret,
    Param,
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
    Ne,
    LT,
    GT,
    LE,
    GE,

    Member,
    Cast,

    Goto,
    Branch,
    Phi
}
impl Tag {
    fn union_data_type(&self) -> DataVariant {
        use DataVariant::*;
        match self {
            Tag::BlockBegin => Int32,
            Tag::Ret => UnOp,
            Tag::Param => Int32,
            Tag::Int => Int,
            Tag::LargeInt => LargeInt,
            Tag::Float => Float,
            Tag::Decl => Type,
            Tag::Load => UnOp,
            Tag::Store => BinOp,
            Tag::String => String,
            Tag::Call => Call,
            Tag::Neg | Tag::Not => UnOp,
            Tag::Add | Tag::Sub | Tag::Mul | Tag::Div | Tag::Mod
            | Tag::Or | Tag::And    
            | Tag::Eq | Tag::Ne | Tag::LT | Tag::GT | Tag::LE | Tag::GE => BinOp,
            Tag::Member => Member,
            Tag::Cast => Cast,
            Tag::Goto => Block,
            Tag::Branch => Branch,
            Tag::Phi => ExtraBranchRefs
        }
    }

    pub fn is_untyped(&self) -> bool {
        matches!(*self, Tag::BlockBegin | Tag::Ret | Tag::Store | Tag::Goto | Tag::Branch)
    }
}
impl fmt::Display for Tag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", format!("{self:?}").bright_blue())
    }
}

const INDEX_OFFSET: u32 = std::mem::variant_count::<RefVal>() as u32;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Ref(u32);
impl Ref {
    pub const UNDEF: Self = Self::val(RefVal::Undef);

    pub const fn val(val: RefVal) -> Self {
        Self(val as u32)
    }
    pub fn index(idx: u32) -> Self {
        Self(INDEX_OFFSET + idx)
    }
    pub fn is_val(&self) -> bool { self.0 < INDEX_OFFSET }
    pub fn into_val(&self) -> Option<RefVal> {
        self.is_val().then(|| unsafe { std::mem::transmute(self.0 as u8) })
    }
    pub fn is_ref(&self) -> bool { !self.is_val() }
    pub fn into_ref(&self) -> Option<u32> {
        self.is_ref().then(|| self.0 - INDEX_OFFSET)
    }

    pub fn to_bytes(&self) -> [u8; 4] {
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

/// forces size of data to be 8 bytes
const _FORCE_DATA_SIZE: u64 = unsafe { std::mem::transmute(Data { int: 0 }) };

#[derive(Clone, Copy)]
pub union Data {
    pub int32: u32,
    pub int: u64,
    pub extra: u32,
    pub extra_len: (u32, u32),
    pub float: f64,
    pub un_op: Ref,
    pub bin_op: (Ref, Ref),
    pub ty: TypeTableIndex,
    pub member: (Ref, u32),
    pub cast: (Ref, Primitive),
    pub branch: (Ref, u32),
    pub none: (),
    pub block: BlockIndex
}
impl fmt::Debug for Data {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.int })
    }
}


#[derive(Clone, Copy)]
pub struct BlockIndex(u32);
impl BlockIndex {
    pub fn bytes(&self) -> [u8; 4] {
        self.0.to_le_bytes()
    }
}
impl fmt::Display for BlockIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "b{}", self.0)
    }
}

#[derive(Clone, Copy)]
enum DataVariant {
    Int,
    Int32,
    LargeInt,
    Block,
    Branch,
    String,
    Call,
    ExtraBranchRefs,
    Float,
    UnOp,
    BinOp,
    Type,
    Member,
    Cast
}

#[derive(Clone, Copy, Debug)]
pub struct TypeTableIndex(u32);
impl TypeTableIndex {
    pub const NONE: Self = Self(u32::MAX);

    pub fn new(idx: u32) -> Self { Self(idx) }
    pub fn idx(self) -> usize { self.0 as usize }
    pub fn is_present(self) -> bool { self.0 != u32::MAX }
}