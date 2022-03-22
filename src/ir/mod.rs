use std::fmt;
use colored::Colorize;
use crate::{types::Primitive, lexer::Span};


mod gen;
mod typing;

pub use gen::reduce;
pub use typing::Type;
use typing::FinalTypeTable;

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
    pub ast: crate::ast::Function, // temporary solution?
    pub ir: Option<FunctionIr>
}

impl Function {
    pub fn header(&self) -> &FunctionHeader { &self.header }
}
impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, (name, param)) in self.header.params.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{name} {param}")?;
        }
        writeln!(f, ") -> {}", self.header.return_type)?;

        let write_ref = |f: &mut fmt::Formatter, r: Ref| {
            if let Some(val) = r.into_val() {
                write!(f, "{}", format!("{val}").yellow())
            } else {
                write!(f, "{}", format!("%{}", r.into_ref().unwrap()).cyan())
            }
        };

        if let Some(ir) = &self.ir {
            for (i, inst) in ir.inst.iter().enumerate() {
                if inst.tag == Tag::BlockBegin {
                    writeln!(f, "  {} {}:", "block".purple(), format!("b{}", unsafe { inst.data.int32 }).bright_blue())?;
                    continue;
                }
                write!(f, "    {:>4} = {} ", format!("%{i}").cyan(), format!("{:?}", inst.tag).green())?;
                unsafe { match inst.tag.union_val() {
                    DataVariant::Int => write!(f, "{}", inst.data.int)?,
                    DataVariant::Int32 => write!(f, "{}", inst.data.int32)?,
                    DataVariant::Block => write!(f, "{}", format!("b{}", inst.data.int32).bright_blue())?,
                    //DataVariant::Extra(len) => write!(f, "{:?}", &self.extra[inst.data.extra as usize .. len as usize])?,
                    DataVariant::LargeInt => {
                        let bytes = &ir.extra[
                            inst.data.extra as usize
                            .. (inst.data.extra + 16) as usize
                        ];
                        let mut bytes_arr = [0; 16];
                        bytes_arr.copy_from_slice(bytes);
                        write!(f, "{:?}", u128::from_le_bytes(bytes_arr))?;
                    }
                    DataVariant::String => {
                        let bytes = &ir.extra[
                            inst.data.extra_len.0 as usize
                            .. (inst.data.extra_len.0 + inst.data.extra_len.1) as usize
                        ];
                        write!(f, "{:?}", bytes)?;
                    }
                    DataVariant::Call => {
                        let start = inst.data.extra_len.0 as usize;
                        let mut bytes = [0; 8];
                        bytes.copy_from_slice(&ir.extra[start..start+8]);
                        let func = SymbolKey(u64::from_le_bytes(bytes));
                        let refs = (0..inst.data.extra_len.1).map(|i| {
                            let mut ref_bytes = [0; 4];
                            let begin = 8 + start + (4 * i) as usize;
                            ref_bytes.copy_from_slice(&ir.extra[begin..begin+4]);
                            Ref::from_bytes(ref_bytes)
                        });
                        write!(f, "f{}(", func.0)?;
                        for (i, r) in refs.enumerate() {
                            if i != 0 {
                                write!(f, ", ")?;
                            }
                            write_ref(f, r)?;
                        }
                        write!(f, ")")?;
                    }
                    DataVariant::ExtraBranchRefs => {
                        for i in 0..inst.data.extra_len.1 {
                            if i != 0 {
                                write!(f, ", ")?;
                            }
                            let mut current_bytes = [0; 4];
                            let begin = (inst.data.extra_len.0 + i * 8) as usize;
                            current_bytes.copy_from_slice(&ir.extra[begin..begin + 4]);
                            let block = u32::from_le_bytes(current_bytes);
                            current_bytes.copy_from_slice(&ir.extra[begin + 4 .. begin + 8]);
                            current_bytes.copy_from_slice(&ir.extra[begin + 4 .. begin + 8]);
                            let r = Ref::from_bytes(current_bytes);
                            write!(f, "[{} ", format!("b{block}").bright_blue())?;
                            write_ref(f, r)?;
                            write!(f, "]")?;
                        }
                    }
                    DataVariant::Float => write!(f, "{}", inst.data.float)?,
                    DataVariant::UnOp => write_ref(f, inst.data.un_op)?,
                    DataVariant::BinOp => {
                        write_ref(f, inst.data.bin_op.0)?;
                        write!(f, ", ")?;
                        write_ref(f, inst.data.bin_op.1)?;
                    }
                    DataVariant::Type => write!(f, "{}", ir.types.get(inst.data.ty))?,
                    DataVariant::Member => {
                        write_ref(f, inst.data.member.0)?;
                        write!(f, ", [member {}]", inst.data.member.1)?;
                    }
                    DataVariant::Cast => {
                        write_ref(f, inst.data.cast.0)?;
                        write!(f, " as {}", inst.data.cast.1)?;
                    }
                    DataVariant::Branch => {
                        write_ref(f, inst.data.branch.0)?;
                        let i = inst.data.branch.1 as usize;
                        let mut bytes = [0; 4];
                        bytes.copy_from_slice(&ir.extra[i..i+4]);
                        let a = u32::from_le_bytes(bytes);
                        bytes.copy_from_slice(&ir.extra[i+4..i+8]);
                        let b = u32::from_le_bytes(bytes);
                        write!(f, " b{a} or b{b}")?;
                    }
                }}
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
impl fmt::Display for TypeDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let TypeDef::Struct(struct_) = self;
        write!(f, "{struct_}")
    }
}

#[derive(Debug, Clone)]
pub struct Struct {
    pub members: Vec<(String, TypeRef)>,
    pub name: String
}
impl Struct {
    pub fn _size(&self, module: &Module) -> u32 {
        self.members.iter().map(|(_, m)| m._size(module)).sum()
    }
}
impl fmt::Display for Struct {
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
    Primitive(Primitive),
    Resolved(SymbolKey),
    Invalid,
}
impl TypeRef {
    pub fn _size(&self, module: &Module) -> u32 {
        match self {
            TypeRef::Primitive(p) => p._size(),
            TypeRef::Resolved(key) => {
                match &module.types[key.idx()] {
                    TypeDef::Struct(s) => s._size(module)
                }
            }
            TypeRef::Invalid => 0
        }
    }
}
impl fmt::Display for TypeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeRef::Primitive(prim) => write!(f, "{}", prim),
            TypeRef::Resolved(key) => write!(f, "{}", key.idx()),
            TypeRef::Invalid => write!(f, "Invalid")
        }
    }
}

pub struct Module {
    pub name: String,
    pub funcs: Vec<Function>,
    pub types: Vec<TypeDef>,
}
impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for TypeDef::Struct(struct_) in &self.types {
            let name = &struct_.name;
            writeln!(f, "{begin} {name}\n{}{end} {name}\n",
                struct_,
                begin = "begin type".blue(),
                end  = "end type".blue()
            )?
        }
        for func in &self.funcs {
            let name = func.name.yellow();
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
    pub span: Span
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
    fn union_val(&self) -> DataVariant {
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
            | Tag::Eq | Tag::Ne | Tag::LT | Tag::GT | Tag::LE | Tag::GE => BinOp,
            Tag::Member => Member,
            Tag::Cast => Cast,
            Tag::Goto => Block,
            Tag::Branch => Branch,
            Tag::Phi => ExtraBranchRefs
        }
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
    pub none: ()
}
impl fmt::Debug for Data {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.int })
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