use std::{fmt, collections::HashMap};
use crate::{types::Primitive, typecheck::TypeTable};

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum SymbolType {
    Func,
    Type
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct SymbolKey(u64);
impl SymbolKey {
    pub fn new(idx: u64) -> Self {
        Self(idx)
    }
    
    pub fn idx(&self) -> usize { self.0 as usize }
}

pub struct Function {
    pub header: FunctionHeader,
    pub ast: crate::ast::Function, // temporary solution?
    pub ir: Vec<Instruction>,
    pub extra: Vec<u8>,
    pub intrinsic: Option<Intrinsic>,
    pub types: TypeTable
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
                write!(f, "{}", val)
            } else {
                write!(f, "%{}", r.into_ref().unwrap())
            }
        };

        for (i, inst) in self.ir.iter().enumerate() {
            if inst.tag == Tag::BlockBegin {
                writeln!(f, "  block {}:", unsafe { inst.data.int32 })?;
                continue;
            }
            write!(f, "    {:>4} = {:?} ", format!("%{i}"), inst.tag)?;
            unsafe { match inst.tag.union_val() {
                DataVariant::Int => write!(f, "{}", inst.data.int)?,
                DataVariant::Int32 => write!(f, "{}", inst.data.int32)?,
                DataVariant::Extra(len) => write!(f, "{:?}", &self.extra[inst.data.extra as usize .. len as usize])?,
                DataVariant::LargeInt => {
                    let bytes = &self.extra[
                        inst.data.extra as usize
                        .. (inst.data.extra + 16) as usize
                    ];
                    let mut bytes_arr = [0; 16];
                    bytes_arr.copy_from_slice(bytes);
                    write!(f, "{:?}", u128::from_le_bytes(bytes_arr))?;
                }
                DataVariant::ExtraLen(elems) => {
                    let bytes = &self.extra[
                        inst.data.extra_len.0 as usize
                        .. (inst.data.extra_len.0 + inst.data.extra_len.1 * elems.size()) as usize
                    ];
                    match elems {
                        ElemTy::Byte => write!(f, "{:?}", bytes)?,
                        ElemTy::Ref => {
                            let refs = (0..inst.data.extra_len.1).map(|i| {
                                let mut ref_bytes = [0; 4];
                                let begin = (i * elems.size()) as usize;
                                let end = begin + elems.size() as usize;
                                ref_bytes.copy_from_slice(&bytes[begin..end]);
                                Ref::from_bytes(ref_bytes)
                            });
                            write!(f, "(")?;
                            for (i, r) in refs.enumerate() {
                                if i != 0 {
                                    write!(f, ", ")?;
                                }
                                write_ref(f, r)?;
                            }
                            write!(f, ")")?;
                            
                        }
                    }
                }
                DataVariant::Float => write!(f, "{}", inst.data.float)?,
                DataVariant::UnOp => write_ref(f, inst.data.un_op)?,
                DataVariant::BinOp => {
                    write_ref(f, inst.data.bin_op.0)?;
                    write!(f, ", ")?;
                    write_ref(f, inst.data.bin_op.1)?;
                }
                DataVariant::Member => {
                    write_ref(f, inst.data.member.0)?;
                    write!(f, ", [member {}]", inst.data.member.1)?;
                }
                DataVariant::Cast => {
                    write_ref(f, inst.data.cast.0)?;
                    write!(f, " as {}", inst.data.cast.1)?;
                }
                DataVariant::None => {}
            }}
            writeln!(f, " :: {}", self.types.get_type(inst.ty).0)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum Intrinsic {
    Print,
    Read,
    Parse
}

#[derive(Debug, Clone)]
pub struct FunctionHeader {
    pub params: Vec<(String, TypeRef)>,
    pub vararg: Option<(String, TypeRef)>,
    pub return_type: TypeRef
}

#[derive(Debug)]
pub enum Type {
    Struct(Struct)
}

#[derive(Debug, Clone)]
pub struct Struct {
    pub members: Vec<(String, TypeRef)>
}
impl Struct {
    pub fn _size(&self, module: &Module) -> u32 {
        self.members.iter().map(|(_, m)| m._size(module)).sum()
    }

    pub fn member_index(&self, name: &str) -> Option<usize> {
        self.members.iter()
            .enumerate()
            .find(|(_, (member_name, _))| member_name == name)
            .map(|(i, _)| i)
    }
}
impl fmt::Display for Struct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ":: {{\n{}}}", self.members.iter().map(|m| format!("{} {},\n", m.0, m.1)).collect::<String>())
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
                    Type::Struct(s) => s._size(module)
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
    pub funcs: Vec<Function>,
    pub types: Vec<Type>,
    pub symbols: HashMap<String, (SymbolType, SymbolKey)>
}
impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (name, (symbol_ty, key)) in &self.symbols {
            match symbol_ty {
                SymbolType::Func => writeln!(f, "begin func {name}: {}end func {name}\n", self.funcs[key.idx()])?,
                SymbolType::Type => writeln!(f, "begin type {name}: {:?}end type {name}\n", self.types[key.idx()])?
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Instruction {
    pub data: Data,
    pub tag: Tag,
    pub ty: TypeTableIndex,
    pub span: TokenSpan
}

#[derive(Clone, Copy)]
pub struct TokenSpan {
    pub start: u32,
    pub end: u32
}

impl TokenSpan {
    pub const MAX: u32 = 16_777_215;
    pub fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }
}
impl fmt::Display for TokenSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}
impl fmt::Debug for TokenSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TokenSpan({}, {})", self.start, self.end)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Tag {
    BlockBegin,
    Ret,
    Invalid,
    Param,
    Int,
    LargeInt,
    Float,
    Declare,
    String,
    Call,
    Neg,

    Add,
    Sub,
    Mul,
    Div,

    Eq,
    LT,
    GT,
    LE,
    GE,

    Member,
    Cast
}
impl Tag {
    pub fn union_val(&self) -> DataVariant {
        use DataVariant::*;
        match self {
            Tag::BlockBegin => Int32,
            Tag::Ret => UnOp,
            Tag::Invalid => None,
            Tag::Param => None,
            Tag::Int => Int,
            Tag::LargeInt => LargeInt,
            Tag::Float => Float,
            Tag::Declare => UnOp,
            Tag::String => ExtraLen(ElemTy::Byte),
            Tag::Call => ExtraLen(ElemTy::Ref),
            Tag::Neg => UnOp,
            Tag::Add | Tag::Sub | Tag::Mul | Tag::Div
            | Tag::Eq | Tag::LT | Tag::GT | Tag::LE | Tag::GE => BinOp,
            Tag::Member => Member,
            Tag::Cast => Cast,
        }
    }
}

const INDEX_OFFSET: u32 = std::mem::variant_count::<RefVal>() as u32;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Ref(u32);
impl Ref {
    pub fn val(val: RefVal) -> Self {
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

#[derive(Clone, Copy)]
pub enum RefVal {
    True,
    False,
    Zero,
    One,
    Unit,
    Undef
}
impl fmt::Display for RefVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RefVal::True => write!(f, "true"),
            RefVal::False => write!(f, "false"),
            RefVal::Zero => write!(f, "0"),
            RefVal::One => write!(f, "1"),
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
    pub member: (Ref, u32),
    pub cast: (Ref, Primitive),
    pub none: ()
}
impl fmt::Debug for Data {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.int })
    }
}

#[derive(Clone, Copy)]
enum ElemTy {
    Byte,
    Ref
}
impl ElemTy {
    fn size(&self) -> u32 {
        match self {
            ElemTy::Byte => 1,
            ElemTy::Ref => 4,
        }
    }
}

#[derive(Clone, Copy)]
enum DataVariant {
    Int,
    Int32,
    LargeInt,
    Extra(u32),
    ExtraLen(ElemTy),
    Float,
    UnOp,
    BinOp,
    Member,
    Cast,
    None
}

#[derive(Clone, Copy, Debug)]
pub struct TypeTableIndex(u32);
impl TypeTableIndex {
    pub fn new(idx: u32) -> Self { Self(idx) }
    pub fn idx(self) -> usize { self.0 as usize }
}