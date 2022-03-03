use std::{fmt, collections::HashMap};

use crate::types::Primitive;

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

/*
#[derive(Debug, Clone)]
pub struct Module {
    pub functions: HashMap<SymbolKey, Function>,
    pub types: HashMap<SymbolKey, Type>
}
*/

#[derive(Debug, Clone)]
pub struct Function {
    pub header: FunctionHeader,
    pub ast: crate::ast::Function, // temporary solution?
    pub ir: Vec<Instruction>,
    pub intrinsic: Option<Intrinsic>
}
impl Function {
    pub fn header(&self) -> &FunctionHeader { &self.header }
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

#[derive(Debug, Clone)]
pub enum Type {
    Struct(SymbolKey, Struct)
}

#[derive(Debug, Clone)]
pub struct Struct {
    pub members: Vec<(String, TypeRef)>
}
impl Struct {
    pub fn _size(&self, module: &IrModule) -> u32 {
        self.members.iter().map(|(_, m)| m._size(module)).sum()
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
    pub fn _size(&self, module: &IrModule) -> u32 {
        match self {
            TypeRef::Primitive(p) => p._size(),
            TypeRef::Resolved(key) => {
                match &module.types[key.idx()] {
                    Type::Struct(_, s) => s._size(module)
                }
            }
            TypeRef::Invalid => 0
        }
    }
}
impl fmt::Display for TypeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeRef::Primitive(prim) => write!(f, "Primitive({})", prim),
            TypeRef::Resolved(key) => write!(f, "Resolved({})", key.idx()),
            TypeRef::Invalid => write!(f, "Invalid")
        }
    }
}

#[derive(Clone, Debug)]
pub struct IrModule {
    pub funcs: Vec<Function>,
    pub types: Vec<Type>,
    pub symbols: HashMap<String, (SymbolType, SymbolKey)>
}

#[derive(Clone, Debug)]
pub enum Definition {
    Function(Function),
    Type(Type)
}

pub struct IrFunc(Vec<Instruction>);


#[derive(Debug, Clone, Copy)]
pub struct Instruction {
    data: Data,
    tag: Tag,
    span: TokenSpan
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

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
pub enum Tag {
    Int,
}

const INDEX_OFFSET: u32 = std::mem::variant_count::<RefVal>() as u32;

#[derive(Clone, Copy)]
pub struct Ref(u32);
impl Ref {
    pub fn val(val: RefVal) -> Self {
        Self(val as u32)
    }
    pub fn index(idx: u32) -> Self {
        Self(INDEX_OFFSET + idx)
    }
    pub fn is_val(&self) -> bool { self.0 < INDEX_OFFSET }
    pub fn is_ref(&self) -> bool { !self.is_val() }
}

#[derive(Clone, Copy)]
pub enum RefVal {
    True,
    False,
    Zero,
    One
}

#[derive(Clone, Copy)]
pub union Data {
    int: u64,
    float: f64,
    bin_op: (Ref, Ref)
}
impl fmt::Debug for Data {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.int })
    }
}