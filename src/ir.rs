use std::{collections::HashMap, fmt::{self, Debug}};

#[derive(Clone, Copy, Debug)]
pub struct SymbolKey(u64);

pub struct SymbolTable {
    ids: HashMap<String, SymbolKey>,
    names: Vec<String> // index with symbol keys
}
impl SymbolTable {
    pub fn new() -> Self {
        Self {
            ids: HashMap::new(),
            names: Vec::new()
        }
    }

    pub fn add(&mut self, name: String) -> SymbolKey {
        self.names.push(name.clone());
        let key = SymbolKey((self.names.len() - 1) as u64);
        self.ids.insert(name, key);
        key
    }
}

pub struct IrModule {
    defs: HashMap<SymbolKey, Definition>
}

pub enum Definition {
    Function(Vec<Instruction>),
    Struct(Vec<SymbolKey>)
}

pub struct IrFunc(Vec<Instruction>);


#[derive(Debug, Clone, Copy)]
pub struct Instruction {
    data: Data,
    tag: Tag,
    span: TokenSpan
}

#[derive(Clone, Copy)]
/// 24-bit numbers for start and end token
pub struct TokenSpan([u8; 6]);
impl TokenSpan {
    pub fn new(start: u32, end: u32) -> Self {
        debug_assert!(start < 16777216);
        debug_assert!(end   < 16777216);
        Self([
            (start >> 16) as u8,
            (start >>  8) as u8,
            (start >>  0) as u8,
            (end   >> 16) as u8,
            (end   >>  8) as u8,
            (end   >>  0) as u8,
        ])
    }
    
    pub fn start(&self) -> u32 {
          self.0[0] as u32 >> 16
        | self.0[1] as u32 >>  8
        | self.0[2] as u32 >>  0
    }
    
    pub fn end(&self) -> u32 {
        self.0[3] as u32 >> 16
      | self.0[4] as u32 >>  8
      | self.0[5] as u32 >>  0
    }
}
impl fmt::Display for TokenSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start(), self.end())
    }
}
impl Debug for TokenSpan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TokenSpan({}, {})", self.start(), self.end())
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
impl Debug for Data {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.int })
    }
}