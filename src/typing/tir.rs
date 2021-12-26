use std::{fmt, collections::HashMap};
use crate::types::Primitive;

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub struct SymbolKey {
    name: String
}
impl SymbolKey {
    pub fn new(name: String) -> Self {
        Self { name }
    }
    pub fn name(&self) -> &str { &self.name }
    pub fn display(&self) -> &str {
        &self.name
    }
    pub fn into_inner(self) -> String {
        self.name
    }
}

#[derive(Debug, Clone)]
pub struct Module {
    pub functions: HashMap<SymbolKey, Function>,
    pub types: HashMap<SymbolKey, Type>
}

#[derive(Debug, Clone)]
pub struct Function {
    pub header: FunctionHeader,
    pub ast: crate::ast::Function, // temporary solution?
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
    pub return_type: TypeRef
}

#[derive(Debug, Clone)]
pub enum Type {
    Struct(Struct)
}

#[derive(Debug, Clone)]
pub struct Struct {
    pub members: Vec<(String, TypeRef)>
}
impl Struct {
    pub fn size(&self, module: &Module) -> u32 {
        self.members.iter().map(|(_, m)| m.size(module)).sum()
    }
}
impl fmt::Display for Struct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ":: {{\n{}}}", self.members.iter().map(|m| format!("{} {},\n", m.0, m.1)).collect::<String>())
    }
}

#[derive(Debug, Clone)]
pub enum TypeRef {
    Primitive(Primitive),
    Resolved(SymbolKey)
}
impl TypeRef {
    pub fn size(&self, module: &Module) -> u32 {
        match self {
            TypeRef::Primitive(p) => p.size(),
            TypeRef::Resolved(key) => {
                match &module.types[key] {
                    Type::Struct(s) => s.size(module)
                }
            }
        }
    }
}
impl fmt::Display for TypeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeRef::Primitive(prim) => write!(f, "{}", prim),
            TypeRef::Resolved(key) => write!(f, "{}", key.display())
        }
    }
}