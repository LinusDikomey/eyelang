use std::collections::HashMap;
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
}

#[derive(Debug)]
pub struct Module {
    pub functions: HashMap<SymbolKey, Function>,
    pub types: HashMap<SymbolKey, Type>
}

#[derive(Debug)]
pub struct Function {
    pub header: FunctionHeader
}
impl Function {
    pub fn header(&self) -> &FunctionHeader { &self.header }
}

#[derive(Debug)]
pub struct FunctionHeader {
    pub args: Vec<(String, TypeRef)>,
    pub return_type: TypeRef
}

#[derive(Debug)]
pub enum Type {
    Struct(Struct)
}

#[derive(Debug)]
pub struct Struct {
    pub members: Vec<(String, TypeRef)>
}
impl Struct {
    pub fn size(&self, module: &Module) -> u32 {
        self.members.iter().map(|(_, m)| m.size(module)).sum()
    }
}

#[derive(Debug)]
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