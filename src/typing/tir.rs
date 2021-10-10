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
    pub args: Vec<(String, TypeRef)>
}

#[derive(Debug)]
pub enum Type {
    Struct(Struct)
}

#[derive(Debug)]
pub struct Struct {
    
}

#[derive(Debug)]
pub enum TypeRef {
    Primitive(Primitive),
    Resolved(SymbolKey)
}