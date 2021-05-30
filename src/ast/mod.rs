use crate::{lexer::tokens::{FloatLiteral, IntLiteral}, types::Primitive};


#[derive(Debug)]
pub struct Module {
    pub functions: Vec<Function>
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub args: Vec<(String, UnresolvedType)>,
    pub return_type: UnresolvedType,
    pub body: Block
}

#[derive(Debug)]
pub struct Block {
    pub items: Vec<BlockItem>
}

#[derive(Debug)]
pub enum BlockItem {
    Block(Block),
    Declare(String, Option<UnresolvedType>, Option<Expression>),
    Expression(Expression)
}

#[derive(Debug)]
pub enum Expression {
    Return(Box<Expression>),
    IntLiteral(IntLiteral),
    FloatLiteral(FloatLiteral),
    StringLiteral(String),
    BoolLiteral(bool),
    Variable(String)
}

#[derive(Debug)]
pub enum UnresolvedType {
    Primitive(Primitive),
    Unresolved(String)
}