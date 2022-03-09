use std::{collections::HashMap, fmt};
use crate::{lexer::tokens::{FloatLiteral, IntLiteral, Operator}, types::Primitive};
use self::repr::{Representer, Repr};

pub mod repr;

#[derive(Debug, Clone)]
pub struct Module {
    pub definitions: HashMap<String, Definition>
}

#[derive(Debug, Clone)]
pub enum Item {
    Definition(String, Definition),
    Block(BlockItem)
}

#[derive(Debug, Clone)]
pub enum Definition {
    Function(Function),
    Struct(StructDefinition),
}

#[derive(Debug, Clone)]
pub struct StructDefinition {
    pub members: Vec<(String, UnresolvedType, u32, u32)>,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub params: Vec<(String, UnresolvedType, u32, u32)>,
    pub vararg: Option<(String, UnresolvedType, u32, u32)>,
    pub return_type: (UnresolvedType, u32, u32),
    pub var_count: u32,
    pub body: BlockOrExpr,
}

#[derive(Debug, Clone)]
pub enum BlockOrExpr {
    Block(Block),
    Expr(Expression)
}
impl<C: Representer> Repr<C> for BlockOrExpr {
    fn repr(&self, c: &C) {
        match self {
            BlockOrExpr::Block(block) => block.repr(c),
            BlockOrExpr::Expr(expr) => expr.repr(c)
        }
    }
}

#[derive(Debug, Clone)]
pub struct Block {
    pub items: Vec<BlockItem>,
    pub defs: HashMap<String, Definition>
}

#[derive(Debug, Clone)]
pub enum BlockItem {
    Block(Block),
    Declare(String, u32, Option<UnresolvedType>, Option<Expression>),
    Assign(LValue, Expression),
    Expression(Expression),
}

#[derive(Debug, Clone)]
pub enum Expression {
    Return(Box<Expression>),
    IntLiteral(IntLiteral),
    FloatLiteral(FloatLiteral),
    StringLiteral(String),
    BoolLiteral(bool),
    Unit,
    Variable(String),
    If(Box<If>),
    FunctionCall(Box<Expression>, Vec<Expression>),
    Negate(Box<Expression>),
    BinOp(Operator, Box<(Expression, Expression)>),
    MemberAccess(Box<Expression>, String),
    Cast(Primitive, Box<Expression>)
}

#[derive(Debug, Clone)]
pub struct If {
    pub cond: Expression,
    pub then: BlockOrExpr,
    pub else_: Option<BlockOrExpr>
}

#[derive(Debug, Clone)]
pub enum LValue {
    Variable(u32, String),
    Member(Box<LValue>, String)
}
impl LValue {
    pub fn start(&self) -> u32 {
        let mut current = self;
        loop {
            match current {
                Self::Variable(start, _) => return *start,
                Self::Member(left, _) => current = &left
            };
        }
    }
    pub fn idents(&self) -> Vec<&str> {
        match self {
            Self::Variable(_, ident) => vec![ident],
            Self::Member(left, ident) => {
                let mut v = left.idents();
                v.push(ident);
                v
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnresolvedType {
    Primitive(Primitive),
    Unresolved(String)
}
impl fmt::Display for UnresolvedType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnresolvedType::Primitive(p) => p.fmt(f),
            UnresolvedType::Unresolved(name) => write!(f, "{name}")
        }
    }
}