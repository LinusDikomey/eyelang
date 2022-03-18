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
    //pub vararg: Option<(String, UnresolvedType, u32, u32)>,
    pub varargs: bool,
    pub return_type: (UnresolvedType, u32, u32),
    pub var_count: u32,
    pub body: Option<BlockOrExpr>,
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

pub fn insert_intrinsics(module: &mut Module) {
    module.definitions.insert("print".to_owned(), Definition::Function(Function {
        body: Some(BlockOrExpr::Block(Block { items: Vec::new(), defs: HashMap::new() })),
        params: Vec::new(),
        varargs: true, //Some(("args".to_owned(), UnresolvedType::Primitive(Primitive::String), 0, 0)),
        var_count: 0,
        return_type: (UnresolvedType::Primitive(Primitive::Unit), 0, 0)
    }));
    module.definitions.insert("read".to_owned(), Definition::Function(Function {
        body: Some(BlockOrExpr::Expr(Expression::StringLiteral(String::new()))),
        params: vec![("s".to_owned(), UnresolvedType::Primitive(Primitive::String), 0, 0)],
        varargs: false,
        var_count: 0,
        return_type: (UnresolvedType::Primitive(Primitive::String), 0, 0)
    }));
    module.definitions.insert("parse".to_owned(), Definition::Function(Function {
        body: Some(BlockOrExpr::Expr(Expression::IntLiteral(crate::lexer::tokens::IntLiteral { val: 0, ty: Some(crate::types::IntType::I32) } ))),
        params: vec![("s".to_owned(), UnresolvedType::Primitive(Primitive::String), 0, 0)],
        varargs: false,
        var_count: 0,
        return_type: (UnresolvedType::Primitive(Primitive::I32), 0, 0)
    }));
}