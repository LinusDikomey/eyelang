use std::{borrow::Borrow, collections::HashMap, fmt};
use crate::{lexer::tokens::{FloatLiteral, IntLiteral, Operator}, types::Primitive};

/// Represent ast nodes as the original code 
pub trait Repr<C: Representer> {
    fn repr(&self, c: &C);
}

/*enum ReprWriter<'a, W: std::fmt::Write> {
    Writer(&'a mut W),
    Parent(&'a mut ReprCtx<'a, W>)
}*/

pub trait Representer {
    fn child(&self) -> Self;
    fn begin_line(&self);
    fn write_start<B: Borrow<str>>(&self, s: B);
    fn write_add<B: Borrow<str>>(&self, s: B);
    fn space(&self) {
        self.write_add(" ");
    }
    fn writeln<B: Borrow<str>>(&self, s: B);
}

pub struct ReprPrinter<'a> {
    indent: &'a str,
    count: u32
}
impl<'a> ReprPrinter<'a> {
    pub fn new(indent: &'a str) -> Self {
        Self { indent, count: 0 }
    }
}
impl Representer for ReprPrinter<'_> {
    fn child(&self) -> Self {
        Self {
            indent: self.indent,
            count: self.count + 1
        }
    }

    fn begin_line(&self) {
        print!("{}", self.indent.repeat(self.count as usize));
    }

    fn write_start<B: Borrow<str>>(&self, s: B) {
        print!("{}{}", self.indent.repeat(self.count as usize), s.borrow());
    }

    fn write_add<B: Borrow<str>>(&self, s: B) {
        print!("{}", s.borrow())
    }

    fn writeln<B: Borrow<str>>(&self, s: B) {
        println!("{}{}", self.indent.repeat(self.count as usize), s.borrow());
    }
}

/*#[derive(Debug, Clone)]
pub enum UnresolvedTypeDefinition {
    Struct(StructDefinition)
}
*/

/*
pub struct Scope<'p> {
    parent: Option<&'p Scope<'p>>,
    functions: HashMap<String, Function>,
    types: HashMap<String, UnresolvedTypeDefinition>,
    variables: HashMap<String, UnresolvedType>,
    expected_return: UnresolvedType

}
*/

#[derive(Debug, Clone)]
pub struct Module {
    pub definitions: HashMap<String, Definition>
}

impl<C: Representer> Repr<C> for Module {
    fn repr(&self, c: &C) {
        for (name, def) in &self.definitions {
            def.repr(c, name);
            c.writeln("");
        }
    }
}

/*#[derive(PartialEq, Debug, Clone)]
pub enum ResolvedType {
    Primitive(Primitive),
    Struct(Vec<(String, ResolvedType)>)
}*/

/*pub struct GenericScope<'p, FuncT, StrT : Clone, VarT, RetT : Clone> {
    parent: Option<&'p GenericScope<'p, FuncT, StrT, VarT, RetT>>,
    functions: HashMap<String, FuncT>,
    types: HashMap<String, StrT>,
    variables: HashMap<String, (VarT, bool)>,
    expected_return: Option<RetT>,
    specified_parent_var_types: HashMap<String, VarT>,
    assigned_parent_vars: Vec<String>
}*/
/*impl<'p, FuncT, StrT : Clone, VarT, RetT : Clone> GenericScope<'p, FuncT, StrT, VarT, RetT> {

    pub fn new() -> Self {
        Self {
            parent: None,
            functions: HashMap::new(),
            types: HashMap::new(),
            variables: HashMap::new(),
            expected_return: None,
            specified_parent_var_types: HashMap::new(),
            assigned_parent_vars: Vec::new()
        }
    }

    pub fn create_inner(&'p self) -> Self {
        Self {
            parent: Some(self),
            functions: HashMap::new(),
            types: HashMap::new(),
            variables: HashMap::new(),
            expected_return: None,
            specified_parent_var_types: HashMap::new(),
            assigned_parent_vars: Vec::new()
        }
    }

    pub fn create_function(&'p self, return_type: RetT) -> Self {
        Self {
            parent: Some(self),
            functions: HashMap::new(),
            types: HashMap::new(),
            variables: HashMap::new(),
            expected_return: Some(return_type),
            specified_parent_var_types: HashMap::new(),
            assigned_parent_vars: Vec::new()
        }
    }


    pub fn resolve_function(&self, name: &str) -> Result<&FuncT, EyeError> {
        if let Some(func) = self.functions.get(name) {
            Ok(func)
        } else {
            if let Some(parent) = &self.parent {
                parent.resolve_function(name)
            } else {
                Err(EyeError::CompileError(CompileError::UnknownFunction(name.to_owned()), SourcePos::new(0, 0), SourcePos::new(0, 0)))
            }
        }
    }
    
    pub fn resolve_type(&self, name: &str) -> Result<StrT, EyeError> {
        if let Some(ty) = self.types.get(name) {
            Ok(ty.clone())
        } else {
            if let Some(parent) = &self.parent {
                parent.resolve_type(name)
            } else {
                Err(EyeError::CompileError(CompileError::UnknownType(name.to_owned()), SourcePos::new(0, 0), SourcePos::new(0, 0)))
            }
        }
    }

    pub fn resolve_variable(&self, name: &str) -> Result<&(VarT, bool), EyeError> {
        if let Some(var) = self.variables.get(name) {
            Ok(var)
        } else {
            if let Some(parent) = self.parent {
                parent.resolve_variable(name)
            } else {
                Err(EyeError::CompileErrorNoPos(CompileError::UnknownVariable(name.to_owned())))
            }
        }
    }

    pub fn specify_variable_type(&mut self, name: &str, ty: VarT) {
        if let Some((var_type, _assigned)) = self.variables.get_mut(name) {
            *var_type = ty;
        } else {
            self.specified_parent_var_types.insert(name.to_owned(), ty);
        }
    }

    pub fn mark_variable_assigned(&mut self, name: &str) {
        if let Some((_var_type, assigned)) = self.variables.get_mut(name) {
            *assigned = true;
        } else {
            self.assigned_parent_vars.push(name.to_owned());
        }
    }

    pub fn expected_return_type(&self) -> Option<RetT> {
        if let Some(ty) = &self.expected_return {
            Some(ty.clone())
        } else {
            if let Some(parent) = &self.parent {
                parent.expected_return_type()
            } else {
                None
            }
        }
    }

    pub fn register_variable(&mut self, name: String, ty: VarT, assigned: bool) {
        self.variables.insert(name, (ty, assigned));
    }
}
*/

//pub type Scope<'p> = GenericScope<'p, Function, Struct, VariableType, ResolvedType>;

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
impl Definition {
    fn repr<C: Representer>(&self, c: &C, name: &str) {
        match self {
            Self::Function(func) => func.repr(c, name),
            Self::Struct(struc) => struc.repr(c, name)
        }
    }
}

#[derive(Debug, Clone)]
pub struct StructDefinition {
    pub members: Vec<(String, UnresolvedType)>,
}
impl StructDefinition {
    fn repr<C: Representer>(&self, c: &C, name: &str) {
        c.writeln(format!("{} :: {{", name));
        let child = c.child();
        for (i, (name, ty)) in self.members.iter().enumerate() {
            child.begin_line();
            child.write_add(name.as_str());
            child.space();
            child.write_add(format!("{ty}"));
            child.write_add(if i == (self.members.len() - 1) { "\n" } else { ",\n" });
        }
        c.write_start("}");
    }
}

#[derive(Debug, Clone)]
pub struct Function {
    pub params: Vec<(String, UnresolvedType)>,
    pub vararg: Option<(String, UnresolvedType)>,
    pub return_type: UnresolvedType,
    pub body: BlockOrExpr,
}
impl Function {
    fn repr<C: Representer>(&self, c: &C, name: &str) {
        c.write_add(name);
        if self.params.len() > 0 {
            c.write_add("(");
            for (i, (name, param)) in self.params.iter().enumerate() {
                c.write_add(name.as_str());
                c.space();
                param.repr(c);
                if i != self.params.len() - 1 {
                    c.write_add(", ");
                }
            }
            c.write_add(")");
        }
        c.write_add(" -> ");
        c.write_add(format!("{}", self.return_type));
        if let BlockOrExpr::Expr(_) = &self.body {
            c.write_add(":");
        }
        c.space();
        self.body.repr(c);
        c.writeln("");
    }
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
impl<C: Representer> Repr<C> for Block {
    fn repr(&self, c: &C) {
        c.write_add("{\n");
        let child = c.child();
        for (name, def) in &self.defs {
            def.repr(&child, name);
        }
        for item in &self.items {
            item.repr(&child);
        }
        c.write_start("}");
    }
}

#[derive(Debug, Clone)]
pub enum BlockItem {
    Block(Block),
    Declare(String, Option<UnresolvedType>, Option<Expression>),
    Assign(LValue, Expression),
    Expression(Expression),
}
impl<C: Representer> Repr<C> for BlockItem {
    fn repr(&self, c: &C) {
        match self {
            Self::Block(block) => block.repr(c),
            Self::Declare(name, ty, expr) => {
                c.write_start(name.as_str());
                if let Some(ty) = ty {
                    c.write_add(": ");
                    c.write_add(format!("{ty}"));
                    if expr.is_some() {
                        c.space();
                    }
                } else {
                    debug_assert!(expr.is_some());
                    c.write_add(" :");
                }
                if let Some(expr) = expr {
                    c.write_add("= ");
                    expr.repr(c);
                }
            }
            Self::Assign(l_val, expr) => {
                c.begin_line();
                l_val.repr(c);
                c.write_add(" = ");
                expr.repr(c);
            }
            Self::Expression(expr) => {
                c.begin_line();
                expr.repr(c);
            }
        }
        c.write_add("\n");
    }
}

#[derive(Debug, Clone)]
pub enum Expression {
    Return(Box<Expression>),
    IntLiteral(IntLiteral),
    FloatLiteral(FloatLiteral),
    StringLiteral(String),
    BoolLiteral(bool),
    Variable(String),
    If(Box<If>),
    FunctionCall(Box<Expression>, Vec<Expression>),
    Negate(Box<Expression>),
    BinOp(Operator, Box<(Expression, Expression)>),
    MemberAccess(Box<Expression>, String),
    Cast(Primitive, Box<Expression>)
}
impl<C: Representer> Repr<C> for Expression {
    fn repr(&self, c: &C) {
        match self {
            Self::Return(val) => {
                c.write_add("ret");
                c.space();
                val.repr(c);
            }
            Self::IntLiteral(lit) => c.write_add(format!("{lit}")),
            Self::FloatLiteral(lit) => c.write_add(format!("{lit}")),
            Self::StringLiteral(s) => {
                c.write_add("\"");
                c.write_add(s.as_str().replace("\n", "\\n"));
                c.write_add("\"");
            }
            Self::BoolLiteral(b) => c.write_add(if *b { "true" } else { "false" }),
            Self::Variable(name) => c.write_add(name.as_str()),
            Self::If(box If { cond, then, else_ }) => {
                c.write_add("if ");
                cond.repr(c);
                if let BlockOrExpr::Block(_) = then {
                    c.space();
                } else {
                    c.write_add(": ");
                }
                then.repr(c);
                if let Some(else_block) = else_ {
                    c.write_add(" else ");
                    else_block.repr(c);
                }
            }
            Self::FunctionCall(func, args) => {
                func.repr(c);
                c.write_add("(");
                for (i, arg) in args.iter().enumerate() {
                    arg.repr(c);
                    if i != (args.len() - 1) {
                        c.write_add(", ");
                    }
                }
                c.write_add(")");
            }
            Self::Negate(expr) => {
                c.write_add("-");
                expr.repr(c);
            }
            Self::BinOp(op, exprs) => {
                c.write_add("(");
                let (l, r) = &**exprs;
                l.repr(c);
                c.space();
                op.repr(c);
                c.space();
                r.repr(c);
                c.write_add(")");
            }
            Self::MemberAccess(expr, member) => {
                expr.repr(c);
                c.write_add(".");
                c.write_add(member.as_str());
            }
            Self::Cast(ty, expr) => {
                ty.repr(c);
                c.space();
                expr.repr(c);
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct If {
    pub cond: Expression,
    pub then: BlockOrExpr,
    pub else_: Option<BlockOrExpr>
}

#[derive(Debug, Clone)]
pub enum LValue {
    Variable(String),
    Member(Box<LValue>, String)
}
impl<C: Representer> Repr<C> for LValue {
    fn repr(&self, c: &C) {
        match self {
            Self::Variable(var) => c.write_add(var.as_str()),
            Self::Member(l_val, member) => {
                l_val.repr(c);
                c.write_add(".");
                c.write_add(member.as_str());
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnresolvedType {
    Primitive(Primitive),
    Unresolved(String)
}
impl<R: Representer> Repr<R> for UnresolvedType {
    fn repr(&self, c: &R) {
        match self {
            Self::Primitive(p) => p.repr(c),
            Self::Unresolved(name) => c.write_add(name.as_str())
        }
    }
}
impl fmt::Display for UnresolvedType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnresolvedType::Primitive(p) => p.fmt(f),
            UnresolvedType::Unresolved(name) => write!(f, "{name}")
        }
    }
}