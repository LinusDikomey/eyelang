use std::{borrow::Borrow, collections::HashMap};
use crate::{lexer::tokens::{FloatLiteral, IntLiteral, Operator}, types::Primitive};
use crate::log;

/// used to represent ast nodes as the original code 
pub trait Repr {
    fn repr(&self, c: &ReprCtx);
}

/*enum ReprWriter<'a, W: std::fmt::Write> {
    Writer(&'a mut W),
    Parent(&'a mut ReprCtx<'a, W>)
}*/

pub struct ReprCtx<'a> {
    indent: &'a str,
    count: u32
}
impl<'a> ReprCtx<'a> {
    pub fn new(indent: &'a str) -> Self {
        Self { indent, count: 0 }
    }
    pub fn child(&self) -> ReprCtx<'_> {
        Self {
            indent: self.indent,
            count: self.count + 1
        }
    }
    pub fn write<S: Borrow<str>>(&self, str: S) {
        print!("{}{}", self.indent.repeat(self.count as usize), str.borrow());
    }
    pub fn writeln<S: Borrow<str>>(&self, str: S) {
        log!("{}{}", self.indent.repeat(self.count as usize), str.borrow());
    }
}

#[derive(Debug, Clone)]
pub enum UnresolvedTypeDefinition {
    Struct(StructDefinition)
}

pub struct Scope<'p> {
    parent: Option<&'p Scope<'p>>,
    functions: HashMap<String, Function>,
    types: HashMap<String, UnresolvedTypeDefinition>,
    variables: HashMap<String, UnresolvedType>,
    expected_return: UnresolvedType

}

#[derive(Debug, Clone)]
pub struct Module {
    pub functions: HashMap<String, Function>,
    pub types: HashMap<String, UnresolvedTypeDefinition>
}

impl Module {
    pub fn to_scope<'p>(self) -> Scope<'p> {
        Scope {
            parent: None,
            functions: self.functions,
            types: self.types,
            variables: HashMap::new(),
            expected_return: UnresolvedType::Primitive(Primitive::Void),
        }
    }
}
impl Repr for Module {
    fn repr(&self, c: &ReprCtx) {
        for (name, ty) in &self.types {
            match ty {
                UnresolvedTypeDefinition::Struct(s) => {
                    c.writeln(format!("struct {} {{", name));
                    let struct_c = c.child();
                    for (name, ty) in &s.members {
                        struct_c.writeln(format!("{} {},", name, ty.display()))
                    }
                    c.writeln("}");
                }
            }
        }
        for (name, func) in &self.functions {
            c.writeln(format!("{} :: {} {{", name, func.return_type.display()));
            let body_c = c.child();
            body_c.writeln("TODO: function body");
            c.writeln("}");
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
    Definition(Definition),
    Block(BlockItem)
}

#[derive(Debug, Clone)]
pub enum Definition {
    Function(String, Function),
    Struct(String, StructDefinition),
}

#[derive(Debug, Clone)]
pub struct StructDefinition {
    pub members: Vec<(String, UnresolvedType)>,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub params: Vec<(String, UnresolvedType)>,
    pub return_type: UnresolvedType,
    pub body: Block
}

#[derive(Debug, Clone)]
pub struct Block {
    pub items: Vec<BlockItem>,
    pub defs: Vec<Definition>
}

#[derive(Debug, Clone)]
pub enum BlockItem {
    Block(Block),
    Declare(String, Option<UnresolvedType>, Option<Expression>),
    Assign(LValue, Expression),
    Expression(Expression)
}

#[derive(Debug, Clone)]
pub enum Expression {
    Return(Option<Box<Expression>>),
    IntLiteral(IntLiteral),
    FloatLiteral(FloatLiteral),
    StringLiteral(String),
    BoolLiteral(bool),
    Variable(String),
    If(Box<Expression>, Block, Option<Block>),
    FunctionCall(Box<Expression>, Vec<Expression>),
    BinOp(Operator, Box<(Expression, Expression)>),
    MemberAccess(Box<Expression>, String)
}

#[derive(Debug, Clone)]
pub enum LValue {
    Variable(String),
    Member(Box<LValue>, String)
}

#[derive(Debug, Clone)]
pub enum UnresolvedType {
    Primitive(Primitive),
    Unresolved(String)
}

impl UnresolvedType {
    pub fn display(&self) -> &str {
        match self {
            UnresolvedType::Primitive(p) => p.display(),
            UnresolvedType::Unresolved(name) => &name
        }
    }
}