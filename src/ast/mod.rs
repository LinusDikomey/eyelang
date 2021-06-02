use std::{collections::HashMap, u128};

use crate::{error::{CompileError, EyeError}, lexer::tokens::{FloatLiteral, IntLiteral, SourcePos}, types::Primitive};


#[derive(Debug, Clone)]
pub struct Module {
    pub name: String,
    pub functions: HashMap<String, Function>,
    pub structs: HashMap<String, Struct>
}

impl Module {
    pub fn to_scope<'p>(self) -> Scope<'p> {
        Scope {
            parent: None,
            functions: self.functions,
            types: self.structs,
            variables: HashMap::new(),
            expected_return: None,
            specified_parent_var_types: HashMap::new(),
            assigned_parent_vars: Vec::new()
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum ResolvedType {
    Primitive(Primitive),
    Struct(Vec<(String, ResolvedType)>)
}

pub struct Scope<'p> {
    parent: Option<&'p Scope<'p>>,
    functions: HashMap<String, Function>,
    types: HashMap<String, Struct>,
    variables: HashMap<String, (VariableType, bool)>,
    expected_return: Option<ResolvedType>,
    specified_parent_var_types: HashMap<String, VariableType>,
    assigned_parent_vars: Vec<String>
}

/// used for variables because types might not yet be known
/// example:
/// x := 3      // UnknownType::Integer
/// y :i32 = x  // now the type is known
#[derive(Debug, Clone, PartialEq)]
pub enum VariableType {
    Known(ResolvedType),
    Any,
    Integer(u128, bool),
    Float(FloatLiteral),
}

impl VariableType {

    pub fn is_more_precise_than(&self, other: &Self) -> bool {
        use VariableType::*;
        match self {
            Known(_) => if let Known(_) = other {false} else {true},  // known is the most precise
            Any => false, // everything is more than or as precise as any
            Integer(val, signed) => {
                match other {
                    Any | Float(_) => true,
                    Known(_) => false,
                    Integer(other_val, other_signed) => {
                        if *signed {
                            if *other_signed {
                                other_val < val
                            } else {
                                true
                            }
                        } else {
                            if *other_signed {
                                false
                            } else {
                                other_val < val
                            }
                        }
                    },
                }
            },
            Float(_lit) => {
                match other {
                    Any | Integer(_, _) => true,
                    Known(_) => false,
                    Float(_other_lit) => false,    //TODO
                }
            }
        }
    }

}

impl<'p> Scope<'p> {

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

    pub fn create_function(&'p self, return_type: ResolvedType) -> Self {
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


    pub fn resolve_function(&self, name: &str) -> Result<&Function, EyeError> {
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

    pub fn resolve_type(&self, unresolved: &UnresolvedType) -> Result<ResolvedType, EyeError> {
        match unresolved {
            UnresolvedType::Primitive(primitive) => Ok(ResolvedType::Primitive(primitive.clone())),
            UnresolvedType::Unresolved(name) => {
                if let Some(ty) = self.types.get(name) {
                    let mut members = Vec::new();
                    for (name, member) in &ty.members {
                        members.push((name.clone(), self.resolve_type(member)?));
                    }
                    Ok(ResolvedType::Struct(members))
                } else {
                    if let Some(parent) = &self.parent {
                        parent.resolve_type(&unresolved)
                    } else {
                        Err(EyeError::CompileError(CompileError::UnknownType(name.clone()), SourcePos::new(0, 0), SourcePos::new(0, 0)))
                    }
                }
            }
        }
    }

    pub fn resolve_variable(&self, name: &str) -> Result<&(VariableType, bool), EyeError> {
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

    pub fn specify_variable_type(&mut self, name: &str, ty: VariableType) {
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

    pub fn expected_return_type(&self) -> Option<ResolvedType> {
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

    pub fn register_variable(&mut self, name: String, ty: VariableType, assigned: bool) {
        self.variables.insert(name, (ty, assigned));
    }
}

#[derive(Debug, Clone)]
pub struct Struct {
    pub members: Vec<(String, UnresolvedType)>,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub args: Vec<(String, UnresolvedType)>,
    pub return_type: UnresolvedType,
    pub body: Block
}

#[derive(Debug, Clone)]
pub struct Block {
    pub items: Vec<BlockItem>
}

#[derive(Debug, Clone)]
pub enum BlockItem {
    Block(Block),
    Declare(String, Option<UnresolvedType>, Option<Expression>),
    Assign(String, Expression),
    Expression(Expression)
}

#[derive(Debug, Clone)]
pub enum Expression {
    Return(Option<Box<Expression>>),
    IntLiteral(IntLiteral),
    FloatLiteral(FloatLiteral),
    StringLiteral(String),
    BoolLiteral(bool),
    Variable(String)
}

#[derive(Debug, Clone)]
pub enum UnresolvedType {
    Primitive(Primitive),
    Unresolved(String)
}