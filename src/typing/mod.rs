use crate::{ast, error::{CompileError, EyeError, EyeResult}};
use std::collections::HashMap;

pub mod tir;
use tir::*;

struct TypingCtx<'a> {
    ast: &'a ast::Module,
    pub function_headers: HashMap<SymbolKey, FunctionHeader>,
    pub functions: HashMap<SymbolKey, Function>,
    pub types: HashMap<SymbolKey, Type>,
}
impl<'a> TypingCtx<'a> {
    fn new(ast: &'a ast::Module) -> Self {
        Self {
            ast,
            function_headers: HashMap::new(),
            functions: HashMap::new(),
            types: HashMap::new(),
        }
    }

    fn insert_func(&mut self, key: SymbolKey, func: Function) -> Result<(), EyeError> {
        if self.functions.contains_key(&key) {
            return Err(EyeError::CompileErrorNoPos(
                CompileError::DuplicateDefinition,
            ));
        }
        self.functions.insert(key.clone(), func);
        Ok(())
    }

    fn insert_type(&mut self, key: SymbolKey, t: Type) -> Result<(), EyeError> {
        if let Some(_existing) = self.types.insert(key.clone(), t) {
            return Err(EyeError::CompileErrorNoPos(
                CompileError::DuplicateDefinition,
            ));
        }
        Ok(())
    }

    fn resolve_type(&mut self, unresolved: &ast::UnresolvedType) -> Result<TypeRef, EyeError> {
        Ok(match unresolved {
            ast::UnresolvedType::Primitive(prim) => TypeRef::Primitive(*prim),
            ast::UnresolvedType::Unresolved(name) => {
                let key = SymbolKey::new(name.clone());
                if !self.types.contains_key(&key) {
                    if let Some(ast::Definition::Struct(t)) = self.ast.definitions.get(key.name()) {
                        let t = self.reduce_type(t)?;
                        self.types.insert(key.clone(), t);
                        TypeRef::Resolved(key)
                    } else {
                        return Err(EyeError::CompileErrorNoPos(CompileError::UnknownType(
                            key.display().to_owned(),
                        )));
                    }
                } else {
                    TypeRef::Resolved(key)
                }
            }
        })        
    }

    fn resolve_func_header(&mut self, key: &SymbolKey) -> EyeResult<&FunctionHeader> {
        if self.functions.contains_key(key) {
            Ok(self.functions[key].header())
        } else {
            if self.function_headers.contains_key(key) {
                Ok(&self.function_headers[key])
            } else {
                if let Some(ast::Definition::Function(func)) = self.ast.definitions.get(key.name()) {
                    let params = func
                        .params
                        .iter()
                        .map(|(name, arg)| {
                            let t = self.resolve_type(arg)?;
                            Ok((name.clone(), t))
                        })
                        .collect::<EyeResult<Vec<_>>>()?;
                        let vararg = if let Some((name, ty)) = &func.vararg {
                            Some((name.clone(), self.resolve_type(ty)?))
                        } else {
                            None
                        };
                    let return_type = self.resolve_type(&func.return_type)?;
                    let header = FunctionHeader { params, return_type, vararg };
                    self.function_headers.insert(key.clone(), header);
                    Ok(&self.function_headers[key])
                } else {
                    Err(EyeError::CompileErrorNoPos(CompileError::UnknownFunction(
                        key.display().to_owned(),
                    )))
                }
            }
        }
    }

    fn reduce_type(&mut self, def: &ast::StructDefinition) -> EyeResult<Type> {
        let members = def.members.iter().map(|(name, ty)| {
            Ok((
                name.clone(), 
                self.resolve_type(ty)?
            ))
        }).collect::<Result<Vec<_>, _>>()?;
        Ok(Type::Struct(Struct { members }))
    }

    fn reduce_func(&mut self, def: &ast::Function, header: FunctionHeader, name: &str) -> EyeResult<Function> {
        let intrinsic = match name {
            "print" => Some(Intrinsic::Print),
            "read" => Some(Intrinsic::Read),
            "parse" => Some(Intrinsic::Parse),
            _ => None
        };
        Ok(Function { header, ast: def.clone(), intrinsic })
    }
}

pub fn reduce(ast: &ast::Module) -> EyeResult<Module> {
    let mut ctx = TypingCtx::new(ast);
    for (name, def) in &ctx.ast.definitions {
        let key = SymbolKey::new(name.clone());
        match def {
            ast::Definition::Struct(struc) => {
                if ctx.types.contains_key(&key) { continue; }
                let t = ctx.reduce_type(struc)?;
                ctx.insert_type(key, t)?;
            }
            ast::Definition::Function(func) => {
                if ctx.functions.contains_key(&key) {
                    continue;
                }
                // first the existence of the header is ensured, then ownership of the header is taken out of the map
                ctx.resolve_func_header(&key)?;
                let header = ctx.function_headers.remove(&key).unwrap();
        
                let func = ctx.reduce_func(func, header, name)?;
                ctx.insert_func(SymbolKey::new(name.clone()), func)?;
            }
        }
    }
    assert_eq!(ctx.function_headers.len(), 0);
    Ok(Module {
        functions: ctx.functions,
        types: ctx.types,
    })
}
