use std::collections::HashMap;
use crate::{ast, error::{CompileError, EyeError, EyeResult}};

mod tir;

use tir::*;

struct TypingCtx<'a> {
    ast: &'a ast::Module,
    function_headers: HashMap<SymbolKey, FunctionHeader>,
    functions: HashMap<SymbolKey, Function>,
    types: HashMap<SymbolKey, Type>
}
impl<'a> TypingCtx<'a> {
    fn new(ast: &'a ast::Module) -> Self {
        Self {
            ast,
            function_headers: HashMap::new(),
            functions: HashMap::new(),
            types: HashMap::new()
        }
    }

    fn insert_func(&mut self, key: SymbolKey, func: Function) -> Result<(), EyeError> {
        if self.functions.contains_key(&key) {
            return Err(EyeError::CompileErrorNoPos(CompileError::DuplicateFunctionDefinition));   
        }
        self.functions.insert(key.clone(), func);
        Ok(())
    }

    fn insert_type(&mut self, key: SymbolKey, t: Type) -> Result<(), EyeError> {
        if self.types.contains_key(&key) {
            return Err(EyeError::CompileErrorNoPos(CompileError::DuplicateTypeDefinition));   
        }
        self.types.insert(key.clone(), t);
        Ok(())
    }

    fn resolve_type(&mut self, key: &SymbolKey) -> Result<&Type, EyeError> {
        if !self.types.contains_key(key) {
            if let Some(t) = self.ast.types.get(key.name()) {
                let t = t.clone();
                let t = self.reduce_type(&t)?;
                self.types.insert(key.clone(), t);
            } else {
                return Err(EyeError::CompileErrorNoPos(CompileError::UnknownType(key.display().to_owned())))
            }
        }
        return Ok(&self.types[key])
    }

    fn resolve_func_header(&mut self, key: &SymbolKey) -> EyeResult<&FunctionHeader> {
        if self.functions.contains_key(key) {
            Ok(self.functions[key].header())
        } else {
            if self.function_headers.contains_key(key) {
                Ok(&self.function_headers[key])
            } else {
                if let Some(func) = self.ast.functions.get(key.name()) {
                    let args = func.args.iter().map(
                        |(name, arg)| {
                            let t = match arg {
                                ast::UnresolvedType::Primitive(prim) => TypeRef::Primitive(*prim),
                                ast::UnresolvedType::Unresolved(unresolved) => {
                                    let key = SymbolKey::new(unresolved.clone());
                                    self.resolve_type(&key)?;
                                    TypeRef::Resolved(key)
                                }
                            };
                            Ok((name.clone(), t))
                        }

                    ).collect::<EyeResult<Vec<_>>>()?;
                    let header = FunctionHeader { args };
                    self.function_headers.insert(key.clone(), header);
                    Ok(&self.function_headers[key])
                } else {
                    Err(EyeError::CompileErrorNoPos(CompileError::UnknownFunction(key.display().to_owned())))
                }
            }
        }
    }

    fn reduce_type(&mut self, def: &ast::UnresolvedTypeDefinition) -> EyeResult<Type> {
        Ok(Type::Struct(Struct { }))
    }

    fn reduce_func(&mut self, def: &ast::Function, header: FunctionHeader) -> EyeResult<Function> {
        Ok(Function { header })
    }
}

pub fn reduce(ast: &ast::Module) -> EyeResult<Module> {
    let mut ctx = TypingCtx::new(ast);
    for (name, t) in &ctx.ast.types {
        let key = SymbolKey::new(name.clone());
        if ctx.types.contains_key(&key) {
            continue
        }
        let t = ctx.reduce_type(t)?;
        ctx.insert_type(key, t)?;
    }
    for (name, func) in &ctx.ast.functions {
        let key = SymbolKey::new(name.clone());
        if ctx.functions.contains_key(&key) {
            continue
        }
        // first the existance of the header is ensured, then ownership of the header is taken out of the map
        ctx.resolve_func_header(&key)?;
        let header = ctx.function_headers.remove(&key).unwrap();
        
        let func = ctx.reduce_func(func, header)?;
        ctx.insert_func(SymbolKey::new(name.clone()), func)?;
    }
    assert_eq!(ctx.function_headers.len(), 0);
    Ok(Module {
        functions: ctx.functions,
        types: ctx.types
    })
}