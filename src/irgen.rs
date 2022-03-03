use crate::{ast, error::{EyeResult, Error, Errors, CompileError}, ir::{SymbolType, SymbolKey}};
use std::collections::HashMap;
use crate::ir::*;

struct IrBuilder {
    ir: Vec<Instruction>
}
impl IrBuilder {
    pub fn new() -> Self {
        Self {
            ir: Vec::new(),
        }
    }

    pub fn add(&mut self, inst: Instruction) -> Ref {
        let idx = self.ir.len() as u32;
        self.ir.push(inst);
        Ref::index(idx)
    }
}

struct TypingCtx {
    funcs: Vec<Function>,
    types: Vec<Type>,
    symbols: HashMap<String, (SymbolType, SymbolKey)>,
}
impl TypingCtx {
    fn new() -> Self {
        Self {
            funcs: Vec::new(),
            types: Vec::new(),
            symbols: HashMap::new(),
            //function_headers: HashMap::new(),
            //functions: HashMap::new(),
            //types: HashMap::new(),
        }
    }

    /*
    fn insert_func(&mut self, key: SymbolKey, func: Function) -> Result<(), EyeError> {
        if self.functions.contains_key(&key) {
            return Err(EyeError::CompileErrorNoPos(
                CompileError::DuplicateDefinition,
            ));
        }
        self.functions.insert(key.clone(), func);
        Ok(())
    }*/

    fn resolve_type(&mut self, unresolved: &ast::UnresolvedType, ast: &ast::Module, errors: &mut Errors) -> Result<TypeRef, Error> {
        //TODO: check if this is recursing with some kind of stack and return recursive type def error.
        Ok(match unresolved {
            ast::UnresolvedType::Primitive(prim) => TypeRef::Primitive(*prim),
            ast::UnresolvedType::Unresolved(name) => {
                if let Some((symbol_ty, key)) = self.symbols.get(name) {
                    if let SymbolType::Type = symbol_ty {
                        TypeRef::Resolved(*key)
                    } else {
                        return Err(Error::TypeExpectedFoundFunction);
                    }
                } else {
                    if let Some(ast::Definition::Struct(def)) = ast.definitions.get(name) {
                        TypeRef::Resolved(self.define_type(name, def, ast, errors))
                    } else {
                        return Err(Error::UnknownType);
                    }
                }
            }
        })        
    }

    //fn resolve_func(&self, name: &str) -> 

    fn define_type(&mut self, name: &str, def: &ast::StructDefinition, ast: &ast::Module, errors: &mut Errors) -> SymbolKey {
        let members = def.members.iter().map(|(name, ty, start, end)| {
            (
                name.clone(), 
                match self.resolve_type(ty, ast, errors) {
                    Ok(ty) => ty,
                    Err(err) => {
                        errors.emit(err, *start, *end);
                        TypeRef::Invalid
                    }
                }
            )
        }).collect();
        let key = SymbolKey::new(self.types.len() as u64);
        self.types.push(Type::Struct(key, Struct { members }));
        let previous = self.symbols.insert(name.to_owned(), (SymbolType::Type, key));
        debug_assert!(previous.is_none(), "Duplicate type definnition inserted");
        key
    }

    fn define_func_header<'a>(&mut self, func: &ast::Function, ast: &ast::Module, errors: &mut Errors) -> EyeResult<FunctionHeader> {    
        let params = func
            .params
            .iter()
            .map(|(name, arg, start, end)| {
                let t = match self.resolve_type(arg, ast, errors) {
                    Ok(t) => t,
                    Err(err) => {
                        errors.emit(err, *start, *end);
                        TypeRef::Invalid
                    }
                };
                (name.clone(), t)
            })
            .collect();
        let vararg = if let Some((name, ty, start, end)) = &func.vararg {
            Some((name.clone(), self.resolve_type(ty, ast, errors).map_err(|err| CompileError { err, start: *start, end: *end })?))
        } else {
            None
        };
        let return_type = self.resolve_type(&func.return_type.0, ast, errors)
            .map_err(|err| CompileError { err, start: func.return_type.1, end: func.return_type.2 })?;
        Ok(FunctionHeader { params, return_type, vararg })
    }

    fn define_func(&mut self, name: &str, def: &ast::Function, header: FunctionHeader) -> EyeResult<SymbolKey> {
        let intrinsic = match name {
            "print" => Some(Intrinsic::Print),
            "read" => Some(Intrinsic::Read),
            "parse" => Some(Intrinsic::Parse),
            _ => None
        };
        let mut builder = IrBuilder::new();
        self.reduce_block_or_expr(&mut builder, &def.body);

        let key = SymbolKey::new(self.funcs.len() as u64);
        self.funcs.push(Function {
            header,
            ast: def.clone(),
            intrinsic,
            ir: builder.ir
        });
        let previous = self.symbols.insert(name.to_owned(), (SymbolType::Func, key));
        debug_assert!(previous.is_none(), "Duplicate func definition inserted");
        Ok(key)
    }

    fn reduce_block_or_expr(&mut self, ir: &mut IrBuilder, block_or_expr: &ast::BlockOrExpr) {
        match block_or_expr {
            ast::BlockOrExpr::Block(block) => self.reduce_block(ir, block),
            ast::BlockOrExpr::Expr(expr) => self.reduce_expr(ir, expr)
        }
    }

    fn reduce_block(&mut self, _ir: &mut IrBuilder, block: &ast::Block) {
        for _item in &block.items {
            
        }
    }

    fn reduce_expr(&mut self, _ir: &mut IrBuilder, _expr: &ast::Expression) {

    }
}

pub fn reduce(ast: &ast::Module, errors: &mut Errors) -> EyeResult<IrModule> {
    let mut ctx = TypingCtx::new();

    for (name, def) in &ast.definitions {
        if ctx.symbols.contains_key(name) { continue; }

        match def {
            ast::Definition::Struct(struc) => {
                ctx.define_type(name, struc, ast, errors);
            }
            ast::Definition::Function(func) => {
                let header = ctx.define_func_header(func, ast, errors)?;
                ctx.define_func(name, func, header)?;
            }
        }
    }
    Ok(IrModule { funcs: ctx.funcs, types: ctx.types, symbols: ctx.symbols })
}