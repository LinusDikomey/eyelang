use crate::{
    ast::{self, StructDefinition, BlockItem},
    error::{EyeResult, Error, Errors, CompileError},
    ir::{SymbolType, SymbolKey},
    types::Primitive, lexer::tokens::Operator
};
use std::{collections::HashMap, ptr::NonNull, num::NonZeroU32};
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

/// A type that may not be (completely) known yet. 
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum TypeInfo {
    Unknown,
    Int,
    Float,
    Func(SymbolKey),
    Type(SymbolKey),
    Primitive(Primitive),
    Resolved(SymbolKey),
    Invalid,
}
impl TypeInfo {
    fn as_type_ref(self) -> Option<TypeRef> {


        let mut v = Vec::new();
        v.push(3);
        v.push(4);

        match self {
            Self::Unknown => None,
            Self::Int => Some(TypeRef::Primitive(Primitive::I32)),
            Self::Float => Some(TypeRef::Primitive(Primitive::F32)),
            Self::Func(_) => Some(TypeRef::Primitive(Primitive::Func)),
            Self::Type(_) => Some(TypeRef::Primitive(Primitive::Type)),
            TypeInfo::Primitive(p) => Some(TypeRef::Primitive(p)),
            TypeInfo::Resolved(r) => Some(TypeRef::Resolved(r)),
            TypeInfo::Invalid => Some(TypeRef::Invalid),
        }
    }

    fn merge(&self, other: TypeInfo) -> Result<Self, Error> {
        self.merge_is_other(other, false)
    }

    fn merge_is_other(&self, other: TypeInfo, is_other: bool) -> Result<Self, Error> {
        let res = match self {
            Self::Unknown => Ok(other),
            Self::Int => {
                match other {
                    Self::Int => Ok(other),
                    Self::Primitive(p) if p.as_int().is_some() => Ok(other),
                    Self::Unknown => Ok(Self::Int),
                    _ => Err(Error::IntExpected)
                }
            }
            Self::Float => {
                match other {
                    Self::Float => Ok(other),
                    Self::Primitive(p) if p.as_float().is_some() => Ok(other),
                    Self::Unknown => Ok(Self::Float),
                    _ => Err(Error::FloatExpected)
                }
            }
            TypeInfo::Primitive(_) | TypeInfo::Resolved(_) | TypeInfo::Func(_) | TypeInfo::Type(_) => {
                (other == *self)
                    .then(|| *self)
                    .ok_or(Error::MismatchedType)
            }
            TypeInfo::Invalid => Ok(*self), // also invalid type 'spreading'
        };
        match res {
            Ok(t) => Ok(t),
            Err(err) => if is_other { println!("Merge failed {self:?} {other:?}"); Err(err) } else { other.merge_is_other(*self, true) }
        }
    }
}
impl From<TypeRef> for TypeInfo {
    fn from(ty: TypeRef) -> Self {
        match ty {
            TypeRef::Primitive(p) => Self::Primitive(p),
            TypeRef::Resolved(r) => Self::Resolved(r),
            TypeRef::Invalid => Self::Invalid,
        }
    }
}

#[derive(Clone, Copy)]
pub enum Symbol {
    Func(SymbolKey),
    Type(SymbolKey),
    Var { ty: TypeInfo, assigned: bool }
}

struct ScopeInfo<'a> {
    parent: Option<NonNull<ScopeInfo<'a>>>,
    symbols: HashMap<String, Symbol>,
    defs: Option<&'a HashMap<String, ast::Definition>>,
}
impl<'a> ScopeInfo<'a> {
    fn parent(&mut self) -> Option<&mut ScopeInfo<'a>> {
        self.parent.as_mut().map(|parent| unsafe { parent.as_mut() })
    }
}

enum FunctionOrHeader {
    Func(Function),
    Header(FunctionHeader)
}
impl FunctionOrHeader {
    fn header(&self) -> &FunctionHeader {
        match self {
            Self::Func(f) => f.header(),
            Self::Header(h) => h
        }
    }
}

struct TypingCtx {
    funcs: Vec<FunctionOrHeader>,
    types: Vec<Type>
}

fn resolve(
    info: &mut ScopeInfo,
    ctx: &mut TypingCtx,
    name: &str,
    errors: &mut Errors
) -> Result<TypeInfo, Error> {
    //TODO: check if this is recursing with some kind of stack and return recursive type def error.
    if let Some(symbol) = info.symbols.get(name) {
        match symbol {
            Symbol::Func(f) => Ok(TypeInfo::Func(*f)),
            Symbol::Type(t) => Ok(TypeInfo::Type(*t)),
            Symbol::Var { ty, assigned } => {
                if !assigned {
                    errors.emit(Error::UseOfUnassignedVariable, 0, 0);
                }
                Ok(*ty)
            }
        }
    } else {
        if let Some(def) = info.defs.map(|defs| defs.get(name)).flatten() {
            Ok(match def {
                ast::Definition::Function(func) => {
                    let header = define_func_header(info, ctx, func, errors).map_err(|err| err.err)?;
                    let key = SymbolKey::new(ctx.funcs.len() as u64);
                    ctx.funcs.push(FunctionOrHeader::Header(header));
                    let prev = info.symbols.insert(name.to_owned(), Symbol::Func(key));
                    debug_assert!(prev.is_none());
                    TypeInfo::Func(key)
                }
                ast::Definition::Struct(struct_) =>  {
                    TypeInfo::Type(define_type(info, ctx, name, struct_, errors))
                }
            })
        } else {
            info.parent.as_mut().map(|parent| {
                resolve(unsafe { parent.as_mut() }, ctx, name, errors)
            }).transpose()?.ok_or_else(|| { println!("UnknownIdent: {name}"); Error::UnknownIdent })
        }
    }
}

fn resolve_type(info: &mut ScopeInfo, ctx: &mut TypingCtx, unresolved: &ast::UnresolvedType, errors: &mut Errors) -> Result<TypeRef, Error> {
    match unresolved {
        ast::UnresolvedType::Primitive(p) => Ok(TypeRef::Primitive(*p)),
        ast::UnresolvedType::Unresolved(name) => {
            if let TypeInfo::Type(ty) = resolve(info, ctx, name, errors)? {
                Ok(TypeRef::Resolved(ty))
            } else {
                Err(Error::TypeExpected)
            }
        }
    }
}

fn define_type(info: &mut ScopeInfo, ctx: &mut TypingCtx, name: &str, def: &ast::StructDefinition, errors: &mut Errors) -> SymbolKey {
    let members = def.members.iter().map(|(name, ty, start, end)| {
        (
            name.clone(), 
            match resolve_type(info, ctx, ty, errors) {
                Ok(ty) => ty,
                Err(err) => {
                    errors.emit(err, *start, *end);
                    TypeRef::Invalid
                }
            }
        )
    }).collect();
    let key = SymbolKey::new(ctx.types.len() as u64);
    ctx.types.push(Type::Struct(Struct { members }));
    let previous = info.symbols.insert(name.to_owned(), Symbol::Type(key));
    debug_assert!(previous.is_none(), "Duplicate type definnition inserted");
    key
}

fn define_func_header<'a>(info: &mut ScopeInfo, ctx: &mut TypingCtx, func: &ast::Function, errors: &mut Errors) -> EyeResult<FunctionHeader> {    
    let params = func
        .params
        .iter()
        .map(|(name, arg, start, end)| {
            let t = match resolve_type(info, ctx, arg, errors) {
                Ok(t) => t,
                Err(err) => {
                    errors.emit(err, *start, *end);
                    TypeRef::Invalid
                }
            };
            (name.clone(), t)
        })
        .collect();
    let vararg = func.vararg.as_ref().map(|(name, ty, start, end)| {
        Ok((
            name.clone(),
            resolve_type(info, ctx, ty, errors)
                .map_err(|err| CompileError { err, start: *start, end: *end })?
        ))
    }).transpose()?;
    let return_type = resolve_type(info, ctx, &func.return_type.0, errors)
        .map_err(|err| CompileError { err, start: func.return_type.1, end: func.return_type.2 })?;
    Ok(FunctionHeader { params, return_type, vararg })
}


struct TypeTable {
    types: Vec<TypeInfo>,
    indices: Vec<Option<NonZeroU32>> // indices are offset by one for non zero optimizations with option
}
impl TypeTable {
    pub fn new(type_count: usize) -> Self {
        Self {
            types: Vec::new(),
            indices: Vec::with_capacity(type_count)
        }
    }

    pub fn constrain(&mut self, idx: usize, info: TypeInfo) -> Result<(), Error> {
        if let Some(type_idx) = self.indices[idx] {
            let ty = &mut self.types[type_idx.get() as usize - 1];
            *ty = ty.merge(info)?;
        } else {
            self.types.push(info);
            self.indices[idx] = Some(NonZeroU32::try_from(self.types.len() as u32).unwrap());
            // len being offset by one is correct here (the first entry is supposed to have index one for NonZero)
        }

        Ok(())
    }
}

struct Scope<'s> {
    ctx: &'s mut TypingCtx,
    info: ScopeInfo<'s>,
}

impl<'s> Scope<'s> {
    pub fn new(ctx: &'s mut TypingCtx, defs: Option<&'s HashMap<String, ast::Definition>>) -> Self {
        Self { ctx, info: ScopeInfo { parent: None, symbols: HashMap::new(), defs } }
    }
    pub fn child<'c>(&'c mut self, defs: Option<&'c HashMap<String, ast::Definition>>) -> Scope<'c> {
        Scope {
            ctx: &mut *self.ctx,
            info: ScopeInfo {
                parent: Some(NonNull::from(&mut self.info)),
                symbols: HashMap::new(),
                defs
            }
        }
    }

    fn resolve(&mut self, name: &str, errors: &mut Errors) -> Result<TypeInfo, Error> {
        resolve(&mut self.info, self.ctx, name, errors)
    }

    fn resolve_type(&mut self, unresolved: &ast::UnresolvedType, errors: &mut Errors) -> Result<TypeRef, Error> {
        resolve_type(&mut self.info, self.ctx, unresolved, errors)
    }

    fn define_type(&mut self, name: &str, def: &StructDefinition, errors: &mut Errors) -> SymbolKey {
        define_type(&mut self.info, self.ctx, name, def, errors)
    }

    fn define_func<'outer>(&'outer mut self, errors: &mut Errors, name: &str, def: &ast::Function, header: FunctionHeader) -> EyeResult<SymbolKey> {
        let intrinsic = match name {
            "print" => Some(Intrinsic::Print),
            "read" => Some(Intrinsic::Read),
            "parse" => Some(Intrinsic::Parse),
            _ => None
        };
        let mut builder = IrBuilder::new();
        let mut scope: Scope<'_> = self.child(None);
        for (name, ty) in &header.params {
            scope.declare_var(&mut builder, name.clone(), (*ty).into(), true);
        }
        let expected = header.return_type.into();
        scope.reduce_block_or_expr(errors, &mut builder, &def.body, expected, expected);

        let func = FunctionOrHeader::Func(Function {
            header,
            ast: def.clone(),
            intrinsic,
            ir: builder.ir
        });
        
        Ok(match self.info.symbols.get(name) {
            None => {
                let key = SymbolKey::new(self.ctx.funcs.len() as u64);
                self.ctx.funcs.push(func);
                self.info.symbols.insert(name.to_owned(), Symbol::Func(key));
                key
            }
            Some(Symbol::Func(key)) => {
                let existing_func = &mut self.ctx.funcs[key.idx()];
                match existing_func {
                    FunctionOrHeader::Func(_) => panic!("Function was already defined"),
                    FunctionOrHeader::Header(_) => *existing_func = func,
                }
                *key
            }
            Some(Symbol::Type(_) | Symbol::Var { .. }) => unreachable!()
        })
    }

    fn declare_var(&mut self, _ir: &mut IrBuilder, name: String, ty: TypeInfo, assigned: bool) {
        self.info.symbols.insert(name, Symbol::Var { ty, assigned });
    }

    fn assign(&mut self, errors: &mut Errors, ir: &mut IrBuilder, l_val: &ast::LValue, val: &ast::Expression, ret: TypeInfo) -> Result<(), Error> {
        let mut current = NonNull::from(&mut self.info);
        
        loop {
            let mut idents = l_val.idents().into_iter();
            if let Some(symbol) = unsafe { current.as_mut() }.symbols.get_mut(idents.next().unwrap()) {
                match symbol {
                    Symbol::Func(_) | Symbol::Type(_) => return Err(Error::ExpectedVarFoundDefinition),
                    Symbol::Var { ty, assigned } => {
                        let mut current_ty = *ty;
                        for ident in idents {
                            current_ty = match current_ty {
                                TypeInfo::Resolved(key) => {
                                    let Type::Struct(struct_) = &mut self.ctx.types[key.idx()];
                                    if let Some((_, member_ty)) = struct_.members.iter().find(|(name, _)| name == ident) {
                                        (*member_ty).into()
                                    } else {
                                        errors.emit(Error::NonexistantMember, 0, 0);
                                        TypeInfo::Invalid
                                    }
                                }
                                TypeInfo::Invalid => break,
                                _ => {
                                    errors.emit(Error::NonexistantMember, 0, 0);
                                    TypeInfo::Invalid
                                }
                            }
                        }
                        *assigned = true;
                        current_ty = current_ty.merge(self.reduce_expr(errors, ir, val, current_ty, ret))?;
                        break current_ty;
                    }
                }
            } else {
                if let Some(new) = unsafe { current.as_mut() }.parent() {
                    current = NonNull::from(new);
                } else {
                    return Err(Error::UnknownVariable)
                }
            }
        };

        Ok(())
    }

    fn reduce_block_or_expr(&mut self, errors: &mut Errors, ir: &mut IrBuilder, be: &ast::BlockOrExpr, expected: TypeInfo, ret: TypeInfo) -> TypeInfo {
        match be {
            ast::BlockOrExpr::Block(block) => {
                self.reduce_block(errors, ir, block, expected, ret);
                TypeInfo::Primitive(Primitive::Unit)
            }
            ast::BlockOrExpr::Expr(expr) => self.reduce_expr(errors, ir, expr, expected, ret)
        }
    }

    fn reduce_block(&mut self, errors: &mut Errors, ir: &mut IrBuilder, block: &ast::Block, _expected: TypeInfo, ret: TypeInfo) {
        let mut scope = self.child(Some(&block.defs));
        for item in &block.items {
            scope.reduce_stmt(errors, ir, item, ret);
        }
    }

    fn reduce_stmt(&mut self, errors: &mut Errors, ir: &mut IrBuilder, stmt: &BlockItem, ret: TypeInfo) {
        match stmt {
            BlockItem::Block(block) => self.reduce_block(errors, ir, block, TypeInfo::Primitive(Primitive::Unit), ret),
            BlockItem::Declare(name, _index, ty, val) => {
                let mut ty = match ty.as_ref().map(|ty| self.resolve_type(&ty, errors)).transpose() {
                    Ok(t) => t,
                    Err(err) => {
                        errors.emit(err, 0, 0);
                        return;
                    }
                }.map_or(TypeInfo::Unknown, Into::into);

                val.as_ref().map(|val| match self.reduce_expr(errors, ir, val, ty, ret).merge(ty) {
                    Ok(new_ty) => ty = new_ty,
                    Err(err) => errors.emit(err, 0, 0)
                });

                self.declare_var(ir, name.clone(), ty, val.is_some());
            }
            BlockItem::Assign(var, val) => {
                self.assign(errors, ir, var, val, ret)
                    .map_err(|err| errors.emit(err, var.start(), var.start()))
                    .ok();
            }
            BlockItem::Expression(expr) => { self.reduce_expr(errors, ir, expr, TypeInfo::Unknown, ret); }
        }
    }

    fn reduce_expr(&mut self, errors: &mut Errors, ir: &mut IrBuilder, expr: &ast::Expression, expected: TypeInfo, ret: TypeInfo) -> TypeInfo {
        match expr {
            ast::Expression::Return(ret_val) => self.reduce_expr(errors, ir, ret_val, ret, ret),
            ast::Expression::IntLiteral(lit) => lit.ty.map_or(TypeInfo::Int, |int_ty| TypeInfo::Primitive(int_ty.into())),
            ast::Expression::FloatLiteral(lit) => lit.ty.map_or(TypeInfo::Float, |float_ty| TypeInfo::Primitive(float_ty.into())),
            ast::Expression::StringLiteral(_) => TypeInfo::Primitive(Primitive::String),
            ast::Expression::BoolLiteral(_) => TypeInfo::Primitive(Primitive::Bool),
            ast::Expression::Variable(name) => match self.resolve(name, errors) {
                Ok(ty) => ty,
                Err(err) => {
                    errors.emit(err, 0, 0);
                    TypeInfo::Invalid
                }
            },
            ast::Expression::If(if_) => {
                let ast::If { cond, then, else_ } = &**if_;
                let b = TypeInfo::Primitive(Primitive::Bool);
                if let Err(err) = b.merge(self.reduce_expr(errors, ir, cond, b, ret)) {
                    errors.emit(err, 0, 0);
                }
                if let Some(else_) = else_ {
                    let then_ty = self.reduce_block_or_expr(errors, ir, then, expected, ret);
                    let else_expected = match expected.merge(then_ty) {
                        Ok(t) => t,
                        Err(err) => {
                            errors.emit(err, 0, 0);
                            then_ty
                        }
                    };
                    let else_ty = self.reduce_block_or_expr(errors, ir, else_, else_expected, ret);
                    match else_ty.merge(else_expected) {
                        Ok(t) => t,
                        Err(err) => {
                            // mismatched types in branches error?
                            errors.emit(err, 0, 0);
                            TypeInfo::Invalid
                        }
                    }
                } else {
                    self.reduce_block_or_expr(errors, ir, then, TypeInfo::Unknown, ret);
                    TypeInfo::Primitive(Primitive::Unit)
                }
            }
            ast::Expression::FunctionCall(func_expr, args) => {
                let func_ty = self.reduce_expr(errors, ir, func_expr, TypeInfo::Unknown, ret);
                match func_ty {
                    TypeInfo::Invalid => TypeInfo::Invalid,
                    TypeInfo::Func(key) => {
                        let header = self.ctx.funcs[key.idx()].header();
                        let return_type = header.return_type.into();
                        let invalid_arg_count = if let Some(_) = &header.vararg {
                            args.len() < header.params.len()
                        } else {
                            args.len() != header.params.len()
                        };
                        if invalid_arg_count {
                            errors.emit(Error::InvalidArgCount, 0, 0);
                        } else {
                            let params = header.params.iter().map(|(_, ty)| *ty);
                            let params = if let Some((_, vararg_ty)) = &header.vararg {
                                params.chain(std::iter::repeat(*vararg_ty)).take(args.len()).collect::<Vec<_>>()
                            } else {
                                params.collect::<Vec<_>>()
                            };
                            for (arg, ty) in args.iter().zip(params) {
                                self.reduce_expr(errors, ir, arg, ty.into(), ret);
                            }
                        }
                        return_type
                    }
                    TypeInfo::Type(ty) => { crate::log!("TODO: Struct init unchecked"); TypeInfo::Resolved(ty) } //TODO: check struct init params
                    _ => {
                        println!("Function expected, found: {func_ty:?}");
                        errors.emit(Error::FunctionExpected, 0, 0);
                        TypeInfo::Invalid
                    }
                }
            }
            ast::Expression::Negate(val) => {
                let ty = self.reduce_expr(errors, ir, val, expected, ret);
                let res = match ty {
                    TypeInfo::Float | TypeInfo::Int => ty.merge(expected),
                    TypeInfo::Primitive(p) => {
                        if let Some(int) = p.as_int() {
                            if !int.is_signed() {
                                Err(Error::CantNegateType)
                            } else {
                                ty.merge(expected)
                            }
                        } else if let Some(_) = p.as_float() {
                            ty.merge(expected)
                        } else {
                            Err(Error::CantNegateType)
                        }
                    }
                    _ => Err(Error::CantNegateType)
                };
                match res {
                    Ok(t) => t,
                    Err(err) => {
                        errors.emit(err, 0, 0);
                        TypeInfo::Invalid
                    }
                }
            }
            ast::Expression::BinOp(op, sides) => {
                let (l, r) = &**sides;
                // binary operations always require the same type on both sides right now
                let is_logical = matches!(op, 
                    Operator::Equals
                    | Operator::LT
                    | Operator::GT
                    | Operator::LE
                    | Operator::GE
                );
                if is_logical {
                    let l_ty = self.reduce_expr(errors, ir, l, TypeInfo::Unknown, ret);
                    let r_ty = self.reduce_expr(errors, ir, r, l_ty, ret);
                    match l_ty.merge(r_ty) {
                        Ok(_) => {}
                        Err(err) => errors.emit(err, 0, 0)
                    }
                    TypeInfo::Primitive(Primitive::Bool)
                } else {
                    let l_ty = match expected.merge(self.reduce_expr(errors, ir, l, expected, ret)) {
                        Ok(t) => t,
                        Err(err) => {
                            errors.emit(err, 0, 0);
                            TypeInfo::Invalid
                        }
                    };
                    match l_ty.merge(self.reduce_expr(errors, ir, r, l_ty, ret)) {
                        Ok(t) => t,
                        Err(err) => {
                            errors.emit(err, 0, 0);
                            TypeInfo::Invalid
                        }
                    }
                }
            }
            ast::Expression::MemberAccess(left, member) => {
                let left_ty = self.reduce_expr(errors, ir, left, TypeInfo::Unknown, ret);
                match left_ty {
                    TypeInfo::Resolved(key) => {
                        let Type::Struct(struct_) = &self.ctx.types[key.idx()];
                        if let Some((_, ty)) = struct_.members.iter().find(|(name, _)| name == member) {
                            (*ty).into()
                        } else {
                            println!("left_ty1: {left_ty:?}");
                            errors.emit(Error::NonexistantMember, 0, 0);
                            TypeInfo::Invalid
                        }
                    }
                    TypeInfo::Invalid => TypeInfo::Invalid,
                    _ => {
                        println!("left_ty2: {left_ty:?}");
                        errors.emit(Error::NonexistantMember, 0, 0);
                        TypeInfo::Invalid
                    }
                }
            }
            ast::Expression::Cast(target, val) => {
                let _ty = self.reduce_expr(errors, ir, val, TypeInfo::Unknown, ret);
                //TODO: check table for available casts
                TypeInfo::Primitive(*target)
            }
        }
    }
}

pub fn check(ast: &ast::Module, errors: &mut Errors) -> EyeResult<Module> {
    let mut ctx = TypingCtx { funcs: Vec::new(), types: Vec::new() };
    let mut scope = Scope::new(&mut ctx, Some(&ast.definitions));

    for (name, def) in &ast.definitions {

        match def {
            ast::Definition::Struct(struc) => {
                if scope.info.symbols.contains_key(name) { continue; }
                scope.define_type(name, struc, errors);
            }
            ast::Definition::Function(func) => {
                let header = match scope.info.symbols.get(name) {
                    Some(Symbol::Func(key)) => {
                        let func = &mut scope.ctx.funcs[key.idx()];
                        match func {
                            FunctionOrHeader::Func(_) => continue,
                            FunctionOrHeader::Header(header) => header.clone()
                        }
                    }
                    Some(Symbol::Type(_) | Symbol::Var { .. }) => unreachable!(),
                    None => define_func_header(&mut scope.info, scope.ctx, func, errors)?
                };
                scope.define_func(errors, name, func, header)?;
            }
        }
    }
    let symbols = scope.info.symbols.into_iter()
        .map(|(name, symbol)| (
            name,
            match symbol {
                Symbol::Func(f) => (SymbolType::Func, f),
                Symbol::Type(t) => (SymbolType::Type, t),
                Symbol::Var { .. } => unimplemented!("Top-level vars shouldn't exist")
            }
        ))
        .collect();
    let funcs = ctx.funcs.into_iter()
        .map(|f| match f {
            FunctionOrHeader::Func(func) => func,
            FunctionOrHeader::Header(_) => unreachable!()
        })
        .collect();
    Ok(Module { funcs, types: ctx.types, symbols })
}
