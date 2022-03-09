use crate::{
    ast::{self, StructDefinition, BlockItem, LValue},
    error::{EyeResult, Error, Errors, CompileError},
    ir::{SymbolType, SymbolKey},
    types::Primitive, lexer::tokens::Operator
};
use std::{collections::HashMap, ptr::NonNull, fmt};
use crate::ir::*;

#[derive(Clone, Copy)]
struct BlockIndex(u32);

struct IrBuilder {
    ir: Vec<Instruction>,
    current_block: Option<u32>,
    types: TypeTable,
    extra_data: Vec<u8>
}
impl IrBuilder {
    pub fn new() -> Self {
        Self {
            ir: Vec::new(),
            current_block: None,
            types: TypeTable::new(),
            extra_data: Vec::new()
        }
    }

    pub fn add(&mut self, data: Data, tag: Tag, ty: TypeTableIndex) -> Ref {
        let idx = self.ir.len() as u32;
        self.ir.push(Instruction { data, tag, ty, span: TokenSpan::new(0, 0) });
        Ref::index(idx)
    }

    pub fn extra_data_vals<'a>(&mut self, bytes: impl IntoIterator<Item = u8>) -> u32 {
        let idx = self.extra_data.len() as u32;
        self.extra_data.extend(bytes);
        idx
    }

    pub fn extra_data<'a>(&mut self, bytes: impl IntoIterator<Item = &'a u8>) -> u32 {
        let idx = self.extra_data.len() as u32;
        self.extra_data.extend(bytes);
        idx
    }

    pub fn extra_len(&mut self, bytes: &[u8]) -> (u32, u32) {
        (self.extra_data(bytes.into_iter()), bytes.len() as u32)
    }

    pub fn begin_block(&mut self, ty: TypeTableIndex) -> BlockIndex {
        let index = self.current_block.map_or(0, |x| x+1);
        let block = BlockIndex(index);
        self.current_block = Some(index);
        self.ir.push(Instruction { data: Data { int32: index }, tag: Tag::BlockBegin, ty, span: TokenSpan::new(0, 0)  });
        block
    }
}

/// A type that may not be (completely) known yet. 
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TypeInfo {
    Unknown,
    Int,
    Float,
    Func(SymbolKey),
    Type(SymbolKey),
    Primitive(Primitive),
    Resolved(SymbolKey),
    Invalid,
}
impl fmt::Display for TypeInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeInfo::Unknown => write!(f, "{{unknown}}"),
            TypeInfo::Int => write!(f, "{{int}}"),
            TypeInfo::Float => write!(f, "{{float}}"),
            TypeInfo::Func(key) => write!(f, "{{func {}}}", key.idx()),
            TypeInfo::Type(key) => write!(f, "{{type-type {}}}", key.idx()),
            TypeInfo::Primitive(p) => write!(f, "{p}"),
            TypeInfo::Resolved(key) => write!(f, "{{type {}}}", key.idx()),
            TypeInfo::Invalid => write!(f, "{{invalid}}"),
        }
    }
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
            Err(err) => if is_other {
                crate::log!("Merge failed {self:?} {other:?}");
                Err(err)
            } else {
                other.merge_is_other(*self, true)
            }
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
enum Symbol {
    Func(SymbolKey),
    Type(SymbolKey),
    Var { ty: TypeTableIndex, val: Ref }
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
    types: &mut TypeTable,
    name: &str,
    errors: &mut Errors
) -> Result<(TypeTableIndex, Option<Ref>), Error> {
    //TODO: check if this is recursing with some kind of stack and return recursive type def error.
    if let Some(symbol) = info.symbols.get(name) {
        match symbol {
            Symbol::Func(f) => Ok((types.add(TypeInfo::Func(*f)), None)),
            Symbol::Type(t) => Ok((types.add(TypeInfo::Type(*t)), None)),
            Symbol::Var { ty, val } => {
                if *val == Ref::val(RefVal::Undef) {
                    errors.emit(Error::UseOfUnassignedVariable, 0, 0);
                }
                Ok((*ty, Some(*val)))
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
                    (types.add(TypeInfo::Func(key)), None)
                }
                ast::Definition::Struct(struct_) =>  {
                    let defined = define_type(info, ctx, Some(types), name, struct_, errors);
                    (types.add(TypeInfo::Type(defined)), None)
                }
            })
        } else {
            info.parent.as_mut().map(|parent| {
                resolve(unsafe { parent.as_mut() }, ctx, types, name, errors)
            }).transpose()?.ok_or_else(|| { println!("UnknownIdent: {name}"); Error::UnknownIdent })
        }
    }
}

fn resolve_noinfer(
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
            Symbol::Var { .. } => {
                unreachable!("noinfer should only be used in a context without vars")
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
                    TypeInfo::Type(define_type(info, ctx, None, name, struct_, errors))
                }
            })
        } else {
            info.parent.as_mut().map(|parent| {
                resolve_noinfer(unsafe { parent.as_mut() }, ctx, name, errors)
            }).transpose()?.ok_or_else(|| { println!("UnknownIdent: {name}"); Error::UnknownIdent })
        }
    }
}

fn resolve_type(info: &mut ScopeInfo, ctx: &mut TypingCtx, types: &mut TypeTable, unresolved: &ast::UnresolvedType, errors: &mut Errors) -> Result<TypeRef, Error> {
    match unresolved {
        ast::UnresolvedType::Primitive(p) => Ok(TypeRef::Primitive(*p)),
        ast::UnresolvedType::Unresolved(name) => {
            let resolved = resolve(info, ctx, types, name, errors)?.0;
            if let TypeInfo::Type(ty) = types.get_type(resolved).0 {
                Ok(TypeRef::Resolved(ty))
            } else {
                Err(Error::TypeExpected)
            }
        }
    }
}

fn resolve_type_noinfer(info: &mut ScopeInfo, ctx: &mut TypingCtx, unresolved: &ast::UnresolvedType, errors: &mut Errors) -> Result<TypeRef, Error> {
    match unresolved {
        ast::UnresolvedType::Primitive(p) => Ok(TypeRef::Primitive(*p)),
        ast::UnresolvedType::Unresolved(name) => {
            if let TypeInfo::Type(ty) = resolve_noinfer(info, ctx, name, errors)? {
                Ok(TypeRef::Resolved(ty))
            } else {
                Err(Error::TypeExpected)
            }
        }
    }
}

fn define_type(info: &mut ScopeInfo, ctx: &mut TypingCtx, mut types: Option<&mut TypeTable>, name: &str, def: &ast::StructDefinition, errors: &mut Errors) -> SymbolKey {
    let members = def.members.iter().map(|(name, ty, start, end)| {
        let resolved = if let Some(types) = &mut types {
            resolve_type(info, ctx, types, ty, errors)
        } else {
            resolve_type_noinfer(info, ctx, ty, errors)
        };
        (
            name.clone(),
            match resolved {
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
            let t = match resolve_type_noinfer(info, ctx, arg, errors) {
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
            resolve_type_noinfer(info, ctx, ty, errors)
                .map_err(|err| CompileError { err, start: *start, end: *end })?
        ))
    }).transpose()?;
    let return_type = resolve_type_noinfer(info, ctx, &func.return_type.0, errors)
        .map_err(|err| CompileError { err, start: func.return_type.1, end: func.return_type.2 })?;
    Ok(FunctionHeader { params, return_type, vararg })
}

#[derive(Clone, Copy, Debug)]
pub struct TypeIdx(u32);
impl TypeIdx {
    fn new(idx: usize) -> Self {
        Self(idx as u32)
    }
    fn get(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Debug)]
pub struct TypeTable {
    types: Vec<TypeInfo>,
    indices: Vec<TypeIdx>
}
impl TypeTable {
    pub fn new() -> Self {
        Self {
            types: Vec::new(),
            indices: Vec::new()
        }
    }

    pub fn get_type(&self, idx: TypeTableIndex) -> (TypeInfo, TypeIdx) {
        let type_idx = self.indices[idx.idx()];
        (self.types[type_idx.get()], type_idx)
    }

    pub fn add(&mut self, info: TypeInfo) -> TypeTableIndex {
        let type_idx = TypeIdx::new(self.types.len());
        self.types.push(info);
        let table_idx = TypeTableIndex::new(self.indices.len() as u32);
        self.indices.push(type_idx);
        table_idx
    }

    pub fn specify(&mut self, idx: TypeTableIndex, info: TypeInfo, errors: &mut Errors) {
        let idx = idx.idx();
        let type_idx = self.indices[idx];
        let ty = &mut self.types[type_idx.get()];
        *ty = match ty.merge(info) {
            Ok(ty) => ty,
            Err(err) => {
                errors.emit(err, 0, 0);
                TypeInfo::Invalid
            }
        };
    }

    pub fn merge(&mut self, a: TypeTableIndex, b: TypeTableIndex, errors: &mut Errors) {
        let a_idx = self.indices[a.idx()];
        let b_idx = &mut self.indices[b.idx()];
        let prev_b_ty = self.types[b_idx.get()];
        *b_idx = a_idx; // make b point to a's type

        let a_ty = &mut self.types[a_idx.get()];
        // merge b's previous type into a
        *a_ty = match a_ty.merge(prev_b_ty) {
            Ok(ty) => ty,
            Err(err) => {
                errors.emit(err, 0, 0);
                TypeInfo::Invalid
            }
        }
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

    fn resolve(&mut self, types: &mut TypeTable, name: &str, errors: &mut Errors) -> Result<(TypeTableIndex, Option<Ref>), Error> {
        resolve(&mut self.info, self.ctx, types, name, errors)
    }

    fn resolve_type(&mut self, types: &mut TypeTable, unresolved: &ast::UnresolvedType, errors: &mut Errors) -> Result<TypeRef, Error> {
        resolve_type(&mut self.info, self.ctx, types, unresolved, errors)
    }

    fn define_type(&mut self, types: Option<&mut TypeTable>, name: &str, def: &StructDefinition, errors: &mut Errors) -> SymbolKey {
        define_type(&mut self.info, self.ctx, types, name, def, errors)
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
            let ty = builder.types.add((*ty).into());
            let param = builder.add(Data { none: () }, Tag::Param, ty);
            scope.declare_var(&mut builder, name.clone(), ty, param);
        }
        let expected = builder.types.add(header.return_type.into());
        scope.reduce_block_or_expr(errors, &mut builder, &def.body, expected, expected);

        let func = FunctionOrHeader::Func(Function {
            header,
            ast: def.clone(),
            intrinsic,
            ir: builder.ir,
            extra: builder.extra_data,
            types: builder.types
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

    fn declare_var(&mut self, _ir: &mut IrBuilder, name: String, ty: TypeTableIndex, val: Ref) {
        self.info.symbols.insert(name, Symbol::Var { ty, val });
    }

    fn assign(&mut self, errors: &mut Errors, ir: &mut IrBuilder, l_val: &ast::LValue, assign_val: &ast::Expression, ret: TypeTableIndex) -> Result<(), Error> {
        let mut current = NonNull::from(&mut self.info);
        
        loop {
            let mut idents = l_val.idents().into_iter();
            if let Some(symbol) = unsafe { current.as_mut() }.symbols.get_mut(idents.next().unwrap()) {
                match symbol {
                    Symbol::Func(_) | Symbol::Type(_) => return Err(Error::ExpectedVarFoundDefinition),
                    Symbol::Var { ty, val } => {
                        
                        let expected = match l_val {
                            LValue::Variable(_, _) => *ty,
                            LValue::Member(_, _) => {
                                let mut current_ty = ir.types.get_type(*ty).0;
                                for ident in l_val.idents().into_iter() {
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
                                ir.types.add(current_ty)
                            }
                        };
                        *val = self.reduce_expr(errors, ir, assign_val, expected, ret);
                        return Ok(())
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
    }

    fn reduce_block_or_expr(&mut self, errors: &mut Errors, ir: &mut IrBuilder, be: &ast::BlockOrExpr, expected: TypeTableIndex, ret: TypeTableIndex) -> BlockIndex {
        match be {
            ast::BlockOrExpr::Block(block) => self.reduce_block(errors, ir, block, expected, ret),
            ast::BlockOrExpr::Expr(expr) => {
                let block_index = ir.begin_block(expected);
                self.reduce_expr(errors, ir, expr, expected, ret);
                block_index
            }
        }
    }

    fn reduce_block(&mut self, errors: &mut Errors, ir: &mut IrBuilder, block: &ast::Block, expected: TypeTableIndex, ret: TypeTableIndex) -> BlockIndex {
        let block_index = ir.begin_block(expected);
        let mut scope = self.child(Some(&block.defs));
        //ir.types.specify(expected, TypeInfo::Primitive(Primitive::Unit), errors);
        for item in &block.items {
            scope.reduce_stmt(errors, ir, item, ret);
        }
        block_index
    }

    fn reduce_stmt(&mut self, errors: &mut Errors, ir: &mut IrBuilder, stmt: &BlockItem, ret: TypeTableIndex) {
        match stmt {
            BlockItem::Block(block) => {
                let block_ty = ir.types.add(TypeInfo::Unknown);
                self.reduce_block(errors, ir, block, block_ty, ret);
            }
            BlockItem::Declare(name, _index, ty, val) => {
                let ty = match ty.as_ref().map(|ty| self.resolve_type(&mut ir.types, &ty, errors)).transpose() {
                    Ok(t) => t,
                    Err(err) => {
                        errors.emit(err, 0, 0);
                        return;
                    }
                }.map_or(TypeInfo::Unknown, Into::into);
                let ty = ir.types.add(ty);

                let val_ref = val.as_ref().map_or(
                    Ref::val(RefVal::Undef),
                    |val| self.reduce_expr(errors, ir, val, ty, ret)
                );

                self.declare_var(ir, name.clone(), ty, val_ref);
                ir.add(Data { un_op: val_ref }, Tag::Declare, ty);
            }
            BlockItem::Assign(var, val) => {
                self.assign(errors, ir, var, val, ret)
                    .map_err(|err| errors.emit(err, var.start(), var.start()))
                    .ok();
            }
            BlockItem::Expression(expr) => {
                let expr_ty = ir.types.add(TypeInfo::Unknown);
                self.reduce_expr(errors, ir, expr, expr_ty, ret);
            }
        }
    }

    fn reduce_expr(&mut self, errors: &mut Errors, ir: &mut IrBuilder, expr: &ast::Expression, expected: TypeTableIndex, ret: TypeTableIndex) -> Ref {
        match expr {
            ast::Expression::Return(ret_val) => {
                let r = self.reduce_expr(errors, ir, ret_val, ret, ret);
                ir.types.specify(expected, TypeInfo::Primitive(Primitive::Never), errors);
                ir.add(Data { un_op: r }, Tag::Ret, expected)
            }
            ast::Expression::IntLiteral(lit) => {
                let int_ty = lit.ty.map_or(TypeInfo::Int, |int_ty| TypeInfo::Primitive(int_ty.into()));
                ir.types.specify(expected, int_ty, errors);
                if lit.val == 0 {
                    Ref::val(RefVal::Zero)
                } else if lit.val == 1 {
                    Ref::val(RefVal::One)
                } else if lit.val <= std::u64::MAX as u128 {
                    ir.add(Data { int: lit.val as u64 }, Tag::Int, expected)
                } else {
                    let extra = ir.extra_data(&lit.val.to_le_bytes());
                    ir.add(Data { extra }, Tag::LargeInt, expected)
                }
            }
            ast::Expression::FloatLiteral(lit) => {
                let float_ty = lit.ty.map_or(TypeInfo::Float, |float_ty| TypeInfo::Primitive(float_ty.into()));
                ir.types.specify(expected, float_ty, errors);
                ir.add(Data { float: lit.val }, Tag::Float, expected)
            }
            ast::Expression::StringLiteral(string) => {
                ir.types.specify(expected, TypeInfo::Primitive(Primitive::String), errors);
                let extra_len = ir.extra_len(string.as_bytes());
                ir.add(Data { extra_len }, Tag::String, expected)
            }
            ast::Expression::BoolLiteral(b) => {
                ir.types.specify(expected, TypeInfo::Primitive(Primitive::Bool), errors);
                Ref::val(if *b { RefVal::True } else { RefVal::False })
            }
            ast::Expression::Unit => {
                ir.types.specify(expected, TypeInfo::Primitive(Primitive::Unit), errors);
                Ref::val(RefVal::Unit)
            }
            ast::Expression::Variable(name) => match self.resolve(&mut ir.types, name, errors) {
                Ok((ty, val)) => {
                    // specify in both direction
                    ir.types.merge(ty, expected, errors);
                    val.unwrap_or(Ref::val(RefVal::Undef))
                }
                Err(err) => {
                    errors.emit(err, 0, 0);
                    Ref::val(RefVal::Undef)
                }
            },
            ast::Expression::If(if_) => {
                let ast::If { cond, then, else_ } = &**if_;
                let b = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
                self.reduce_expr(errors, ir, cond, b, ret)
                //todo!();
                /*if let Some(else_) = else_ {
                    let then_block = self.reduce_block_or_expr(errors, ir, then, expected, ret);
                    let else_block = self.reduce_block_or_expr(errors, ir, else_, expected, ret);
                    let after = ir.begin_block(ir.types.add(TypeInfo::Primitive(Primitive::Unit)));
                    
                } else {
                    self.reduce_block_or_expr(errors, ir, then, TypeInfo::Unknown, ret);
                    TypeInfo::Primitive(Primitive::Unit)
                }*/
            }
            ast::Expression::FunctionCall(func_expr, args) => {
                let func_ty = ir.types.add(TypeInfo::Unknown);
                self.reduce_expr(errors, ir, func_expr, func_ty, ret);
                match ir.types.get_type(func_ty).0 {
                    TypeInfo::Invalid => ir.add(Data { none: () }, Tag::Invalid, func_ty),
                    TypeInfo::Func(key) => {
                        let header = self.ctx.funcs[key.idx()].header();
                        ir.types.specify(expected, header.return_type.into(), errors);
                        let invalid_arg_count = if let Some(_) = &header.vararg {
                            args.len() < header.params.len()
                        } else {
                            args.len() != header.params.len()
                        };
                        if invalid_arg_count {
                            errors.emit(Error::InvalidArgCount, 0, 0);
                            ir.add(Data { none: () }, Tag::Invalid, expected)
                        } else {
                            let params = header.params.iter().map(|(_, ty)| *ty);
                            let params = if let Some((_, vararg_ty)) = &header.vararg {
                                params.chain(std::iter::repeat(*vararg_ty)).take(args.len()).collect::<Vec<_>>()
                            } else {
                                params.collect::<Vec<_>>()
                            };
                            let bytes = args.iter().zip(params).map(|(arg, ty)| {
                                let ty = ir.types.add(ty.into());
                                self.reduce_expr(errors, ir, arg, ty, ret).to_bytes()
                            }).flatten().collect::<Vec<_>>();
                            let extra = ir.extra_data_vals(bytes);
                            ir.add(Data { extra_len: (extra, args.len() as u32) }, Tag::Call, expected)
                        }
                    }
                    TypeInfo::Type(ty) => todo!(), //{ crate::log!("TODO: Struct init unchecked"); TypeInfo::Resolved(ty) } //TODO: check struct init params
                    _ => {
                        println!("Function expected, found: {func_ty:?}");
                        errors.emit(Error::FunctionExpected, 0, 0);
                        ir.types.specify(expected, TypeInfo::Invalid, errors);
                        ir.add(Data { none: () }, Tag::Invalid, expected)
                    }
                }
            }
            ast::Expression::Negate(val) => {
                let inner = self.reduce_expr(errors, ir, val, expected, ret);
                let is_ok = match ir.types.get_type(expected).0 {
                    TypeInfo::Float | TypeInfo::Int | TypeInfo::Unknown => Ok(()),
                    TypeInfo::Primitive(p) => {
                        if let Some(int) = p.as_int() {
                            if !int.is_signed() {
                                Err(Error::CantNegateType)
                            } else {
                                Ok(())
                            }
                        } else if let Some(_) = p.as_float() {
                            Ok(())
                        } else {
                            Err(Error::CantNegateType)
                        }
                    }
                    _ => Err(Error::CantNegateType)
                };
                if let Err(err) = is_ok {
                    errors.emit(err, 0, 0);
                }
                ir.add(Data { un_op: inner }, Tag::Neg, expected)
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

                let inner_ty = if is_logical { ir.types.add(TypeInfo::Unknown) } else { expected };
                let l = self.reduce_expr(errors, ir, l, inner_ty, ret);
                let r = self.reduce_expr(errors, ir, r, inner_ty, ret);
                let tag = match op {
                    Operator::Add => Tag::Add,
                    Operator::Sub => Tag::Sub,
                    Operator::Mul => Tag::Mul,
                    Operator::Div => Tag::Div,

                    Operator::Equals => Tag::Eq,
                    Operator::LT => Tag::LT,
                    Operator::GT => Tag::GT,
                    Operator::LE => Tag::LE,
                    Operator::GE => Tag::GE,
                };
                ir.add(Data { bin_op: (l, r) }, tag, inner_ty)
            }
            ast::Expression::MemberAccess(left, member) => {
                let left_ty = ir.types.add(TypeInfo::Unknown);
                let left = self.reduce_expr(errors, ir, left, left_ty, ret);
                let (ty, idx) = match ir.types.get_type(left_ty).0 {
                    TypeInfo::Resolved(key) => {
                        let Type::Struct(struct_) = &self.ctx.types[key.idx()];
                        if let Some((i, (_, ty))) = struct_.members.iter().enumerate().find(|(_, (name, _))| name == member) {
                            ((*ty).into(), i)
                        } else {
                            println!("left_ty1: {left_ty:?}");
                            errors.emit(Error::NonexistantMember, 0, 0);
                            (TypeInfo::Invalid, 0)
                        }
                    }
                    TypeInfo::Invalid => (TypeInfo::Invalid, 0),
                    _ => {
                        println!("left_ty2: {left_ty:?}");
                        errors.emit(Error::NonexistantMember, 0, 0);
                        (TypeInfo::Invalid, 0)
                    }
                };
                ir.types.specify(expected, ty, errors);
                ir.add(Data { member: (left, idx as u32) }, Tag::Member, expected)
            }
            ast::Expression::Cast(target, val) => {
                ir.types.specify(expected, TypeInfo::Primitive(*target), errors);
                let inner_ty = ir.types.add(TypeInfo::Unknown);
                let val = self.reduce_expr(errors, ir, val, inner_ty, ret);
                //TODO: check table for available casts
                ir.add(Data { cast: (val, *target) }, Tag::Cast, expected)
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
                scope.define_type(None, name, struc, errors);
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
