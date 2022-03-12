use crate::{
    ast::{self, StructDefinition, BlockItem, LValue},
    error::{Error, Errors, CompileError},
    types::Primitive, lexer::tokens::Operator
};
use std::{collections::HashMap, ptr::NonNull};
use super::{*, typing::*};

#[derive(Clone, Copy)]
struct BlockIndex(u32);
impl BlockIndex {
    fn bytes(&self) -> [u8; 4] {
        self.0.to_le_bytes()
    }
}

struct IrBuilder {
    ir: Vec<Instruction>,
    current_block: u32,
    next_block: u32,
    types: TypeTable,
    extra_data: Vec<u8>
}
impl IrBuilder {
    pub fn new() -> Self {
        Self {
            ir: vec![Instruction {
                data: Data { int32: 0 },
                tag: Tag::BlockBegin,
                span: TokenSpan::new(0, 0),
                ty: TypeTableIndex::NONE
            }],
            current_block: 0,
            next_block: 1,
            types: TypeTable::new(),
            extra_data: Vec::new()
        }
    }

    pub fn add(&mut self, data: Data, tag: Tag, ty: TypeTableIndex) -> Ref {
        let idx = self.ir.len() as u32;
        self.ir.push(Instruction { data, tag, ty, span: TokenSpan::new(0, 0) });
        Ref::index(idx)
    }

    pub fn extra_data<'a>(&mut self, bytes: &[u8]) -> u32 {
        let idx = self.extra_data.len() as u32;
        self.extra_data.extend(bytes);
        idx
    }

    pub fn extra_len(&mut self, bytes: &[u8]) -> (u32, u32) {
        (self.extra_data(bytes), bytes.len() as u32)
    }

    pub fn create_block(&mut self) -> BlockIndex {
        let idx = BlockIndex(self.next_block);
        self.next_block += 1;
        idx
    }

    pub fn begin_block(&mut self, idx: BlockIndex) {
        debug_assert!(
            matches!(self.ir[self.ir.len() - 1].tag, Tag::Branch | Tag::Goto | Tag::Ret),
            "Can't begin next block without exiting previous one (Branch/Goto/Ret)"
        );

        self.current_block = idx.0;
        self.ir.push(Instruction {
            data: Data { int32: idx.0 },
            tag: Tag::BlockBegin,
            ty: TypeTableIndex::NONE,
            span: TokenSpan::new(0, 0)  }
        );
    }

    pub fn _create_and_begin_block(&mut self) -> BlockIndex {
        let block = self.create_block();
        self.begin_block(block);
        block
    }
}

#[derive(Clone, Copy)]
enum Symbol {
    Func(SymbolKey),
    Type(SymbolKey),
    Var { ty: TypeTableIndex, var: Ref }
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
            Symbol::Var { ty, var } => {
                Ok((*ty, Some(*var)))
            }
        }
    } else {
        if let Some(def) = info.defs.map(|defs| defs.get(name)).flatten() {
            Ok(match def {
                ast::Definition::Function(func) => {
                    let header = define_func_header(info, ctx, name.to_owned(), func, errors);
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
                    let header = define_func_header(info, ctx, name.to_owned(), func, errors);
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

fn define_func_header<'a>(info: &mut ScopeInfo, ctx: &mut TypingCtx, name: String, func: &ast::Function, errors: &mut Errors) -> FunctionHeader {    
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
    }).transpose();
    let vararg = errors.emit_unwrap(vararg, None);

    let return_type = resolve_type_noinfer(info, ctx, &func.return_type.0, errors)
        .map_err(|err| CompileError { err, start: func.return_type.1, end: func.return_type.2 });
    let return_type = errors.emit_unwrap(return_type, TypeRef::Invalid);
    FunctionHeader { params, return_type, vararg, name }
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

    fn define_func<'outer>(&'outer mut self, errors: &mut Errors, name: &str, def: &ast::Function, header: FunctionHeader) -> SymbolKey {
        let intrinsic = match name {
            "print" => Some(Intrinsic::Print),
            "read" => Some(Intrinsic::Read),
            "parse" => Some(Intrinsic::Parse),
            _ => None
        };
        let mut builder = IrBuilder::new();
        let mut scope: Scope<'_> = self.child(None);
        for (i, (name, ty)) in header.params.iter().enumerate() {
            let ty = builder.types.add((*ty).into());
            let param = builder.add(Data { int32: i as u32 }, Tag::Param, ty);
            scope.info.symbols.insert(name.clone(), Symbol::Var { ty, var: param });
        }
        let expected = builder.types.add(header.return_type.into());
        let val = scope.reduce_block_or_expr(errors, &mut builder, &def.body, expected, expected);
        builder.add(Data { un_op: val }, Tag::Ret, expected);

        let func = FunctionOrHeader::Func(Function {
            header,
            ast: def.clone(),
            intrinsic,
            ir: builder.ir,
            extra: builder.extra_data,
            types: builder.types,
            block_count: builder.next_block
        });
        
        match self.info.symbols.get(name) {
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
        }
    }

    fn declare_var(&mut self, ir: &mut IrBuilder, name: String, ty: TypeTableIndex) -> Ref {
        let var = ir.add(Data { ty }, Tag::Decl, ty);
        self.info.symbols.insert(name, Symbol::Var { ty, var });
        var
    }

    fn assign(&mut self, errors: &mut Errors, ir: &mut IrBuilder, l_val: &ast::LValue, assign_val: &ast::Expression, ret: TypeTableIndex) -> Result<(), Error> {
        let mut current = NonNull::from(&mut self.info);
        
        loop {
            let mut idents = l_val.idents().into_iter();
            if let Some(symbol) = unsafe { current.as_mut() }.symbols.get_mut(idents.next().unwrap()) {
                match symbol {
                    Symbol::Func(_) | Symbol::Type(_) => return Err(Error::ExpectedVarFoundDefinition),
                    Symbol::Var { ty, var } => {
                        let mut current_var = *var;
                        let expected = match l_val {
                            LValue::Variable(_, _) => *ty,
                            LValue::Member(_, _) => {
                                let mut current_ty = ir.types.get_type(*ty).0;
                                for ident in idents {
                                    (current_ty, current_var) = match current_ty {
                                        TypeInfo::Resolved(key) => {
                                            let Type::Struct(struct_) = &mut self.ctx.types[key.idx()];
                                            if let Some((i, (_, member_ty))) = struct_.members.iter().enumerate().find(|(_, (name, _))| name == ident) {
                                                
                                                ((*member_ty).into(), ir.add(Data { member: (current_var, i as u32) }, Tag::Member, *ty))
                                            } else {
                                                errors.emit(Error::NonexistantMember, 0, 0);
                                                (TypeInfo::Invalid, Ref::val(RefVal::Undef))
                                            }
                                        }
                                        TypeInfo::Invalid => break,
                                        TypeInfo::Unknown => {
                                            errors.emit(Error::TypeMustBeKnownHere, 0, 0);
                                            (TypeInfo::Invalid, Ref::val(RefVal::Undef))
                                        }
                                        _ => {
                                            errors.emit(Error::NonexistantMember, 0, 0);
                                            (TypeInfo::Invalid, Ref::val(RefVal::Undef))
                                        }
                                    }
                                }
                                ir.types.add(current_ty)
                            }
                        };
                        let expr_val = self.reduce_expr(errors, ir, assign_val, expected, ret);
                        ir.add(Data { bin_op: (current_var, expr_val) }, Tag::Store, expected);
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

    fn reduce_block_or_expr(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        be: &ast::BlockOrExpr,
        expected: TypeTableIndex,
        ret: TypeTableIndex
    ) -> Ref {
        match be {
            ast::BlockOrExpr::Block(block) => {
                self.reduce_block(errors, ir, block, expected, ret);
                Ref::val(RefVal::Unit)
            }
            ast::BlockOrExpr::Expr(expr) => self.reduce_expr(errors, ir, expr, expected, ret)
        }
    }

    fn reduce_block(&mut self, errors: &mut Errors, ir: &mut IrBuilder, block: &ast::Block, _expected: TypeTableIndex, ret: TypeTableIndex) {
        let mut scope = self.child(Some(&block.defs));
        //ir.types.specify(expected, TypeInfo::Primitive(Primitive::Unit), errors);
        for item in &block.items {
            scope.reduce_stmt(errors, ir, item, ret);
        }
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

                let var = self.declare_var(ir, name.clone(), ty);

                if let Some(val) = val {
                    self.reduce_expr_store_into_var(errors, ir, val, var, ty, ret);
                }
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
    
    // there are multiple 'expr' functions here so that 'Decl' instructions aren't duplicated.
    // Otherwise the lhs and rhs of a declaration or assignment might both declare a variable.

    fn reduce_expr(&mut self, errors: &mut Errors, ir: &mut IrBuilder, expr: &ast::Expression, expected: TypeTableIndex, ret: TypeTableIndex) -> Ref {
        self.reduce_expr_any(errors, ir, expr, expected, ret,
            |ir| ir.add(Data { ty: expected }, Tag::Decl, expected), // declare new var
            |_, r| r,
            |r| r
        )
    }
    fn reduce_expr_store_into_var(&mut self, errors: &mut Errors, ir: &mut IrBuilder, expr: &ast::Expression, var: Ref, expected: TypeTableIndex, ret: TypeTableIndex) {
        self.reduce_expr_any(errors, ir, expr, expected, ret,
            |_| var,
            |ir, r| { ir.add(Data { bin_op: (var, r) }, Tag::Store, expected); }, // store non-variable value
            |_| () // value is already stored
        );
    }

    fn reduce_expr_any<T>(
        &mut self,
        errors: &mut Errors,
        ir: &mut IrBuilder,
        expr: &ast::Expression,
        expected: TypeTableIndex,
        ret: TypeTableIndex,
        get_var: impl Fn(&mut IrBuilder) -> Ref,
        default: impl Fn(&mut IrBuilder, Ref) -> T,
        stored_val: impl Fn(Ref) -> T,
    ) -> T {
        let r = match expr {
            ast::Expression::Return(ret_val) => {
                let r = self.reduce_expr(errors, ir, ret_val, ret, ret);
                ir.types.specify(expected, TypeInfo::Primitive(Primitive::Never), errors);
                ir.add(Data { un_op: r }, Tag::Ret, expected)
            }
            ast::Expression::IntLiteral(lit) => {
                let int_ty = lit.ty.map_or(TypeInfo::Int, |int_ty| TypeInfo::Primitive(int_ty.into()));
                ir.types.specify(expected, int_ty, errors);
                if lit.val <= std::u64::MAX as u128 {
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
                Ok((ty, var)) => {
                    ir.types.merge(ty, expected, errors);
                    var.map(|var| ir.add(Data { un_op: var }, Tag::Load, ty)).unwrap_or(Ref::val(RefVal::Undef))
                }
                Err(err) => {
                    errors.emit(err, 0, 0);
                    Ref::val(RefVal::Undef)
                }
            },
            ast::Expression::If(if_) => {
                let ast::If { cond, then, else_ } = &**if_;
                let b = ir.types.add(TypeInfo::Primitive(Primitive::Bool));
                let cond = self.reduce_expr(errors, ir, cond, b, ret);
                let then_block = ir.create_block();
                let other_block = ir.create_block();

                let branch_extra = ir.extra_data(&then_block.0.to_le_bytes());
                ir.extra_data(&other_block.0.to_le_bytes());

                let never_ty = ir.types.add(TypeInfo::Primitive(Primitive::Never));
                ir.add(Data { branch: (cond, branch_extra) }, Tag::Branch, never_ty);
                ir.begin_block(then_block);
                
                let val = if let Some(else_) = else_ {
                    let after_block = ir.create_block();
                    let then_val = self.reduce_block_or_expr(errors, ir, then, expected, ret);
                    ir.add(Data { int32: after_block.0 }, Tag::Goto, never_ty);
                    ir.begin_block(other_block);
                    let else_val = self.reduce_block_or_expr(errors, ir, else_, expected, ret);
                    ir.add(Data { int32: after_block.0 }, Tag::Goto, never_ty);
                    ir.begin_block(after_block);

                    let extra = ir.extra_data(&then_block.bytes());
                    ir.extra_data(&then_val.to_bytes());
                    ir.extra_data(&other_block.bytes());
                    ir.extra_data(&else_val.to_bytes());
                    ir.add(Data { extra_len: (extra, 2) }, Tag::Phi, expected)
                } else {
                    ir.types.specify(expected, TypeInfo::Primitive(Primitive::Unit), errors);
                    let then_ty = ir.types.add(TypeInfo::Unknown);
                    self.reduce_block_or_expr(errors, ir, then, then_ty, ret);
                    ir.add(Data { int32: other_block.0 }, Tag::Goto, never_ty);
                    ir.begin_block(other_block);

                    Ref::val(RefVal::Unit)
                };
                val
            }
            ast::Expression::FunctionCall(func_expr, args) => {
                let func_ty = ir.types.add(TypeInfo::Unknown);
                dbg!(self.reduce_expr(errors, ir, func_expr, func_ty, ret));
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
                            Ref::val(RefVal::Undef)
                        } else {
                            let params = header.params.iter().map(|(_, ty)| *ty);
                            let params = if let Some((_, vararg_ty)) = &header.vararg {
                                params.chain(std::iter::repeat(*vararg_ty)).take(args.len()).collect::<Vec<_>>()
                            } else {
                                params.collect::<Vec<_>>()
                            };
                            let mut bytes = Vec::with_capacity(8 + 4 * args.len());
                            bytes.extend(&key.bytes());
                            for (arg, ty) in args.iter().zip(params) {
                                let ty = ir.types.add(ty.into());
                                let expr = self.reduce_expr(errors, ir, arg, ty, ret);
                                bytes.extend(&expr.to_bytes());
                            }
                            let extra = ir.extra_data(&bytes);
                            ir.add(Data { extra_len: (extra, args.len() as u32) }, Tag::Call, expected)
                        }
                    }
                    TypeInfo::Type(ty) => {
                        let Type::Struct(struct_) = &self.ctx.types[ty.idx()];
                        ir.types.specify(expected, TypeInfo::Resolved(ty), errors);

                        if args.len() != struct_.members.len() {
                            errors.emit(Error::InvalidArgCount, 0, 0);
                            Ref::val(RefVal::Undef)
                        } else {
                            let val = get_var(ir);
                            let member_types: Vec<TypeInfo> = struct_.members.iter()
                            .map(|(_, ty)| (*ty).into())
                            .collect();
                            for (i, (member_val, member_ty)) in args.iter().zip(member_types).enumerate() {
                                let member_ty = ir.types.add(member_ty);
                                let member_val = self.reduce_expr(errors, ir, member_val, member_ty, ret);
                                let member = ir.add(Data { member: (val, i as u32) }, Tag::Member, member_ty);
                                ir.add(Data { bin_op: (member, member_val) }, Tag::Store, member_ty);
                            }
                            return stored_val(val);
                        }
                    }
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
                let is_logical = matches!(op, 
                    Operator::Equals
                    | Operator::LT
                    | Operator::GT
                    | Operator::LE
                    | Operator::GE
                );

                // binary operations always require the same type on both sides right now
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
                            errors.emit(Error::NonexistantMember, 0, 0);
                            (TypeInfo::Invalid, 0)
                        }
                    }
                    TypeInfo::Invalid => (TypeInfo::Invalid, 0),
                    TypeInfo::Unknown => {
                        errors.emit(Error::TypeMustBeKnownHere, 0, 0);
                        (TypeInfo::Invalid, 0)
                    }
                    _ => {
                        errors.emit(Error::NonexistantMember, 0, 0);
                        (TypeInfo::Invalid, 0)
                    }
                };
                ir.types.specify(expected, ty, errors);
                ir.add(Data { member: (left, idx as u32) }, Tag::Member, expected) //TODO: probably load here
            }
            ast::Expression::Cast(target, val) => {
                ir.types.specify(expected, TypeInfo::Primitive(*target), errors);
                let inner_ty = ir.types.add(TypeInfo::Unknown);
                let val = self.reduce_expr(errors, ir, val, inner_ty, ret);
                //TODO: check table for available casts
                ir.add(Data { cast: (val, *target) }, Tag::Cast, expected)
            }
        };
        default(ir, r)
    }
}

pub fn reduce(ast: &ast::Module, errors: &mut Errors) -> Module {
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
                    None => define_func_header(&mut scope.info, scope.ctx, name.clone(), func, errors)
                };
                scope.define_func(errors, name, func, header);
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
    Module { name: "MainModule".to_owned(), funcs, types: ctx.types, symbols }
}
