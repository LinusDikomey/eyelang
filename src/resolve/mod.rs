use crate::{ast::{self, ModuleId, Definition, ExprRef, Ast}, error::{Errors, Error}, dmap, span::{Span, TSpan}};

use self::{types::{DefId, Type, SymbolTable, FunctionHeader, Struct, TypeDef, TupleCountMode, FunctionId}, type_info::{TypeTableIndex, TypeTable, TypeInfo, TypeTableIndices}};

pub mod const_val;
pub mod types;
pub mod type_info;
mod expr;
mod pat;
mod exhaust;

#[derive(Clone, Copy)]
struct ModuleCtx {
    src: *const str,
    id: ModuleId,
    root: ModuleId,
}
impl ModuleCtx {
    fn src(&self) -> &str {
        unsafe { &*self.src }
    }
}

struct Scope<'a> {
    module_scopes: *const [Scope<'static>],
    module: ModuleCtx,
    parent: Option<&'a Scope<'a>>,
    names: dmap::DHashMap<String, DefId>,
}
impl Scope<'static> {
    fn root(names: dmap::DHashMap<String, DefId>, module_ctx: ModuleCtx) -> Self {
        Self {
            module_scopes: &[],
            module: module_ctx,
            parent: None,
            names,
        }
    }
    fn set_module_scopes_ptr(&mut self, module_scopes: *const [Scope<'static>]) {
        self.module_scopes = module_scopes;
    }

    fn child<'a>(&'a self) -> LocalScope<'a> {
        LocalScope {
            parent: LocalOrGlobalScope::Global(self),
            scope: Scope {
                module_scopes: self.module_scopes,
                module: self.module,
                parent: Some(self),
                names: dmap::new()
            },
            locals: dmap::new(),
        }
    }
}
impl<'a> Scope<'a> {
    fn module_scope(&'a self, id: ModuleId) -> &'a Scope<'static> {
        unsafe { &(*self.module_scopes)[id.idx()] }
    }

    fn define(&mut self, name: String, def_id: DefId) -> Option<DefId> {
        self.names.insert(name, def_id)
    }

    fn resolve(&self, name: &str, name_span: TSpan, errors: &mut Errors) -> Option<DefId> {
        // PERF: make non-recursive
        if let Some(id) = self.names.get(name) {
            Some(*id)
        } else {
            if let Some(parent) = self.parent {
                return parent.resolve(name, name_span, errors);
            } else {
                errors.emit_span(Error::UnknownIdent, name_span.in_mod(self.module.id));
                None
            }
        }
    }

    fn resolve_path(&self, path: &ast::IdentPath, errors: &mut Errors) -> Option<DefId> {
        let (root, middle, last) = path.segments(self.module.src());
        let mut current_module = if root.is_some() { Some(self.module.root) } else { None };

        for (segment, segment_span) in middle {
            let scope = if let Some(module) = current_module {
                self.module_scope(module)
            } else {
                self
            };
            match scope.resolve(segment, segment_span, errors)? {
                DefId::Module(id) => current_module = Some(id),
                _ => {
                    errors.emit_span(Error::ModuleExpected, segment_span.in_mod(self.module.id));
                    return None;
                }
            }

        }

        if let Some((segment, span)) = last {
            if let Some(module) = current_module {
                self.module_scope(module)
            } else {
                self
            }.resolve(segment, span, errors)
        } else {
            // should be fine to unwrap here since empty paths don't exist
            Some(DefId::Module(current_module.unwrap()))
        }
    }

    fn resolve_ty(&self, ty: &ast::UnresolvedType, symbols: &SymbolTable, errors: &mut Errors) -> Type {
        match ty {
            ast::UnresolvedType::Primitive(p, _) => Type::Prim(*p),
            ast::UnresolvedType::Unresolved(path, generics) => {
                let Some(id) = self.resolve_path(path, errors) else { return Type::Invalid };
                match id {                    
                    DefId::Type(id) => {
                        let generic_count = symbols.generic_count(id);
                        let generics = if let Some((generics, generics_span)) = generics {
                            if generics.len() as u8 != generic_count {
                                errors.emit_span(
                                    Error::InvalidGenericCount {
                                        expected: generic_count,
                                        found: generics.len() as u8
                                    },
                                    generics_span.in_mod(self.module.id)
                                );
                                return Type::Invalid;
                            }
                            generics
                                .iter()
                                .map(|ty| self.resolve_ty(ty, symbols, errors))
                                .collect()
                        } else {
                            if generic_count != 0 {
                                errors.emit_span(
                                    Error::InvalidGenericCount { expected: generic_count, found: 0 },
                                    path.span().in_mod(self.module.id)
                                );
                                return Type::Invalid;
                            }
                            vec![]
                        };
                        Type::Id(id, generics)
                    }
                    DefId::Function(_) | DefId::Module(_) => {
                        errors.emit_span(Error::TypeExpected, path.span().in_mod(self.module.id));
                        Type::Invalid
                    }
                }
            }
            ast::UnresolvedType::Pointer(inner) => Type::Pointer(Box::new(self.resolve_ty(&inner.0, symbols, errors))),
            ast::UnresolvedType::Array(inner) => {
                let Some(count) = inner.2 else {
                    errors.emit_span(Error::ArraySizeCantBeInferredHere, inner.1.in_mod(self.module.id));
                    return Type::Invalid;
                };
                Type::Array(Box::new((self.resolve_ty(&inner.0, symbols, errors), count)))
            }
            ast::UnresolvedType::Tuple(_, _) => todo!(),
            ast::UnresolvedType::Infer(_) => {
                errors.emit_span(Error::InferredTypeNotAllowedHere, ty.span().in_mod(self.module.id)) ;
                Type::Invalid
            }
        }
    }

    fn resolve_type_info(&self, ty: &ast::UnresolvedType, symbols: &SymbolTable, types: &mut TypeTable, errors: &mut Errors) -> TypeInfo {
        match ty {
            ast::UnresolvedType::Primitive(p, _) => TypeInfo::Primitive(*p),
            ast::UnresolvedType::Unresolved(path, generics) => {
                let Some(id) = self.resolve_path(path, errors) else { return TypeInfo::Invalid };
                match id {                    
                    DefId::Type(id) => {
                        let generic_count = symbols.generic_count(id);
                        let generics = if let Some((generics, generics_span)) = generics {
                            if generics.len() as u8 != generic_count {
                                errors.emit_span(
                                    Error::InvalidGenericCount {
                                        expected: generic_count,
                                        found: generics.len() as u8
                                    },
                                    generics_span.in_mod(self.module.id)
                                );
                                return TypeInfo::Invalid;
                            }
                            let generics: Vec<_> = generics
                                .iter()
                                .map(|ty| self.resolve_type_info(ty, symbols, types, errors))
                                .collect();
                            types.add_multiple(generics)
                        } else {
                            if generic_count != 0 {
                                errors.emit_span(
                                    Error::InvalidGenericCount { expected: generic_count, found: 0 },
                                    path.span().in_mod(self.module.id)
                                );
                                return TypeInfo::Invalid;
                            }
                            TypeTableIndices::EMPTY
                        };
                        TypeInfo::Resolved(id, generics)
                    }
                    DefId::Function(_) | DefId::Module(_) => {
                        errors.emit_span(Error::TypeExpected, path.span().in_mod(self.module.id));
                        TypeInfo::Invalid
                    }
                }
            }
            ast::UnresolvedType::Pointer(inner) => {
                let inner = self.resolve_type_info(&inner.0, symbols, types, errors);
                TypeInfo::Pointer(types.add(inner))
            }
            ast::UnresolvedType::Array(inner) => {
                let Some(count) = inner.2 else {
                    errors.emit_span(Error::ArraySizeCantBeInferredHere, inner.1.in_mod(self.module.id));
                    return TypeInfo::Invalid;
                };
                let elem_ty = self.resolve_type_info(&inner.0, symbols, types, errors);
                TypeInfo::Array(inner.2, types.add(elem_ty))
            }
            ast::UnresolvedType::Tuple(elems, _) => {
                let elems = elems
                    .iter()
                    .map(|ty| self.resolve_type_info(ty, symbols, types, errors))
                    .collect::<Vec<_>>();
                
                TypeInfo::Tuple(types.add_multiple(elems), TupleCountMode::Exact)
            }
            ast::UnresolvedType::Infer(_) => TypeInfo::Unknown,
        }
    }
}

pub struct ExprInfo<'a> {
    pub expected: TypeTableIndex,
    pub ret: TypeTableIndex,
    pub noreturn: &'a mut bool,
}
impl<'a> ExprInfo<'a> {
    pub fn mark_noreturn(&mut self) {
        *self.noreturn = true;
    }
    pub fn with_expected(&mut self, expected: TypeTableIndex) -> ExprInfo {
        ExprInfo { expected, ret: self.ret, noreturn: self.noreturn }
    }
    pub fn with_noreturn<'b>(&self, noreturn: &'b mut bool) -> ExprInfo<'b> {
        ExprInfo { expected: self.expected, ret: self.ret, noreturn }
    }
    pub fn reborrow(&mut self) -> ExprInfo<'_> {
        ExprInfo { expected: self.expected, ret: self.ret, noreturn: &mut *self.noreturn }
    }
}



#[derive(Clone, Copy)]
pub enum LocalDefId {
    Def(DefId),
    Var(VarId),
}
enum LocalOrGlobalScope<'a> {
    Local(&'a LocalScope<'a>),
    Global(&'a Scope<'static>)
}
pub struct LocalScope<'a> {
    parent: LocalOrGlobalScope<'a>,
    scope: Scope<'a>,
    locals: dmap::DHashMap<String, LocalDefId>,
}
impl<'a> LocalScope<'a> {
    pub fn child(&'a self, defs: dmap::DHashMap<String, DefId>) -> LocalScope<'a> {
        LocalScope {
            parent: LocalOrGlobalScope::Local(self),
            scope: Scope {
                module_scopes: self.scope.module_scopes,
                module: self.scope.module,
                parent: Some(&self.scope),
                names: defs,
            },
            locals: dmap::new()
        }
    }
    pub fn define_var(&mut self, name: String, id: VarId) {
        self.locals.insert(name, LocalDefId::Var(id));
    }

    pub fn resolve_local(&self, name: &str, name_span: TSpan, errors: &mut Errors) -> Option<LocalDefId> {
        if let Some(local) = self.locals.get(name) {
            Some(*local)
        } else if let Some(def) = self.scope.names.get(name) {
            Some(LocalDefId::Def(*def))
        } else {
            match self.parent {
                LocalOrGlobalScope::Local(local) => local.resolve_local(name, name_span, errors),
                LocalOrGlobalScope::Global(global) => global.resolve(name, name_span, errors).map(LocalDefId::Def),
            }
        }

    }
}

pub fn resolve_project(ast: &mut Ast, main_module: ModuleId, errors: &mut Errors, require_main_func: bool) {
    let mut symbols = SymbolTable::new();
    // add ids for all definitions
    let mut module_scopes: Vec<_> = ast.modules.iter().enumerate().map(|(i, module)| {
        let module_id = ModuleId::new(i as _);
        let module_ctx = ModuleCtx { src: ast.src(module_id).0, id: module_id, root: main_module };
        let names = scope_defs(&ast[module.definitions], &mut symbols);
        Scope::root(names, module_ctx)
    }).collect();   
    let module_scopes_ptr: *const [Scope] = module_scopes.as_slice();
    for scope in &mut module_scopes {
        scope.set_module_scopes_ptr(module_scopes_ptr);
    }
    // resolve types and function signatures
    for (module, scope) in ast.modules.iter().zip(&mut module_scopes) {
        for (name, def) in &ast[module.definitions] {

            let def_id = *scope.names.get(name).unwrap();
            resolve_def(name, def, def_id, &mut symbols, scope, errors);
        }
    }
    eprintln!("{symbols:?}");
    // function bodies
    for scope in &mut module_scopes {
        for (name, def) in &scope.names {
            match def {
                DefId::Function(func_id) => {
                    let Some(Definition::Function(func)) = ast[ast[scope.module.id].definitions].get(name) else {
                        unreachable!()
                    };

                    if let Some(body) = func.body {
                        let mut types = TypeTable::new();
                        let mut vars = vec![];
                        func_body(body, *func_id, scope, Ctx {
                            ast,
                            symbols: &mut symbols,
                            types: &mut types,
                            errors,
                            vars: &mut vars,
                        });
                    }
                }
                DefId::Type(_) | DefId::Module(_) => {}
            }
        }
    }
}

/// add all order independent definitions to a scope
fn scope_defs<'a>(scope_defs: &'a dmap::DHashMap<String, Definition>, symbols: &mut SymbolTable) -> dmap::DHashMap<String, DefId> {
    scope_defs.iter().map(|(name, def)| {
        let def_id = match def {
            Definition::Function(_) => DefId::Function(symbols.add_func()),
            Definition::Struct(def) => DefId::Type(symbols.add_type(name.clone(), def.generic_count())),
            Definition::Enum(def) => DefId::Type(symbols.add_type(name.clone(), def.generic_count())),
            Definition::Trait(_) => todo!(),
            Definition::Module(_) => todo!(),
            Definition::Use(_) => todo!(),
            Definition::Const(_, _) => todo!(),
            Definition::Global(_, _) => todo!(),
        };
        (name.clone(), def_id)
    }).collect()
}

fn resolve_def(name: &str, def: &Definition, def_id: DefId, symbols: &mut SymbolTable, scope: &mut Scope, errors: &mut Errors) {
    match def {
        Definition::Function(def) => {
            let DefId::Function(id) = def_id else { unreachable!() };
            symbols.place_func(id, func_signature(name.to_owned(), def, scope, symbols, errors));
        }
        Definition::Struct(def) => {
            let DefId::Type(id) = def_id else { unreachable!() };
            symbols.place_type(id, TypeDef::Struct(struct_def(name.to_owned(),def, scope, symbols, errors)));
        }
        Definition::Enum(_) => todo!(),
        Definition::Trait(_) => todo!(),
        Definition::Module(_) => todo!(),
        Definition::Use(_) => todo!(),
        Definition::Const(_, _) => todo!(),
        Definition::Global(_, _) => todo!(),
    }
}

fn func_signature(name: String, func: &ast::Function, scope: &mut Scope, symbols: &SymbolTable, errors: &mut Errors)
-> FunctionHeader {
    let params = func.params.iter().map(|(name, ty, _, _)| {
        (name.clone(), scope.resolve_ty(ty, symbols, errors))
    }).collect();

    let return_type = scope.resolve_ty(&func.return_type, symbols, errors);

    FunctionHeader {
        name,
        params,
        return_type,
        varargs: func.varargs,
    }
}

fn struct_def(name: String, def: &ast::StructDefinition, scope: &mut Scope, symbols: &SymbolTable, errors: &mut Errors)
-> Struct {
    let members = def.members.iter().map(|(name, ty, _, _)| {
        (name.clone(), scope.resolve_ty(ty, symbols, errors))
    }).collect();

    Struct {
        name,
        members,
        symbols: dmap::new(),
        generic_count: def.generic_count(),
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct VarId(u32);
impl VarId {
    pub const MISSING: Self = Self(u32::MAX);
}

struct Ctx<'a> {
    ast: &'a mut Ast,
    symbols: &'a mut SymbolTable,
    types: &'a mut TypeTable,
    errors: &'a mut Errors,
    vars: &'a mut Vec<TypeTableIndex>,
}
impl<'a> Ctx<'a> {
    fn reborrow(&mut self) -> Ctx<'_> {
        Ctx {
            ast: &mut *self.ast,
            symbols: &mut *self.symbols,
            types: &mut *self.types,
            errors: &mut *self.errors,
            vars: &mut *self.vars,
        }
    }

    fn specify(&mut self, idx: TypeTableIndex, info: TypeInfo, span: Span) {
        self.types.specify(idx, info, self.errors, span, &self.symbols)
    }

    fn new_var(&mut self, ty: TypeTableIndex) -> VarId {
        let id = VarId(self.vars.len() as u32);
        self.vars.push(ty);
        id
    }
}

fn func_body<'src>(body: ExprRef, func_id: FunctionId, scope: &Scope<'static>, mut ctx: Ctx) {
    let mut scope = scope.child();
    let signature = ctx.symbols.get_func(func_id);
    for (name, ty) in &signature.params {
        let type_info = ty.as_info(ctx.types);
        let ty = ctx.types.add(type_info);
        let var = VarId(ctx.vars.len() as _);
        ctx.vars.push(ty);
        scope.define_var(name.clone(), var);
    }

    let signature = ctx.symbols.get_func(func_id);
    let return_type_info = signature.return_type.as_info(ctx.types);
    let expected = ctx.types.add(return_type_info);

    let mut noreturn = false;
    scope.expr(body, ExprInfo { expected, ret: expected, noreturn: &mut noreturn }, ctx);
}