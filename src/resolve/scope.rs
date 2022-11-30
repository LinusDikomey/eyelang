use std::ops::{Index, IndexMut};

use crate::{ast::{ModuleId, self, TypeId, ExprRef, Ast}, dmap::{DHashMap, self}, span::{TSpan, Span}, error::{Errors, Error}, parser::Counts, irgen, help::id};

use super::{types::{DefId, SymbolTable, Type, TupleCountMode}, type_info::{TypeTableIndex, TypeInfoOrIndex, TypeInfo, TypeTable}, VarId, const_val};

#[derive(Clone, Copy)]
pub struct ModuleCtx {
    pub src: *const str,
    pub id: ModuleId,
    pub root: ModuleId,
}
impl ModuleCtx {
    pub fn src(&self) -> &str {
        unsafe { &*self.src }
    }
}

/// A DefId that might not be fully resolved, for example when constants or use statements are present
#[derive(Clone, Debug)]
pub enum UnresolvedDefId {
    Resolved(DefId),
    Const {
        expr: ExprRef,
        ty: ast::UnresolvedType,
        counts: Counts,
    },
    Use(ast::IdentPath),
}

id!(u64, 8: ScopeId);
impl ScopeId {
    pub fn module(module: ModuleId) -> Self {
        Self(module.idx() as _)
    }
}

struct ParentScope {
    id: ScopeId,
    can_see_locals: bool,
}

pub struct Scope {
    pub module: ModuleCtx,
    parent: Option<ParentScope>,
    names: DHashMap<String, UnresolvedDefId>,
    locals: DHashMap<String, LocalDefId>,
}
impl Scope {
    pub fn root(names: DHashMap<String, UnresolvedDefId>, module_ctx: ModuleCtx) -> Self {
        Self {
            module: module_ctx,
            parent: None,
            names,
            locals: dmap::new(),
        }
    }

    pub fn get_def(&self, name: &str) -> Option<&UnresolvedDefId> {
        self.names.get(name)
    }
}

pub struct Scopes {
    scopes: Vec<Scope>,
}
impl Index<ScopeId> for Scopes {
    type Output = Scope;

    fn index(&self, index: ScopeId) -> &Self::Output {
        &self.scopes[index.idx()]
    }
}
impl IndexMut<ScopeId> for Scopes {
    fn index_mut(&mut self, index: ScopeId) -> &mut Self::Output {
        &mut self.scopes[index.idx()]
    }
}
impl Scopes {
    pub fn new(module_scopes: Vec<Scope>) -> Self {
        Self { scopes: module_scopes }
    }
    pub fn add(&mut self, scope: Scope) -> ScopeId {
        self.scopes.push(scope);
        ScopeId((self.scopes.len() - 1) as _)
    }

    pub fn child(&mut self, parent: ScopeId, names: DHashMap<String, UnresolvedDefId>, locals: DHashMap<String, LocalDefId>, can_see_locals: bool) -> ScopeId {
        self.add(Scope {
            module: self[parent].module,
            parent: Some(ParentScope { id: parent, can_see_locals }),
            names,
            locals,
        })
    }
    
    pub fn resolve(&mut self, mut id: ScopeId, name: &str, name_span: Span, errors: &mut Errors, symbols: &mut SymbolTable, ast: &Ast, ir: &mut irgen::Functions) -> DefId {
        // PERF: make non-recursive
        loop {
            let scope = &mut self[id];
            if let Some(def_id) = scope.names.get(name) {
                return match def_id {
                    UnresolvedDefId::Resolved(id) => *id,
    
                    // TODO: when parent scopes are mutable somehow, update in self.names so resolval is cached :
                    UnresolvedDefId::Const { expr, ty, counts } => {
                        match const_val::eval(*expr, ty, *counts, self, id, errors, ast, symbols, ir) {
                            const_val::ConstResult::Val(val) => DefId::Const(symbols.add_const(val)),
                            const_val::ConstResult::Symbol(def) => def.as_def_id(),
                        }
                    }
                    UnresolvedDefId::Use(path) => self.resolve_path(id, path, errors, symbols, ast, ir),
                }
            } else {
                if let Some(parent) = scope.parent {
                    id = parent.id;
                } else {
                    errors.emit_span(Error::UnknownIdent, name_span);
                    return DefId::Invalid;
                }
            }
        }
        
    }

    fn module_scope(&self, module: ModuleId) -> &Scope { &self.scopes[module.idx()] }
    fn module_scope_mut(&mut self, module: ModuleId) -> &mut Scope { &mut self.scopes[module.idx()] }

    /// Resolves everything in a path except the last segment.
    /// Returns None if the path was invalid and Some(None) if the path is simply empty.
    pub fn resolve_path_front<'s>(
        &self,
        id: ScopeId,
        root: Option<TSpan>,
        middle: impl Iterator<Item = (&'s str, TSpan)>,
        errors: &mut Errors,
        symbols: &mut SymbolTable,
        ast: &Ast,
        ir_functions: &mut irgen::Functions,
    ) -> Option<Option<ModuleId>> {
        let mut current_module = None;
        for (segment, segment_span) in middle {
            let scope = if let Some(module) = current_module {
                ScopeId::module(module)
            } else {
                id
            };
            match self.resolve(scope, segment, segment_span.in_mod(self[id].module.id), errors, symbols, ast, ir_functions) {
                DefId::Module(id) => current_module = Some(id),
                _ => {
                    errors.emit_span(Error::ModuleExpected, segment_span.in_mod(self[id].module.id));
                    return None;
                }
            }
        }

        Some(current_module)
    }

    pub fn resolve_path(&self, id: ScopeId, path: &ast::IdentPath, errors: &mut Errors, symbols: &mut SymbolTable, ast: &Ast, ir: &mut irgen::Functions) -> DefId {
        let (root, middle, last) = path.segments(self[id].module.src());
        let module_id = self[id].module.id;
        let Some(module) = self.resolve_path_front(id, root, middle, errors, symbols, ast, ir) else { return DefId::Invalid };

        if let Some((segment, span)) = last {
            let scope = module.map_or(id, ScopeId::module);
            self.resolve(scope, segment, span.in_mod(module_id), errors, symbols, ast, ir)
        } else {
            // should be fine to unwrap here since empty paths don't exist
            DefId::Module(module.unwrap())
        }
    }

    pub fn resolve_ty(&self, scope: ScopeId, ty: &ast::UnresolvedType, errors: &mut Errors, symbols: &mut SymbolTable, ast: &Ast, ir: &mut irgen::Functions) -> Type {
        match ty {
            ast::UnresolvedType::Primitive(p, _) => Type::Prim(*p),
            ast::UnresolvedType::Unresolved(path, generics) => {
                match self.resolve_path(scope, path, errors, symbols, ast, ir) {                    
                    DefId::Type(id) => self.generic_type_instantiation(
                        scope,
                        path,
                        id,
                        generics,
                        symbols,
                        errors,
                        None,
                        |type_id, symbols, errors| self.resolve_ty(scope, type_id, errors, symbols, ast, ir)
                    ).map_or(Type::Invalid, |generics| Type::Id(id, generics)),
                    DefId::Generic(i) => Type::Generic(i),
                    DefId::Function(_) | DefId::Trait(_) | DefId::TraitFunc(_, _)
                    | DefId::Module(_) | DefId::Global(_) | DefId::Const(_) => {
                        errors.emit_span(Error::TypeExpected, path.span().in_mod(self[scope].module.id));
                        Type::Invalid
                    }
                    DefId::Invalid => Type::Invalid
                }
            }
            ast::UnresolvedType::Pointer(inner) => Type::Pointer(Box::new(self.resolve_ty(scope, &inner.0, errors, symbols, ast, ir))),
            ast::UnresolvedType::Array(inner) => {
                let Some(count) = inner.2 else {
                    errors.emit_span(Error::ArraySizeCantBeInferredHere, inner.1.in_mod(self[scope].module.id));
                    return Type::Invalid;
                };
                Type::Array(Box::new((self.resolve_ty(scope, &inner.0, errors, symbols, ast, ir), count)))
            }
            ast::UnresolvedType::Tuple(members, _) => Type::Tuple(
                members
                    .iter()
                    .map(|ty| self.resolve_ty(scope, ty, errors, symbols, ast, ir))
                    .collect()
            ),
            ast::UnresolvedType::Infer(_) => {
                errors.emit_span(Error::InferredTypeNotAllowedHere, ty.span().in_mod(self[scope].module.id)) ;
                Type::Invalid
            }
        }
    }

    pub fn generic_type_instantiation<T: Clone>(
        &self,
        scope: ScopeId,
        path: &ast::IdentPath,
        id: TypeId,
        generics: &Option<(Vec<ast::UnresolvedType>, TSpan)>,
        symbols: &mut SymbolTable,
        errors: &mut Errors,
        on_omitted_generic: Option<T>,
        mut resolve_ty: impl FnMut(&ast::UnresolvedType, &mut SymbolTable, &mut Errors) -> T,
    ) -> Option<Vec<T>> {
        let generic_count = symbols.generic_count(id);
        let generics = if let Some((generics, generics_span)) = generics {
            if generics.len() as u8 != generic_count {
                errors.emit_span(
                    Error::InvalidGenericCount {
                        expected: generic_count,
                        found: generics.len() as u8
                    },
                    generics_span.in_mod(self[scope].module.id)
                );
                return None;
            }
            generics
                .iter()
                .map(|ty| resolve_ty(ty, symbols, errors))
                .collect()
        } else {
            if generic_count != 0 {
                if let Some(on_omitted) = on_omitted_generic {
                    vec![on_omitted; generic_count as usize]
                } else {
                    errors.emit_span(
                        Error::InvalidGenericCount { expected: generic_count, found: 0 },
                        path.span().in_mod(self[scope].module.id)
                    );
                    return None;
                }
            } else {
                vec![]
            }
        };
        Some(generics)
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



#[derive(Clone, Debug)]
pub enum LocalDefId {
    Def(DefId),
    Var(VarId),
    Type(TypeTableIndex),
}

/*
impl<'a> LocalScope<'a> {
    pub fn child(&'a self, locals: DHashMap<String, LocalDefId>) -> LocalScope<'a> {
        LocalScope {
            parent: LocalOrGlobalScope::Local(self),
            scope: Scope {
                module_scopes: self.scope.module_scopes,
                module: self.scope.module,
                parent: Some(&self.scope),
                names: dmap::new(),
            },
            locals,
        }
    }
    pub fn child_with_defs(
        &'a self,
        defs: &DHashMap<String, ast::Definition>,
        ast: &Ast,
        symbols: &mut SymbolTable,
        errors: &mut Errors,
        ir_functions: &mut irgen::Functions
    ) -> LocalScope<'a> {
        let names = super::scope_defs(defs);
        //super::cross_resolve::local(defs, &mut names, &self.scope, ast, errors);
        
        let mut scope = LocalScope {
            parent: LocalOrGlobalScope::Local(self),
            scope: Scope {
                module_scopes: self.scope.module_scopes,
                module: self.scope.module,
                parent: Some(&self.scope),
                names,
            },
            locals: dmap::new(),
        };
        
        // resolve types, function signatures
        for (name, def) in defs {
            super::resolve_def(name, def, ast, symbols, &mut scope.scope, errors, ir_functions);
        }

        // function bodies
        super::scope_bodies(&scope.scope, defs, &ast, symbols, errors, ir_functions);

        scope
    }

    pub fn mod_id(&self) -> ModuleId {
        self.scope.module.id
    }
    pub fn define_var(&mut self, name: String, id: VarId) {
        self.locals.insert(name, LocalDefId::Var(id));
    }
    pub fn add_generic(&mut self, name: String, ty: TypeTableIndex) {
        self.locals.insert(name, LocalDefId::Type(ty));
    }

    pub fn resolve_path(&self, path: &ast::IdentPath, errors: &mut Errors, symbols: &mut SymbolTable, ast: &Ast, ir: &mut irgen::Functions) -> LocalDefId {
        let (root, middle, last) = path.segments(self.scope.module.src());
        let Some(current_module) = self.scope.resolve_path_front(root, middle, errors, symbols, ast, ir) else {
            return LocalDefId::Def(DefId::Invalid);
        };

        if let Some((segment, span)) = last {
            if let Some(module) = current_module {
                LocalDefId::Def(self.scope.module_scope(module).resolve(segment, span.in_mod(self.mod_id()), errors, symbols, ast, ir))
            } else {
                self.resolve_local(segment, span, errors, symbols, ast, ir)
            }
        } else {
            // should be fine to unwrap here since empty paths don't exist
            LocalDefId::Def(DefId::Module(current_module.unwrap()))
        }
    }

    pub fn resolve_type_info(
        &self,
        ty: &ast::UnresolvedType,
        types: &mut TypeTable,
        errors: &mut Errors,
        symbols: &mut SymbolTable,
        ast: &Ast,
        ir: &mut irgen::Functions
    ) -> TypeInfoOrIndex {
        TypeInfoOrIndex::Type(match ty {
            ast::UnresolvedType::Primitive(p, _) => TypeInfo::Primitive(*p),
            ast::UnresolvedType::Unresolved(path, generics) => {
                let id = self.resolve_path(path, errors, symbols, ast, ir);
                match id {
                    LocalDefId::Type(idx) => {
                        if let Some((_, generics_span)) = generics {
                            errors.emit_span(Error::UnexpectedGenerics, generics_span.in_mod(self.mod_id()));
                            return TypeInfoOrIndex::Type(TypeInfo::Invalid);
                        }
                        return TypeInfoOrIndex::Idx(idx);
                    }
                    LocalDefId::Def(DefId::Type(id)) => {
                        self.scope.generic_type_instantiation(path, id, generics, symbols, errors,
                            Some(TypeInfoOrIndex::Type(TypeInfo::Unknown)),
                            |ty, symbols, errors| self.resolve_type_info(ty, types, errors, symbols, ast, ir)
                        )
                        .map_or(
                            TypeInfo::Invalid,
                            |generics| TypeInfo::Resolved(id, types.add_multiple_info_or_index(generics))
                        )
                    }
                    LocalDefId::Def(DefId::Generic(i)) => TypeInfo::Generic(i),
                    LocalDefId::Var(_) | LocalDefId::Def(
                        DefId::Function(_) | DefId::Module(_) | DefId::Trait(_)
                        | DefId::TraitFunc(_, _) | DefId::Global(_) | DefId::Const(_)
                    ) => {
                        errors.emit_span(Error::TypeExpected, path.span().in_mod(self.mod_id()));
                        TypeInfo::Invalid
                    }
                    LocalDefId::Def(DefId::Invalid) => TypeInfo::Invalid
                }
            }
            ast::UnresolvedType::Pointer(inner) => {
                let inner = self.resolve_type_info(&inner.0, types, errors, symbols, ast, ir);
                TypeInfo::Pointer(types.add_info_or_idx(inner))
            }
            ast::UnresolvedType::Array(inner) => {
                let elem_ty = self.resolve_type_info(&inner.0, types, errors, symbols, ast, ir);
                TypeInfo::Array(inner.2, types.add_info_or_idx(elem_ty))
            }
            ast::UnresolvedType::Tuple(elems, _) => {
                let elems = elems
                    .iter()
                    .map(|ty| self.resolve_type_info(ty, types, errors, symbols, ast, ir))
                    .collect::<Vec<_>>();
                
                TypeInfo::Tuple(types.add_multiple_info_or_index(elems), TupleCountMode::Exact)
            }
            ast::UnresolvedType::Infer(_) => TypeInfo::Unknown,
        })
    }

    pub fn resolve_local(&self, name: &str, name_span: TSpan, errors: &mut Errors, symbols: &mut SymbolTable, ast: &Ast, ir: &mut irgen::Functions) -> LocalDefId {
        if let Some(local) = self.locals.get(name) {
            local.clone()
        } else if let Some(def) = self.scope.names.get(name) {
            match def {
                UnresolvedDefId::Resolved(def) => LocalDefId::Def(*def),
                // TODO: also update here in locals so resolval only happens once (when scope parents are mutable)
                UnresolvedDefId::Const { expr, ty, counts } => {
                    match const_val::eval(*expr, ty, *counts, &self.scope, errors, ast, symbols, ir) {
                        const_val::ConstResult::Val(val) => LocalDefId::Def(DefId::Const(symbols.add_const(val))),
                        const_val::ConstResult::Symbol(def) => LocalDefId::Def(def.as_def_id()),
                    }
                }
                UnresolvedDefId::Use(path) => self.resolve_path(path, errors, symbols, ast, ir),
            }
        } else {
            match self.parent {
                LocalOrGlobalScope::Local(local) => local.resolve_local(name, name_span, errors, symbols, ast, ir),
                LocalOrGlobalScope::Global(global) => LocalDefId::Def(
                    global.resolve(name, name_span.in_mod(self.mod_id()), errors, symbols, ast, ir)
                ),
            }
        }
    }

    pub fn span(&self, expr: ExprRef, ast: &Ast) -> Span {
        ast[expr].span_in(ast, self.scope.module.id)
    }
}
*/