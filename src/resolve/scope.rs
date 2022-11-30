use crate::{ast::{ModuleId, self, TypeId, ExprRef, Ast}, dmap::{DHashMap, self}, span::{TSpan, Span}, error::{Errors, Error}, parser::Counts};

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

pub struct Scope<'a> {
    module_scopes: *const [Scope<'static>],
    pub module: ModuleCtx,
    parent: Option<&'a Scope<'a>>,
    names: DHashMap<String, UnresolvedDefId>,
}
impl Scope<'static> {
    pub fn root(names: DHashMap<String, UnresolvedDefId>, module_ctx: ModuleCtx) -> Self {
        Self {
            module_scopes: &[],
            module: module_ctx,
            parent: None,
            names,
        }
    }
    pub fn set_module_scopes_ptr(&mut self, module_scopes: *const [Scope<'static>]) {
        self.module_scopes = module_scopes;
    }
}
impl<'a> Scope<'a> {
    pub fn child_scope(&mut self, names: DHashMap<String, UnresolvedDefId>) -> Scope<'_> {
        Scope {
            module_scopes: self.module_scopes,
            module: self.module,
            parent: Some(self),
            names,
        }
    }

    pub fn child(&self) -> LocalScope<'_> {
        LocalScope {
            parent: LocalOrGlobalScope::Global(self),
            scope: Scope {
                module_scopes: self.module_scopes,
                module: self.module,
                parent: Some(self),
                names: dmap::new(),
            },
            locals: dmap::new(),
        }
    }

    pub fn signature_scope(&self, generics: DHashMap<String, UnresolvedDefId>) -> Scope {
        Scope {
            module_scopes: self.module_scopes,
            module: self.module,
            parent: Some(self),
            names: generics,
        }
    }
    pub fn module_scope(&'a self, id: ModuleId) -> &'a Scope<'static> {
        unsafe { &(*self.module_scopes)[id.idx()] }
    }

    pub fn resolve(&self, name: &str, name_span: Span, errors: &mut Errors, symbols: &mut SymbolTable, ast: &Ast) -> DefId {
        // PERF: make non-recursive
        if let Some(id) = self.names.get(name) {
            match id {
                UnresolvedDefId::Resolved(id) => *id,

                // TODO: when parent scopes are mutable somehow, update in self.names so resolval is cached :
                UnresolvedDefId::Const { expr, ty, counts } => {
                    match const_val::eval(*expr, ty, *counts, self, errors, ast, symbols) {
                        const_val::ConstResult::Val(val) => DefId::Const(symbols.add_const(val)),
                        const_val::ConstResult::Symbol(def) => def.as_def_id(),
                    }
                }
                UnresolvedDefId::Use(path) => self.resolve_path(path, errors, symbols, ast),
            }
        } else {
            if let Some(parent) = self.parent {
                return parent.resolve(name, name_span, errors, symbols, ast);
            } else {
                errors.emit_span(Error::UnknownIdent, name_span);
                DefId::Invalid
            }
        }
    }

    /// Resolves everything in a path except the last segment.
    /// Returns None if the path was invalid and Some(None) if the path is simply empty.
    pub fn resolve_path_front<'s>(
        &self,
        root: Option<TSpan>,
        middle: impl Iterator<Item = (&'s str, TSpan)>,
        errors: &mut Errors,
        symbols: &mut SymbolTable,
        ast: &Ast,
    ) -> Option<Option<ModuleId>> {
        let mut current_module = if root.is_some() { Some(self.module.root) } else { None };

        for (segment, segment_span) in middle {
            let scope = if let Some(module) = current_module {
                self.module_scope(module)
            } else {
                self
            };
            match scope.resolve(segment, segment_span.in_mod(self.module.id), errors, symbols, ast) {
                DefId::Module(id) => current_module = Some(id),
                _ => {
                    errors.emit_span(Error::ModuleExpected, segment_span.in_mod(self.module.id));
                    return None;
                }
            }
        }

        Some(current_module)
    }

    
    /// retrieve a definition in this scope
    pub fn get_def(&self, name: &str) -> Option<&UnresolvedDefId> {
        self.names.get(name)
    }
    
    /*
    /// retrieve a mutable reference to a definition in this scope
    pub fn get_def_mut(&mut self, name: &str) -> &mut DefId {
        self.names.get_mut(name).unwrap()
    }
    */

    pub fn resolve_path(&self, path: &ast::IdentPath, errors: &mut Errors, symbols: &mut SymbolTable, ast: &Ast) -> DefId {
        let (root, middle, last) = path.segments(self.module.src());
        let Some(current_module) = self.resolve_path_front(root, middle, errors, symbols, ast) else { return DefId::Invalid };

        if let Some((segment, span)) = last {
            if let Some(module) = current_module {
                self.module_scope(module)
            } else {
                self
            }.resolve(segment, span.in_mod(self.module.id), errors, symbols, ast)
        } else {
            // should be fine to unwrap here since empty paths don't exist
            DefId::Module(current_module.unwrap())
        }
    }

    pub fn resolve_ty(&self, ty: &ast::UnresolvedType, errors: &mut Errors, symbols: &mut SymbolTable, ast: &Ast) -> Type {
        match ty {
            ast::UnresolvedType::Primitive(p, _) => Type::Prim(*p),
            ast::UnresolvedType::Unresolved(path, generics) => {
                match self.resolve_path(path, errors, symbols, ast) {                    
                    DefId::Type(id) => self.generic_type_instantiation(
                        path,
                        id,
                        generics,
                        symbols,
                        errors,
                        None,
                        |id, symbols, errors| self.resolve_ty(id, errors, symbols, ast)
                    ).map_or(Type::Invalid, |generics| Type::Id(id, generics)),
                    DefId::Generic(i) => Type::Generic(i),
                    DefId::Function(_) | DefId::Trait(_) | DefId::TraitFunc(_, _)
                    | DefId::Module(_) | DefId::Global(_) | DefId::Const(_) => {
                        errors.emit_span(Error::TypeExpected, path.span().in_mod(self.module.id));
                        Type::Invalid
                    }
                    DefId::Invalid => Type::Invalid
                }
            }
            ast::UnresolvedType::Pointer(inner) => Type::Pointer(Box::new(self.resolve_ty(&inner.0, errors, symbols, ast))),
            ast::UnresolvedType::Array(inner) => {
                let Some(count) = inner.2 else {
                    errors.emit_span(Error::ArraySizeCantBeInferredHere, inner.1.in_mod(self.module.id));
                    return Type::Invalid;
                };
                Type::Array(Box::new((self.resolve_ty(&inner.0, errors, symbols, ast), count)))
            }
            ast::UnresolvedType::Tuple(members, _) => Type::Tuple(
                members
                    .iter()
                    .map(|ty| self.resolve_ty(ty, errors, symbols, ast))
                    .collect()
            ),
            ast::UnresolvedType::Infer(_) => {
                errors.emit_span(Error::InferredTypeNotAllowedHere, ty.span().in_mod(self.module.id)) ;
                Type::Invalid
            }
        }
    }

    pub fn generic_type_instantiation<T: Clone>(
        &self,
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
                    generics_span.in_mod(self.module.id)
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
                        path.span().in_mod(self.module.id)
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
enum LocalOrGlobalScope<'a> {
    Local(&'a LocalScope<'a>),
    Global(&'a Scope<'a>)
}
pub struct LocalScope<'a> {
    parent: LocalOrGlobalScope<'a>,
    pub scope: Scope<'a>,
    pub locals: DHashMap<String, LocalDefId>,
}
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
    pub fn child_with_defs(&'a self, defs: &DHashMap<String, ast::Definition>, ast: &Ast, symbols: &mut SymbolTable, errors: &mut Errors)
    -> LocalScope<'a> {
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
            super::resolve_def(name, def, ast, symbols, &mut scope.scope, errors);
        }

        // function bodies
        super::scope_bodies(&scope.scope, defs, &ast, symbols, errors);

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

    pub fn resolve_path(&self, path: &ast::IdentPath, errors: &mut Errors, symbols: &mut SymbolTable, ast: &Ast) -> LocalDefId {
        let (root, middle, last) = path.segments(self.scope.module.src());
        let Some(current_module) = self.scope.resolve_path_front(root, middle, errors, symbols, ast) else {
            return LocalDefId::Def(DefId::Invalid);
        };

        if let Some((segment, span)) = last {
            if let Some(module) = current_module {
                LocalDefId::Def(self.scope.module_scope(module).resolve(segment, span.in_mod(self.mod_id()), errors, symbols, ast))
            } else {
                self.resolve_local(segment, span, errors, symbols, ast)
            }
        } else {
            // should be fine to unwrap here since empty paths don't exist
            LocalDefId::Def(DefId::Module(current_module.unwrap()))
        }
    }

    pub fn resolve_type_info(&self, ty: &ast::UnresolvedType, types: &mut TypeTable, errors: &mut Errors, symbols: &mut SymbolTable, ast: &Ast)
    -> TypeInfoOrIndex {
        TypeInfoOrIndex::Type(match ty {
            ast::UnresolvedType::Primitive(p, _) => TypeInfo::Primitive(*p),
            ast::UnresolvedType::Unresolved(path, generics) => {
                let id = self.resolve_path(path, errors, symbols, ast);
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
                            |ty, symbols, errors| self.resolve_type_info(ty, types, errors, symbols, ast)
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
                let inner = self.resolve_type_info(&inner.0, types, errors, symbols, ast);
                TypeInfo::Pointer(types.add_info_or_idx(inner))
            }
            ast::UnresolvedType::Array(inner) => {
                let elem_ty = self.resolve_type_info(&inner.0, types, errors, symbols, ast);
                TypeInfo::Array(inner.2, types.add_info_or_idx(elem_ty))
            }
            ast::UnresolvedType::Tuple(elems, _) => {
                let elems = elems
                    .iter()
                    .map(|ty| self.resolve_type_info(ty, types, errors, symbols, ast))
                    .collect::<Vec<_>>();
                
                TypeInfo::Tuple(types.add_multiple_info_or_index(elems), TupleCountMode::Exact)
            }
            ast::UnresolvedType::Infer(_) => TypeInfo::Unknown,
        })
    }

    pub fn resolve_local(&self, name: &str, name_span: TSpan, errors: &mut Errors, symbols: &mut SymbolTable, ast: &Ast) -> LocalDefId {
        if let Some(local) = self.locals.get(name) {
            local.clone()
        } else if let Some(def) = self.scope.names.get(name) {
            match def {
                UnresolvedDefId::Resolved(def) => LocalDefId::Def(*def),
                // TODO: also update here in locals so resolval only happens once (when scope parents are mutable)
                UnresolvedDefId::Const { expr, ty, counts } => {
                    match const_val::eval(*expr, ty, *counts, &self.scope, errors, ast, symbols) {
                        const_val::ConstResult::Val(val) => LocalDefId::Def(DefId::Const(symbols.add_const(val))),
                        const_val::ConstResult::Symbol(def) => LocalDefId::Def(def.as_def_id()),
                    }
                }
                UnresolvedDefId::Use(path) => self.resolve_path(path, errors, symbols, ast),
            }
        } else {
            match self.parent {
                LocalOrGlobalScope::Local(local) => local.resolve_local(name, name_span, errors, symbols, ast),
                LocalOrGlobalScope::Global(global) => LocalDefId::Def(
                    global.resolve(name, name_span.in_mod(self.mod_id()), errors, symbols, ast)
                ),
            }
        }
    }

    pub fn span(&self, expr: ExprRef, ast: &Ast) -> Span {
        ast[expr].span_in(ast, self.scope.module.id)
    }
}