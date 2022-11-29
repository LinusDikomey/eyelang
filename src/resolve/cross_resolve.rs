use crate::{ast::{ModuleId, Ast, Definition, UnresolvedType, ExprRef}, span::TSpan, error::{Errors, Error}, dmap::DHashMap};

use super::{scope::{Scope, ResolvedLocalScope}, types::{DefId, SymbolTable}, consts::{self, ConstResult, ConstVal}, type_info::TypeTable, expr::LocalScope};


pub(super) fn top_level<'src>(module_scopes: &mut [Scope<'static>], symbols: &mut SymbolTable, ast: &Ast, errors: &mut Errors) {
    for i in 0..module_scopes.len() {
        let module = ModuleId::new(i as u32);
        let mut scope = UnfinishedGlobalScope { scopes: module_scopes, module, ast };
        for (name, def) in &ast[ast[module].definitions] {
            scope.cross_resolve_top_level(name, def, module, symbols, errors);
        }
    }
}


pub struct UnfinishedGlobalScope<'a> {
    pub scopes: &'a mut [Scope<'static>],
    pub module: ModuleId,
    ast: &'a Ast,
}
impl<'a> UnfinishedGlobalScope<'a> {
    fn cross_resolve_top_level_by_name(
        &mut self,
        name: &str,
        span: TSpan,
        module: ModuleId,
        symbols: &mut SymbolTable,
        errors: &mut Errors,
    ) -> DefId {

        let Some(def) = self.ast[self.ast[module].definitions].get(name) else {
            errors.emit_span(Error::UnknownIdent, span.in_mod(module));
            return DefId::Invalid;
        };
        self.cross_resolve_top_level(name, def, module, symbols, errors)
    }

    fn cross_resolve_top_level(
        &mut self,
        def_name: &str,
        def: &Definition,
        module: ModuleId,
        symbols: &mut SymbolTable,
        errors: &mut Errors
    ) -> DefId {

        match self.scopes[module.idx()].get_def_mut(def_name) {
            DefId::Unresolved { resolving } => {
                if *resolving {
                    let span = match def {
                        Definition::Use(path) => path.span(),
                        Definition::Const(_, expr) => self.ast[*expr].span(self.ast),
                        _ => unreachable!()
                    };
                    errors.emit_span(Error::RecursiveDefinition, span.in_mod(module));
                    return DefId::Invalid;
                }
                *resolving = true;

                let def_id = match def {
                    Definition::Use(path) => {
                        let (root, segments, last) = path.segments(self.ast.src(module).0);
                        
                        let mut cur_mod = if root.is_some() {
                            self.scopes[module.idx()].module.root
                        } else {
                            module
                        };

                        for (name, name_span) in segments {
                            match self.cross_resolve_top_level_by_name(name, name_span, cur_mod, symbols, errors) {
                                DefId::Module(id) => cur_mod = id,
                                DefId::Invalid => {
                                    *self.scopes[module.idx()].get_def_mut(def_name) = DefId::Invalid;
                                    return DefId::Invalid
                                }
                                _ => {
                                    *self.scopes[module.idx()].get_def_mut(def_name) = DefId::Invalid;
                                    errors.emit_span(Error::ModuleExpected, name_span.in_mod(module));
                                    return DefId::Invalid
                                }
                            }
                        }

                        if let Some((last_name, last_span)) = last {
                            self.cross_resolve_top_level_by_name(last_name, last_span, cur_mod, symbols, errors)
                        } else {
                            DefId::Module(cur_mod)
                        }
                    }
                    Definition::Const(ty, val) => {
                        // TODO: proper scope
                        let scope: ResolvedLocalScope = todo!();/*self.child() */
                        let c = eval_const(scope, ty, *val, symbols, errors);
                        const_res_to_def_id(c, symbols)
                    }
                    _ => unreachable!()
                };
                *self.scopes[module.idx()].get_def_mut(def_name) = def_id;
                def_id
            }
            other => *other
        }
    }
}

pub struct UnfinishedLocalScope<'a> {
    defs: &'a DHashMap<String, Definition>,
    scope_defs: &'a mut DHashMap<String, DefId>,
    parent: &'a Scope<'a>,
}
impl<'a> UnfinishedLocalScope<'a> {
    fn cross_resolve_local_by_name(
        &mut self,
        name: &str,
        name_span: TSpan,
        symbols: &mut SymbolTable,
        ast: &Ast,
        errors: &mut Errors
    ) -> DefId {
        let Some(def) = self.defs.get(name) else {
            return self.parent.resolve(name, name_span.in_mod(self.parent.module.id), errors);
        };
        self.cross_resolve_local(def, name, symbols, ast, errors)
    }

    fn cross_resolve_local(
        &mut self,
        def: &Definition,
        name: &str,
        symbols: &mut SymbolTable,
        ast: &Ast,
        errors: &mut Errors
    ) -> DefId {
        match self.scope_defs.get(name).unwrap() {
            DefId::Unresolved { resolving } => {
                if *resolving {
                    let span = match def {
                        Definition::Use(path) => path.span(),
                        Definition::Const(_, expr) => ast[*expr].span(ast),
                        _ => unreachable!()
                    };
                    errors.emit_span(Error::RecursiveDefinition, span.in_mod(self.parent.module.id));
                    return DefId::Invalid;
                }
                
                let def_id = match def {
                    Definition::Use(path) => {
                        let (root, segments, last) = path.segments(ast.src(self.parent.module.id).0);
                        if root.is_some() {
                            self.parent.resolve_path(path, errors)
                        } else {
                            let mut current_module = None;
                            for (name, name_span) in segments {
                                let next_mod = if let Some(current) = current_module {
                                    self.parent.module_scope(current).resolve(name, name_span.in_mod(self.parent.module.id), errors)
                                } else {
                                    self.cross_resolve_local_by_name(name, name_span, symbols, ast, errors)
                                };
                                match next_mod {
                                    DefId::Module(id) => current_module = Some(id),
                                    DefId::Invalid => {
                                        *self.scope_defs.get_mut(name).unwrap() = DefId::Invalid;
                                        return DefId::Invalid;
                                    }
                                    _ => {
                                        errors.emit_span(Error::ModuleExpected, name_span.in_mod(self.parent.module.id));
                                        *self.scope_defs.get_mut(name).unwrap() = DefId::Invalid;
                                        return DefId::Invalid;
                                    }
                                }
                            }

                            if let Some((last_name, name_span)) = last {
                                if let Some(module) = current_module {
                                    self.parent.module_scope(module)
                                        .resolve(last_name, name_span.in_mod(self.parent.module.id), errors)
                                } else {
                                    self.cross_resolve_local_by_name(last_name, name_span, symbols, ast, errors)
                                }
                            } else {
                                DefId::Module(current_module.unwrap())
                            }
                        }
                    }
                    Definition::Const(ty, val) => {
                        // TODO: proper scope here
                        let scope: ResolvedLocalScope = todo!();
                        // self.child()
                        let c = eval_const(scope, ty, *val, symbols, errors);
                        const_res_to_def_id(c, symbols)
                    }
                    _ => unreachable!()
                };

                *self.scope_defs.get_mut(name).unwrap() = def_id;
                def_id
            }
            other => *other
        }
    }
}
/*
impl LocalScope for UnfinishedLocalScope {
    fn module(&self) -> super::scope::ModuleCtx {
        todo!()
    }

    fn resolve_type_info(&mut self, ty: &UnresolvedType, symbols: &mut SymbolTable, types: &mut SymbolTable, errors: &mut Errors) -> super::type_info::TypeInfo {
        todo!()
    }

    fn define_var(name: &str, var_id: super::VarId) {
        todo!()
    }
}
*/

fn const_res_to_def_id(c: ConstResult, symbols: &mut SymbolTable) -> DefId {
    match c {
        ConstResult::Val(val) => {
            DefId::Const(symbols.add_const(val))
        }
        ConstResult::Symbol(const_symbol) => match const_symbol {
            consts::ConstSymbol::Func(id) => DefId::Function(id),
            consts::ConstSymbol::Type(id) => DefId::Type(id),
            consts::ConstSymbol::TypeValue(_) => todo!(),
            consts::ConstSymbol::Trait(id) => DefId::Trait(id),
            consts::ConstSymbol::TraitFunc(id, idx) => DefId::TraitFunc(id, idx),
            consts::ConstSymbol::LocalType(_) => todo!(),
            consts::ConstSymbol::Module(id) => DefId::Module(id),
        }
    }
}


pub(super) fn local(
    defs: &DHashMap<String, Definition>, 
    scope_defs: &mut DHashMap<String, DefId>,
    parent: &Scope,
    symbols: &mut SymbolTable,
    ast: &Ast,
    errors: &mut Errors
) {
    let mut scope = UnfinishedLocalScope { defs, scope_defs, parent };
    for (name, def) in scope.defs {
        scope.cross_resolve_local(def, name, symbols, ast, errors);
    }
}

fn eval_const(mut scope: impl LocalScope, ty: &UnresolvedType, val: ExprRef, symbols: &mut SymbolTable, errors: &mut Errors) -> ConstResult {
    let mut types = TypeTable::new(0);
    let ty = scope.resolve_type_info(ty, symbols, &mut types, errors);
    // TODO: resolve constants properly
    ConstResult::Val(ConstVal::Unit)
}