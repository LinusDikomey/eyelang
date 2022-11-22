use crate::{ast::{ModuleId, Ast, Definition}, span::TSpan, error::{Errors, Error}, dmap::DHashMap};

use super::{scope::Scope, types::DefId};



pub(super) fn top_level(module_scopes: &mut [Scope<'static>], ast: &Ast, errors: &mut Errors) {
    for i in 0..module_scopes.len() {
        let module = ModuleId::new(i as u32);
        for (name, def) in &ast[ast[module].definitions] {
            cross_resolve_top_level(name, def, module, module_scopes, ast, errors);
        }
    }
}

fn cross_resolve_top_level_by_name(
    name: &str,
    span: TSpan,
    module: ModuleId,
    scopes: &mut [Scope<'static>],
    ast: &Ast,
    errors: &mut Errors,
) -> DefId {

    let Some(def) = ast[ast[module].definitions].get(name) else {
        errors.emit_span(Error::UnknownIdent, span.in_mod(module));
        return DefId::Invalid;
    };
    cross_resolve_top_level(name, def, module, scopes, ast, errors)
}

fn cross_resolve_top_level(
    def_name: &str,
    def: &Definition,
    module: ModuleId,
    scopes: &mut [Scope<'static>],
    ast: &Ast,
    errors: &mut Errors
) -> DefId {

    match scopes[module.idx()].names.get_mut(def_name).unwrap() {
        DefId::Unresolved { resolving } => {
            if *resolving {
                let span = match def {
                    Definition::Use(path) => path.span(),
                    Definition::Const(_, expr) => ast[*expr].span(ast),
                    _ => unreachable!()
                };
                errors.emit_span(Error::RecursiveDefinition, span.in_mod(module));
                return DefId::Invalid;
            }
            *resolving = true;

            let def_id = match def {
                Definition::Use(path) => {
                    let (root, segments, last) = path.segments(ast.src(module).0);
                    
                    let mut cur_mod = if root.is_some() {
                        scopes[module.idx()].module.root
                    } else {
                        module
                    };

                    for (name, name_span) in segments {
                        match cross_resolve_top_level_by_name(name, name_span, cur_mod, scopes, ast, errors) {
                            DefId::Module(id) => cur_mod = id,
                            DefId::Invalid => {
                                *scopes[module.idx()].names.get_mut(def_name).unwrap() = DefId::Invalid;
                                return DefId::Invalid
                            }
                            _ => {
                                *scopes[module.idx()].names.get_mut(def_name).unwrap() = DefId::Invalid;
                                errors.emit_span(Error::ModuleExpected, name_span.in_mod(module));
                                return DefId::Invalid
                            }
                        }
                    }

                    if let Some((last_name, last_span)) = last {
                        cross_resolve_top_level_by_name(last_name, last_span, cur_mod, scopes, ast, errors)
                    } else {
                        DefId::Module(cur_mod)
                    }
                }
                Definition::Const(_, _) => todo!(),
                _ => unreachable!()
            };
            *scopes[module.idx()].names.get_mut(def_name).unwrap() = def_id;
            def_id
        }
        other => *other
    }
}


pub(super) fn local(defs: &DHashMap<String, Definition>, scope_defs: &mut DHashMap<String, DefId>, parent: &Scope, ast: &Ast, errors: &mut Errors) {
    for (name, def) in defs {
        cross_resolve_local(def, name, defs, scope_defs, parent, ast, errors);
    }
}

fn cross_resolve_local_by_name(
    name: &str,
    name_span: TSpan,
    defs: &DHashMap<String, Definition>,
    scope_defs: &mut DHashMap<String, DefId>,
    parent: &Scope,
    ast: &Ast,
    errors: &mut Errors
) -> DefId {
    let Some(def) = defs.get(name) else {
        return parent.resolve(name, name_span.in_mod(parent.module.id), errors);
    };
    cross_resolve_local(def, name, defs, scope_defs, parent, ast, errors)
}

fn cross_resolve_local(
    def: &Definition,
    name: &str,
    defs: &DHashMap<String, Definition>,
    scope_defs: &mut DHashMap<String, DefId>,
    parent: &Scope,
    ast: &Ast,
    errors: &mut Errors
) -> DefId {
    match scope_defs.get(name).unwrap() {
        DefId::Unresolved { resolving } => {
            if *resolving {
                let span = match def {
                    Definition::Use(path) => path.span(),
                    Definition::Const(_, expr) => ast[*expr].span(ast),
                    _ => unreachable!()
                };
                errors.emit_span(Error::RecursiveDefinition, span.in_mod(parent.module.id));
                return DefId::Invalid;
            }
            
            let def_id = match def {
                Definition::Use(path) => {
                    let (root, segments, last) = path.segments(ast.src(parent.module.id).0);
                    if root.is_some() {
                        parent.resolve_path(path, errors)
                    } else {
                        let mut current_module = None;
                        for (name, name_span) in segments {
                            let next_mod = if let Some(current) = current_module {
                                parent.module_scope(current).resolve(name, name_span.in_mod(parent.module.id), errors)
                            } else {
                                cross_resolve_local_by_name(name, name_span, defs, scope_defs, parent, ast, errors)
                            };
                            match next_mod {
                                DefId::Module(id) => current_module = Some(id),
                                DefId::Invalid => {
                                    *scope_defs.get_mut(name).unwrap() = DefId::Invalid;
                                    return DefId::Invalid;
                                }
                                _ => {
                                    errors.emit_span(Error::ModuleExpected, name_span.in_mod(parent.module.id));
                                    *scope_defs.get_mut(name).unwrap() = DefId::Invalid;
                                    return DefId::Invalid;
                                }
                            }
                        }

                        if let Some((last_name, name_span)) = last {
                            if let Some(module) = current_module {
                                parent.module_scope(module)
                                    .resolve(last_name, name_span.in_mod(parent.module.id), errors)
                            } else {
                                cross_resolve_local_by_name(last_name, name_span, defs, scope_defs, parent, ast, errors)
                            }
                        } else {
                            DefId::Module(current_module.unwrap())
                        }
                    }
                }
                Definition::Const(_, _) => todo!(),
                _ => unreachable!()
            };

            *scope_defs.get_mut(name).unwrap() = def_id;
            def_id
        }
        other => *other
    }
}