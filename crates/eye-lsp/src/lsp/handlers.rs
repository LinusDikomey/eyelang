use std::{cell::OnceCell, path::Path};

use compiler::{
    Def, ModuleSpan,
    compiler::{BodyOrTypes, LocalScope, VarId},
    typing::LocalTypeId,
};
use error::span::TSpan;
use parser::ast::{Ast, ScopeId};
use serde_json::Value;

use crate::{
    ResponseError,
    lsp::{
        Lsp,
        find_in_ast::{FoundType, ScopeContext},
    },
    types::{
        Location, Range, TextEdit,
        notification::{DidOpenTextDocumentParams, DidSaveTextDocumentParams},
        request::{
            CompletionItem, CompletionItemKind, CompletionItemLabelDetails, CompletionParams,
            DefinitionParams, DocumentFormattingParams, Hover, HoverParams, MarkupContent,
            MarkupKind, Request,
        },
    },
};

impl Lsp {
    pub fn handle_notification(
        &mut self,
        method: &str,
        params: Value,
    ) -> Result<(), ResponseError> {
        match method {
            "textDocument/didOpen" => self.on_notification(Self::did_open, params),
            "textDocument/didSave" => self.on_notification(Self::did_save, params),
            _ => {
                tracing::info!("Unhandled notification: {method} {params}");
                Ok(())
            }
        }
    }

    pub fn handle_request(&mut self, method: &str, params: Value) -> Result<Value, ResponseError> {
        match method {
            HoverParams::METHOD => self.on_request(Self::hover, params),
            CompletionParams::METHOD => self.on_request(Self::complete, params),
            DefinitionParams::METHOD => self.on_request(Self::definition, params),
            DocumentFormattingParams::METHOD => self.on_request(Self::formatting, params),
            _ => {
                tracing::info!("Unhandled request {method} {params}");
                Err(ResponseError {
                    code: crate::ERROR_FAILED,
                    message: "unsupported request".to_owned(),
                    data: Value::Null,
                })
            }
        }
    }

    pub fn did_open(&mut self, open: DidOpenTextDocumentParams) {
        if let Some(project) = self.find_project_of_uri(&open.textDocument.uri) {
            tracing::info!(
                "Opened file {} is part of existing project {} at {}",
                open.textDocument.uri.path().display(),
                self.compiler.get_project(project).name,
                self.compiler
                    .get_project(project)
                    .root
                    .as_ref()
                    .unwrap()
                    .display(),
            );
            return;
        }
        let path = open.textDocument.uri.path();
        let project_path = find_project_path(path);
        let name = if project_path.is_file() {
            project_path.file_stem()
        } else {
            project_path.file_name()
        }
        .and_then(|name| name.to_str())
        .unwrap_or("unknown");
        tracing::info!(
            "Opened file {} is part of new project {name} at {}",
            path.display(),
            project_path.display()
        );
        match self.compiler.add_project(
            name.to_owned(),
            project_path.to_path_buf(),
            self.std.into_iter().collect(),
        ) {
            Ok(id) => {
                self.projects.push(id);
                self.update_diagnostics();
            }
            Err(err) => tracing::error!("Failed to add new project: {err:?}"),
        }
    }

    pub fn did_save(&mut self, save: DidSaveTextDocumentParams) {
        let Some(project) = self.find_project_of_uri(&save.textDocument.uri) else {
            tracing::warn!(
                "Got save notification for file that is not part of any project: {:?}",
                save.textDocument.uri.path().display()
            );
            return;
        };

        // find all invalidated projects
        let mut invalidated_projects = dmap::new_set();
        invalidated_projects.insert(project);

        loop {
            let mut changed = false;
            for project in self.compiler.project_ids() {
                if invalidated_projects.contains(&project) {
                    continue;
                }
                if self
                    .compiler
                    .get_project(project)
                    .dependencies
                    .iter()
                    .any(|dep| invalidated_projects.contains(dep))
                {
                    invalidated_projects.insert(project);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        for module in self.compiler.module_ids() {
            let project = self.compiler.modules[module.idx()].project;
            if invalidated_projects.contains(&project) {
                self.compiler.modules[module.idx()].ast = OnceCell::new();
            }
        }

        self.update_diagnostics();
    }

    pub fn hover(&mut self, hover: HoverParams) -> Hover {
        let Some((_module, _offset, found)) = self.find_document_position(&hover.position) else {
            return Hover {
                contents: String::new(),
                range: None,
            };
        };
        Hover {
            contents: format!("{found:?}"),
            range: None,
        }
    }

    pub fn complete(&mut self, complete: CompletionParams) -> Vec<CompletionItem> {
        tracing::info!("Handling completion");
        let Some((module, offset, found)) = self.find_document_position(&complete.position) else {
            tracing::info!("Document not found: {:?}", complete.position);
            return Vec::new();
        };
        let mut completions = Vec::new();

        let mut current = (module, found.scope);
        let mut in_prelude = false;
        loop {
            let ast = self.compiler.get_module_ast(current.0);
            let scope = &ast[current.1];
            for name in scope.definitions.keys() {
                let def =
                    self.compiler
                        .resolve_in_scope(current.0, current.1, name, ModuleSpan::MISSING);
                let kind = match def {
                    Def::Invalid => CompletionItemKind::Constant,
                    Def::Function(_, _) => CompletionItemKind::Function,
                    Def::BaseType(_) => CompletionItemKind::TypeParameter,
                    Def::Type(_) => CompletionItemKind::Struct, // there is no Type Kind onfortunately
                    Def::Trait(_, _) => CompletionItemKind::Interface,
                    Def::ConstValue(_) => CompletionItemKind::Constant,
                    Def::Module(_) => CompletionItemKind::Module,
                    Def::Global(_, _) => CompletionItemKind::Variable,
                };
                completions.push(CompletionItem {
                    label: name.to_owned(),
                    kind: Some(kind),
                    detail: None,
                    labelDetails: None,
                    documentation: None,
                });
            }

            match scope.parent {
                Some(parent) => current.1 = parent,
                None => {
                    if !in_prelude {
                        let prelude = compiler::compiler::builtins::get_prelude(&self.compiler);
                        current = (
                            prelude,
                            self.compiler.get_module_ast(prelude).top_level_scope_id(),
                        );
                        in_prelude = true;
                    } else {
                        break;
                    }
                }
            }
        }
        let context = self.find_context_for_scope(module, found.scope);
        match context {
            ScopeContext::TopLevel => completions.push(CompletionItem {
                label: format!("completion_toplevel {found:?}"),
                kind: None,
                detail: None,
                labelDetails: None,
                documentation: None,
            }),
            ScopeContext::Function(function_id) => {
                let ast = self.compiler.get_module_ast(module);
                let mut variables = Vec::new();
                let mut hooks = CompletionHooks {
                    variables: &mut variables,
                    target_offset: offset,
                    target_scope: found.scope,
                    ast,
                    done: false,
                };
                // TODO: currently this doesn't properly handle closures!
                let checked =
                    compiler::check::function(&self.compiler, module, function_id, &mut hooks);
                // TODO: remove this completion that should help with debugging
                if !hooks.done {
                    completions.push(CompletionItem {
                        label: "debug_completion_not_done".into(),
                        kind: None,
                        detail: None,
                        labelDetails: None,
                        documentation: None,
                    });
                }
                if let BodyOrTypes::Body(hir) = &checked.body_or_types {
                    let signature = self.compiler.get_signature(module, function_id);
                    for (name, variable) in variables {
                        let ty = hir[hir.vars[variable.idx()]];
                        let ty = self.compiler.types.display(ty, &signature.generics);
                        completions.push(CompletionItem {
                            label: name,
                            kind: Some(CompletionItemKind::Variable),
                            detail: None,
                            labelDetails: Some(CompletionItemLabelDetails {
                                description: Some(format!(": {ty}")),
                                detail: None,
                            }),
                            documentation: Some(MarkupContent {
                                kind: MarkupKind::Markdown,
                                value: "Documentation for completion will go here\n\nCode block test:\n```eye\nexample :: fn(x i32) {}\n```".to_string(),
                            }),
                        });
                    }
                }
            }
        }

        tracing::info!("Returning {} completions", completions.len());
        completions
    }

    pub fn definition(&mut self, params: DefinitionParams) -> Option<Location> {
        let (module, _, found) = self.find_document_position(&params.position)?;
        let (module, span) = match found.ty {
            FoundType::VarRef | FoundType::Generic => {
                let ast = self.compiler.get_module_ast(module);
                let name = &ast.src()[found.span.range()];
                match self
                    .compiler
                    .resolve_in_scope(module, found.scope, name, ModuleSpan::MISSING)
                {
                    Def::Invalid => return None,
                    Def::Function(module, function) => {
                        let ast = self.compiler.get_module_ast(module);
                        let span = ast[ast[function].scope].span;
                        (module, span)
                    }
                    Def::Module(module) => (module, TSpan::EMPTY),
                    Def::Global(module, global) => {
                        let ast = self.compiler.get_module_ast(module);
                        (module, ast[ast[global].scope].span)
                    }
                    Def::Trait(module, trait_id) => {
                        let ast = self.compiler.get_module_ast(module);
                        (module, ast[ast[trait_id].scope].span)
                    }
                    Def::BaseType(_) | Def::Type(_) | Def::ConstValue(_) => return None, // TODO
                }
            }
            _ => return None,
        };
        let ast = self.compiler.get_module_ast(module);
        let range = Range::from_span(span, ast.src());
        Some(Location {
            uri: self.uri_from_module(module),
            range,
        })
    }

    pub fn formatting(&mut self, params: DocumentFormattingParams) -> Option<Vec<TextEdit>> {
        let Ok(src) = std::fs::read_to_string(params.textDocument.uri.path()) else {
            return None;
        };
        let len = src.len().try_into().ok()?;
        let range = Range::from_span(TSpan::new(0, len), &src);
        let (formatted, errors) = format::format(src.into_boxed_str());
        if errors.error_count() > 0 {
            return None;
        }
        Some(vec![TextEdit {
            range,
            newText: formatted,
        }])
    }
}

fn find_project_path(file: &Path) -> &Path {
    let Some(mut dir) = file.parent() else {
        return file;
    };
    loop {
        if dir.join("main.eye").exists() {
            return dir;
        } else if dir.join("mod.eye").exists() {
            let Some(parent) = dir.parent() else {
                return file;
            };
            dir = parent;
        } else {
            return file;
        }
    }
}

struct CompletionHooks<'a> {
    variables: &'a mut Vec<(String, VarId)>,
    target_scope: ScopeId,
    target_offset: u32,
    ast: &'a Ast,
    done: bool,
}
impl<'a> compiler::check::Hooks for CompletionHooks<'a> {
    fn on_check_expr(
        &mut self,
        expr: parser::ast::ExprId,
        scope: &mut compiler::compiler::LocalScope,
        _expected: LocalTypeId,
        _return_ty: LocalTypeId,
        _noreturn: &mut bool,
    ) {
        if self.done || self.ast[expr].span(self.ast).start < self.target_offset {
            return;
        }
        self.complete(scope);
    }

    fn on_exit_scope(&mut self, scope: &mut compiler::compiler::LocalScope) {
        if !self.done && scope.static_scope.is_some_and(|s| s == self.target_scope) {
            self.complete(scope);
        }
    }
}
impl<'a> CompletionHooks<'a> {
    fn complete(&mut self, scope: &mut LocalScope) {
        self.done = true;
        let mut current = &*scope;
        loop {
            self.variables.extend(
                current
                    .variables
                    .iter()
                    .map(|(name, var)| (name.clone().into_string(), *var)),
            );
            match &current.parent {
                compiler::compiler::LocalScopeParent::Some(parent) => {
                    current = parent;
                }
                // TODO: handle closed over scopes for completions
                compiler::compiler::LocalScopeParent::ClosedOver { .. }
                | compiler::compiler::LocalScopeParent::None => break,
            }
        }
    }
}
