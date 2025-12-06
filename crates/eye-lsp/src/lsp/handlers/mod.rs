mod complete;
mod hover;

use std::{cell::OnceCell, path::Path};

use compiler::{Def, ModuleSpan};
use error::span::TSpan;
use serde_json::Value;

use crate::{
    ResponseError,
    lsp::{Lsp, find_in_ast::FoundType},
    types::{
        Location, Range, TextEdit,
        notification::{DidOpenTextDocumentParams, DidSaveTextDocumentParams},
        request::{
            CompletionParams, DefinitionParams, DocumentFormattingParams, HoverParams, Request,
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

    pub fn definition(&mut self, params: DefinitionParams) -> Option<Location> {
        let (module, _, found) = self.find_document_position(&params.position)?;
        let (module, span) = match found.ty {
            FoundType::Ident | FoundType::Generic => {
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
