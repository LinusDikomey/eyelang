use std::path::Path;

use serde_json::Value;

use crate::{
    ResponseError,
    lsp::{Lsp, find_in_ast},
    types::{
        notification::{DidOpenTextDocumentParams, DidSaveTextDocumentParams},
        request::{Hover, HoverParams},
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
            "textDocument/hover" => self.on_request(Self::hover, params),
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
                self.compiler.get_project(project).root.display(),
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
        match self
            .compiler
            .add_project(name.to_owned(), project_path.to_path_buf())
        {
            Ok(id) => {
                if let Some(std) = self.std {
                    self.compiler.add_dependency(id, std);
                }
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
                self.compiler.modules[module.idx()].ast = None;
            }
        }

        self.update_diagnostics();
    }

    pub fn hover(&mut self, hover: HoverParams) -> Hover {
        self.find_project_of_uri(&hover.position.textDocument.uri);
        let Some(module) = self.find_module_of_uri(&hover.position.textDocument.uri) else {
            return Hover {
                contents: "Failed to locate file for hover".to_owned(),
                range: None,
            };
        };
        let ast = self.compiler.get_module_ast(module);
        let Some(offset) = hover.position.position.to_offset(ast.src()) else {
            return Hover {
                contents: format!(
                    "invalid offset {}:{}",
                    hover.position.position.line, hover.position.position.character
                ),
                range: None,
            };
        };
        let found = find_in_ast::find(ast, offset);
        Hover {
            contents: format!("{found:?}"),
            range: None,
        }
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
