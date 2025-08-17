use std::path::{Component, PathBuf};

use compiler::{Compiler, Def, ModuleSpan, ProjectId, check::ProjectErrors};
use parser::ast::ModuleId;
use serde_json::Value;

use crate::{
    ResponseError, send_notification,
    types::{self, Diagnostic, Uri, request::Request},
};

mod find_in_ast;
mod handlers;

pub struct Lsp {
    compiler: Compiler,
    projects: Vec<ProjectId>,
    std: Option<ProjectId>,
}
impl Lsp {
    pub fn new(initialize: types::Initialize) -> Self {
        let mut compiler = Compiler::new();
        let project_path = initialize.root_uri.map_or_else(
            || initialize.root_path.as_deref().map(PathBuf::from),
            |uri| Some(uri.path().to_path_buf()),
        );
        let std = match compiler.add_project("std".to_owned(), compiler::std_path::find()) {
            Ok(std) => Some(std),
            Err(err) => {
                tracing::error!("Failed to add std library: {err:?}");
                None
            }
        };
        let project = project_path.and_then(|path| {
            let name = path.components().next_back().map_or_else(
                || "<unnamed project>".to_owned(),
                |s| s.as_os_str().to_string_lossy().into_owned(),
            );
            if !path.join("main.eye").exists() {
                return None;
            }
            compiler.add_project(name, path).ok().inspect(|&project| {
                if let Some(std) = std {
                    compiler.add_dependency(project, std);
                }
            })
        });
        let mut lsp = Self {
            compiler,
            projects: project.into_iter().collect(),
            std,
        };
        lsp.update_diagnostics();

        lsp
    }

    fn on_request<F: FnMut(&mut Self, R) -> R::Response, R: Request>(
        &mut self,
        mut handler: F,
        params: Value,
    ) -> Result<Value, ResponseError> {
        Ok(serde_json::to_value(handler(self, serde_json::from_value(params)?)).unwrap())
    }

    fn on_notification<F: FnMut(&mut Self, N), N: types::notification::Notification>(
        &mut self,
        mut handler: F,
        params: Value,
    ) -> Result<(), ResponseError> {
        handler(self, serde_json::from_value(params)?);
        Ok(())
    }

    pub fn find_project_of_uri(&self, uri: &Uri) -> Option<ProjectId> {
        let path = uri.path();
        self.projects.iter().copied().find(|&project| {
            pathdiff::diff_paths(path, &self.compiler.get_project(project).root)
                .is_some_and(|diff| !diff.components().any(|c| c == Component::ParentDir))
        })
    }

    pub fn find_module_of_uri(&mut self, uri: &Uri) -> Option<ModuleId> {
        let path = uri.path();
        self.projects.iter().copied().find_map(|project_id| {
            let project = self.compiler.get_project(project_id);
            if path == project.root {
                return Some(project.root_module);
            }
            let diff = pathdiff::diff_paths(path, &project.root)?;
            if diff.components().any(|c| c == Component::ParentDir) {
                tracing::debug!("Project at {:?} has no relative path", project.root);
                return None;
            }
            let mut module = project.root_module;
            let mut components = diff.components();
            let file_name = components.next_back()?;
            let Component::Normal(file_name) = file_name else {
                tracing::debug!("not normal");
                return None;
            };
            tracing::debug!("looking for module in project");
            let final_name = file_name.to_str()?.strip_suffix(".eye")?;
            for component in components {
                let Component::Normal(name) = component else {
                    continue;
                };
                let name = name.to_str()?;
                let Def::Module(new_module) =
                    self.compiler
                        .resolve_in_module(module, name, ModuleSpan::MISSING)
                else {
                    tracing::debug!("not a module resolved");
                    return None;
                };
                module = new_module;
            }
            Some(match final_name {
                "mod" | "main" => module,
                _ => {
                    let Def::Module(module) =
                        self.compiler
                            .resolve_in_module(module, final_name, ModuleSpan::MISSING)
                    else {
                        tracing::debug!("not a module resolvedin final");
                        return None;
                    };
                    module
                }
            })
        })
    }

    pub fn update_diagnostics(&mut self) {
        tracing::debug!("Updating diagnostics for {} projects", self.projects.len());
        for &project in &self.projects {
            self.compiler.errors = ProjectErrors::new();
            self.compiler.check_complete_project(project);
            let errors = std::mem::replace(&mut self.compiler.errors, ProjectErrors::new());
            for (module, errors) in errors.by_file {
                let src = self.compiler.get_module_ast(module).src();
                let mut diagnostics = Vec::new();
                let mut emit = |errors: &[error::CompileError], severity| {
                    for error in errors {
                        // PERF: more efficient position calculation
                        let start = error::calculate_position(src, error.span.start);
                        let end = error::calculate_position(src, error.span.end);
                        let mut message = error.err.conclusion().to_owned();
                        if let Some(details) = error.err.details() {
                            message.push('\n');
                            message.push_str(&details);
                        }
                        diagnostics.push(Diagnostic {
                            range: types::Range {
                                start: types::Position {
                                    line: start.line,
                                    character: start.column,
                                },
                                end: types::Position {
                                    line: end.line,
                                    character: end.column,
                                },
                            },
                            severity: Some(severity),
                            code: None,
                            codeDescription: None,
                            source: None,
                            message,
                        });
                    }
                };
                emit(&errors.errors, types::DiagnosticSeverity::Error);
                emit(&errors.warnings, types::DiagnosticSeverity::Warning);

                let params = types::notification::PublishDiagnosticsParams {
                    uri: Uri::from_path(&self.compiler.modules[module.idx()].path),
                    // TODO: track versions of files
                    version: None,
                    diagnostics,
                };
                send_notification(params);
            }
        }
    }
}
