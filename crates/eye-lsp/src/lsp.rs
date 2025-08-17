use std::path::PathBuf;

use compiler::{Compiler, ProjectId, check::ProjectErrors};
use serde_json::Value;

use crate::{
    ResponseError, send_notification,
    types::{self, Diagnostic, Uri, request::Request},
};

mod handlers;

pub struct Lsp {
    compiler: Compiler,
    projects: Vec<ProjectId>,
}
impl Lsp {
    pub fn new(initialize: types::Initialize) -> Self {
        let mut compiler = Compiler::new();
        let project_path = initialize.root_uri.map_or_else(
            || initialize.root_path.as_deref().map(PathBuf::from),
            |uri| Some(uri.path().to_path_buf()),
        );
        let project = project_path.and_then(|path| {
            let name = path.components().next_back().map_or_else(
                || "<unnamed project>".to_owned(),
                |s| s.as_os_str().to_string_lossy().into_owned(),
            );
            if !path.join("main.eye").exists() {
                return None;
            }
            compiler.add_project(name, path).ok()
        });
        let std_path = std::env::current_exe()
            .ok()
            .and_then(|path| path.parent().map(|path| path.join("std/")))
            .and_then(|std_path| {
                std_path
                    .try_exists()
                    .is_ok_and(|exists| exists)
                    .then_some(std_path)
            })
            .unwrap_or(PathBuf::from("std/"));
        _ = compiler.add_project("std".to_owned(), std_path.join("main.eye"));
        Self {
            compiler,
            projects: project.into_iter().collect(),
        }
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
            pathdiff::diff_paths(path, &self.compiler.get_project(project).root).is_some_and(
                |diff| {
                    !diff
                        .components()
                        .any(|c| c == std::path::Component::ParentDir)
                },
            )
        })
    }

    pub fn update_diagnostics(&mut self) {
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
