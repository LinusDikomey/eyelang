use std::path::PathBuf;

use compiler::{Compiler, ProjectId};
use serde_json::Value;

use crate::{
    ERROR_FAILED, Notification, ResponseError,
    types::{self, Hover},
};

pub struct Lsp {
    compiler: Compiler,
    project: Option<ProjectId>,
}
impl Lsp {
    pub fn new(initialize: types::Initialize) -> Self {
        let mut compiler = Compiler::new();
        let project_path = initialize.root_uri.map_or_else(
            || initialize.root_path.as_deref().map(PathBuf::from),
            |uri| Some(PathBuf::from(uri.path())),
        );
        let project = project_path.and_then(|path| {
            let name = path.components().next_back().map_or_else(
                || "<unnamed project>".to_owned(),
                |s| s.as_os_str().to_string_lossy().into_owned(),
            );
            compiler.add_project(name, path.join("main.eye")).ok()
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
            compiler: Compiler::new(),
            project,
        }
    }

    pub fn handle_notification(&mut self, _notification: Notification) {}

    pub fn handle_request(&mut self, method: &str, _params: Value) -> Result<Value, ResponseError> {
        Ok(match method {
            "textDocument/hover" => serde_json::to_value(self.handle_hover()).unwrap(),
            _ => {
                return Err(ResponseError {
                    code: ERROR_FAILED,
                    message: "unsupported request".to_owned(),
                    data: Value::Null,
                });
            }
        })
    }

    fn handle_hover(&mut self) -> Hover {
        Hover {
            contents: "This is a hover text".to_owned(),
            range: None,
        }
    }
}
