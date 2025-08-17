#![allow(non_snake_case, dead_code)]

pub mod notification;
pub mod request;

use std::path::Path;

use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
pub struct Uri(String);
impl Uri {
    pub fn from_path(path: &Path) -> Self {
        Self(format!(
            "file://{}",
            path.canonicalize().unwrap().to_string_lossy()
        ))
    }
    pub fn path(&self) -> &Path {
        Path::new(self.0.strip_prefix("file://").unwrap_or(&self.0))
    }
}
type DocumentUri = Uri;
type Integer = i32;

#[derive(Debug, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Id {
    Number(i32),
    String(String),
}

#[derive(Deserialize)]
pub struct Initialize {
    #[serde(rename = "processId")]
    pub process_id: Option<i32>,
    #[serde(rename = "rootPath")]
    pub root_path: Option<String>,
    #[serde(rename = "rootUri")]
    pub root_uri: Option<DocumentUri>,
}

#[derive(Serialize)]
pub struct InitializeResult {
    pub capabilities: ServerCapabilities,
    #[serde(rename = "serverInfo")]
    pub server_info: ServerInfo,
}

#[derive(Serialize)]
pub struct ServerCapabilities {
    pub positionEncoding: String,
    pub hoverProvider: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub textDocumentSync: Option<TextDocumentSyncOptions>,
    // ...
}

#[derive(Serialize)]
pub struct TextDocumentSyncOptions {
    pub openClose: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub change: Option<TextDocumentSyncKind>,
    pub save: bool,
}

#[derive(serde_repr::Serialize_repr)]
#[repr(i32)]
pub enum TextDocumentSyncKind {
    None = 0,
    Full = 1,
    Incremental = 2,
}

#[derive(Serialize)]
pub struct ServerInfo {
    pub name: String,
    pub version: Option<String>,
}

#[derive(Serialize, Deserialize)]
pub struct Range {
    pub start: Position,
    pub end: Position,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Position {
    pub line: u32,
    pub character: u32,
}
impl Position {
    pub fn to_offset(&self, mut src: &str) -> Option<u32> {
        let mut offset = 0;
        for _ in 0..self.line {
            let i = src.find('\n')? + 1;
            offset += i as u32;
            src = &src[i..];
        }
        let mut chars = src.chars();
        for _ in 0..self.character {
            let c = chars.next()?;
            if c == '\n' {
                return None;
            }
            offset += c.len_utf8() as u32;
        }

        Some(offset)
    }
}

#[derive(Deserialize, Debug)]
pub struct TextDocumentPositionParams {
    pub textDocument: TextDocumentIdentifier,
    pub position: Position,
}

#[derive(Serialize, Deserialize)]
pub struct TextDocumentItem {
    pub uri: DocumentUri,
    pub languageId: String,
    pub version: Integer,
    pub text: String,
}

#[derive(Deserialize, Debug)]
pub struct WorkDoneProgressParams {
    workDoneToken: Option<ProgressToken>,
}

#[derive(Deserialize, Debug)]
#[serde(untagged)]
pub enum ProgressToken {
    String(String),
    Int(i32),
}

#[derive(Deserialize, Debug)]
pub struct TextDocumentIdentifier {
    pub uri: DocumentUri,
}

#[derive(Serialize)]
pub struct Diagnostic {
    pub range: Range,
    pub severity: Option<DiagnosticSeverity>,
    pub code: Option<String>,
    pub codeDescription: Option<CodeDescription>,
    pub source: Option<String>,
    pub message: String,
    // ...
}

#[derive(Debug, Clone, Copy)]
pub enum DiagnosticSeverity {
    Error = 1,
    Warning = 2,
    Information = 3,
    Hint = 4,
}
impl Serialize for DiagnosticSeverity {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_i32(*self as i32)
    }
}

#[derive(Serialize)]
pub struct CodeDescription {
    pub href: Uri,
}
