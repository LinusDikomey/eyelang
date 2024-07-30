use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct Uri(String);
impl Uri {
    pub fn path(&self) -> &str {
        self.0.strip_prefix("file://").unwrap_or(&self.0)
    }
}
type DocumentUri = Uri;

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
    #[serde(rename = "positionEncoding")]
    pub position_encoding: String,
    #[serde(rename = "hoverProvider")]
    pub hover_provider: bool,
    // ...
}

#[derive(Serialize)]
pub struct ServerInfo {
    pub name: String,
    pub version: Option<String>,
}

#[derive(Serialize)]
pub struct Hover {
    pub contents: String, // TODO: can be MarkedString/MarkupContents/...
    pub range: Option<Range>,
}

#[derive(Serialize, Deserialize)]
pub struct Range {
    pub start: Position,
    pub end: Position,
}

#[derive(Serialize, Deserialize)]
pub struct Position {
    pub line: u64,
    pub character: u64,
}

#[derive(Serialize)]
pub struct Diagnostic {
    pub range: Range,
    pub severity: Option<DiagnosticSeverity>,
    pub code: Option<String>,
    #[serde(rename = "codeDescription")]
    pub code_description: Option<CodeDescription>,
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

pub struct PublishDiagnosticsParams {
    pub uri: DocumentUri,

    /**
     * Optional the version number of the document the diagnostics are published
     * for.
     *
     * @since 3.15.0
     */
    pub version: Option<i32>,

    pub diagnostics: Vec<Diagnostic>,
}
