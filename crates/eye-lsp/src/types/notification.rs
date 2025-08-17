use serde::{Deserialize, Serialize, de::DeserializeOwned};

use crate::types::{Diagnostic, DocumentUri, Integer, TextDocumentIdentifier, TextDocumentItem};

pub trait Notification: DeserializeOwned {}
pub trait ServerNotification: Serialize {
    const METHOD: &'static str;
}

#[derive(Deserialize)]
pub struct DidOpenTextDocumentParams {
    pub textDocument: TextDocumentItem,
}
impl Notification for DidOpenTextDocumentParams {}

#[derive(Deserialize)]
pub struct DidSaveTextDocumentParams {
    pub textDocument: TextDocumentIdentifier,
    pub text: Option<String>,
}
impl Notification for DidSaveTextDocumentParams {}

#[derive(Serialize)]
pub struct PublishDiagnosticsParams {
    pub uri: DocumentUri,
    pub version: Option<Integer>,
    pub diagnostics: Vec<Diagnostic>,
}
impl ServerNotification for PublishDiagnosticsParams {
    const METHOD: &'static str = "textDocument/publishDiagnostics";
}
