use serde::{Deserialize, Serialize, de::DeserializeOwned};
use serde_repr::{Deserialize_repr, Serialize_repr};

use crate::types::{Location, Range, TextDocumentPositionParams, WorkDoneProgressParams};

pub trait Request: DeserializeOwned {
    const METHOD: &'static str;
    type Response: Serialize;
}

#[derive(Deserialize, Debug)]
pub struct HoverParams {
    #[serde(flatten)]
    pub position: TextDocumentPositionParams,
    #[serde(flatten)]
    pub work_done: WorkDoneProgressParams,
}
impl Request for HoverParams {
    const METHOD: &'static str = "textDocument/hover";
    type Response = Hover;
}

#[derive(Serialize)]
pub struct Hover {
    pub contents: String, // TODO: can be MarkedString/MarkupContents/...
    pub range: Option<Range>,
}

#[derive(Deserialize)]
pub struct CompletionParams {
    #[serde(flatten)]
    pub position: TextDocumentPositionParams,
    #[serde(flatten)]
    pub work_done: WorkDoneProgressParams,
    // PartialResultParams
    pub context: Option<CompletionContext>,
}
impl Request for CompletionParams {
    const METHOD: &'static str = "textDocument/completion";
    type Response = Vec<CompletionItem>;
}

#[derive(Deserialize)]
pub struct CompletionContext {
    pub triggerKind: CompletionTriggerKind,
    pub triggerCharacter: Option<String>,
}

#[derive(Deserialize_repr)]
#[repr(u8)]
pub enum CompletionTriggerKind {
    Invoked = 1,
    TriggerCharacter = 2,
    TriggerForIncompleteCompletions = 3,
}

#[derive(Serialize)]
pub struct CompletionItem {
    pub label: String,
    pub kind: Option<CompletionItemKind>,
}

#[derive(Serialize_repr)]
#[repr(u8)]
pub enum CompletionItemKind {
    Text = 1,
    Method = 2,
    Function = 3,
    Constructor = 4,
    Field = 5,
    Variable = 6,
    Class = 7,
    Interface = 8,
    Module = 9,
    Property = 10,
    Unit = 11,
    Value = 12,
    Enum = 13,
    Keyword = 14,
    Snippet = 15,
    Color = 16,
    File = 17,
    Reference = 18,
    Folder = 19,
    EnumMember = 20,
    Constant = 21,
    Struct = 22,
    Event = 23,
    Operator = 24,
    TypeParameter = 25,
}

#[derive(Deserialize)]
pub struct DefinitionParams {
    #[serde(flatten)]
    pub position: TextDocumentPositionParams,
    // WorkDoneProgressParams, PartialResultParams
}
impl Request for DefinitionParams {
    const METHOD: &'static str = "textDocument/definition";
    type Response = Option<Location>;
}
