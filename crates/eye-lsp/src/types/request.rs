use serde::{Deserialize, Serialize, de::DeserializeOwned};

use crate::types::{Range, TextDocumentPositionParams, WorkDoneProgressParams};

pub trait Request: DeserializeOwned {
    type Response: Serialize;
}

#[derive(Deserialize, Debug)]
pub struct HoverParams {
    #[serde(flatten)]
    position: TextDocumentPositionParams,
    #[serde(flatten)]
    work_done: WorkDoneProgressParams,
}
impl Request for HoverParams {
    type Response = Hover;
}

#[derive(Serialize)]
pub struct Hover {
    pub contents: String, // TODO: can be MarkedString/MarkupContents/...
    pub range: Option<Range>,
}
