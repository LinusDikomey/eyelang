use lsp_types::{HoverParams, MarkupContent};

use super::{State, LspError};


pub fn handle_hover(_state: &mut State, _params: HoverParams) -> Result<Option<lsp_types::Hover>, LspError> {
    Ok(Some(lsp_types::Hover {
        contents: lsp_types::HoverContents::Markup(MarkupContent {
            kind: lsp_types::MarkupKind::Markdown,
            value: "Markus Söder in Town".to_owned()
        }),
        range: None
    }))
}
