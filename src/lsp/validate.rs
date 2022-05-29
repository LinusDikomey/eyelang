use std::time::Instant;

use crossbeam::channel::Sender;
use lsp_server::{Message, Notification};
use lsp_types::{PublishDiagnosticsParams, Position};
use lsp_types::{Diagnostic, DiagnosticSeverity, notification::PublishDiagnostics};
use lsp_types::notification::Notification as _;

use super::{LspError, debug};

pub fn start_checking(uri: lsp_types::Url, sender: Sender<Message>) -> Result<(), LspError> {
    std::thread::spawn(|| {
        let now = Instant::now();
        let res = std::panic::catch_unwind(|| {
            if let Err(err) = check(uri, sender) {
                debug(format!("Error while validating: {err:?}"));
            }
        });
        if let Err(err) = res {
            debug(format!("Validation panicked: {err:?}"));
        }
        debug(format!("Validation took {:?}", now.elapsed()))
    });
    Ok(())
}

fn calc_range(span: crate::lexer::Span, ast: &crate::ast::Ast) -> lsp_types::Range {
    let (src, _) = ast.src(span.module);
    let mut line = 0;
    let mut line_char = 0;
    for c in (&src[0..span.start as usize]).chars() {
        match c {
            '\n' => {
                line += 1;
                line_char = 0;
            }
            _ => line_char += 1
        }
    }
    let mut end_line = line;
    let mut end_line_char = line_char;
    for c in (&src[span.start as usize ..= span.end as usize]).chars() {
        match c {
            '\n' => {
                end_line += 1;
                end_line_char = 0;
            }
            _ => end_line_char += 1
        }
    }
    lsp_types::Range::new(Position::new(line, line_char), Position::new(end_line, end_line_char))
}

fn check(uri: lsp_types::Url, sender: Sender<Message>) -> Result<(), LspError> {
    let path = uri.to_file_path().map_err(|_| LspError::InvalidPath)?;
    debug(format!("validation path: {path:?}"));
    let diagnostics = match crate::compile::project(&path, false, true, &[], true, &mut crate::Stats::default()) {
        Ok(_) => {
            Vec::new()
        }
        Err((modules, errors)) => {
            errors.get().iter().map(|error| {
                Diagnostic {
                    severity: Some(DiagnosticSeverity::ERROR),
                    message: error.err.to_string(),
                    range: calc_range(error.span, &modules),
                    
                    ..Default::default()
                }
            }).collect::<Vec<Diagnostic>>()
        }
    };
    send_diagnostics(uri, sender, diagnostics)?;
    Ok(())
}

fn send_diagnostics(uri: lsp_types::Url, sender: Sender<Message>, diagnostics: Vec<Diagnostic>)
-> Result<(), LspError> {
    debug(format!("Sending {} diagnostics", diagnostics.len()));
    sender.send(Message::Notification(Notification {
        method: PublishDiagnostics::METHOD.to_owned(),
        params: serde_json::to_value(PublishDiagnosticsParams {
            uri,
            diagnostics,
            version: None
        })?
    }))?;
    Ok(())
}