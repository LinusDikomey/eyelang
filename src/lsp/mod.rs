use crossbeam::channel::Sender;
use lsp_server::{ProtocolError, Request, Response};
use lsp_types::{
    ServerCapabilities,
    HoverProviderCapability,
    TextDocumentSyncKind,
    CompletionOptions,
    TextDocumentSyncCapability,
    notification::{Notification, DidSaveTextDocument},
};
use std::{io::Write, path::Path};
use crate::Args;

use self::dispatch::{RequestDispatcher, NotificationDispatcher};

mod dispatch;
mod handlers;
mod validate;

pub struct State {
    sender: Sender<lsp_server::Message>,
}

#[derive(Debug)]
pub enum LspError {
    Protocol(ProtocolError),
    SerdeJson(serde_json::Error),
    Recv(crossbeam::channel::RecvError),
    Send(crossbeam::channel::SendError<lsp_server::Message>),
    InvalidPath
}
impl From<ProtocolError> for LspError {
    fn from(e: ProtocolError) -> Self {
        Self::Protocol(e)
    }
}
impl From<serde_json::Error> for LspError {
    fn from(e: serde_json::Error) -> Self {
        Self::SerdeJson(e)
    }
}
impl From<crossbeam::channel::RecvError> for LspError {
    fn from(e: crossbeam::channel::RecvError) -> Self {
        Self::Recv(e)
    }
}
impl From<crossbeam::channel::SendError<lsp_server::Message>> for LspError {
    fn from(e: crossbeam::channel::SendError<lsp_server::Message>) -> Self {
        Self::Send(e)
    }
}

pub fn lsp(_args: &Args) -> Result<(), LspError> {
    debug("launching");

    let (connection, _io_threads) = lsp_server::Connection::stdio();

    let (initialize_id, initialize_params) = connection.initialize_start()?;

    debug(format!("init: {}", initialize_params));

    let _initialize_params: lsp_types::InitializeParams = serde_json::from_value(initialize_params)?;
    
    let initialize_result = lsp_types::InitializeResult {
        capabilities: ServerCapabilities {
            text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::INCREMENTAL)),
            completion_provider: Some(CompletionOptions {
                resolve_provider: Some(true),
                ..Default::default()
            }),
            hover_provider: Some(HoverProviderCapability::Simple(true)),
            ..Default::default()
        },
        server_info: Some(lsp_types::ServerInfo {
            name: String::from("eye-analyzer"),
            version: Some("0.0.1".to_owned()),
        }),
    };

    connection.initialize_finish(initialize_id, serde_json::to_value(initialize_result)?)?;
    
    debug("init finished, ready for commands");

    loop {
        let mut state = State { sender: connection.sender.clone() };
        match connection.receiver.recv()? {
            lsp_server::Message::Request(req) => match state.on_request(req) {
                Ok(()) | Err(Ok(())) => {},
                Err(Err(e)) => debug(format!("Error occured: {:?}", e))
            }
            lsp_server::Message::Response(resp) => state.complete(resp),
            lsp_server::Message::Notification(not) => {
                match not.method.as_str() {
                    lsp_types::notification::Exit::METHOD => {
                        break Ok(());
                    }
                    _ => match state.on_notification(not) {
                        Ok(()) | Err(Ok(())) => {}
                        Err(Err(e)) => debug(format!("Error occurred: {:?}", e))
                    }
                }
            }
        }
    }
}

impl State {
    fn on_request(&mut self, req: Request) -> Result<(), Result<(), LspError>> {
        debug(format!("req: {}", req.method));

        RequestDispatcher { req, state: self }
            .on::<lsp_types::request::HoverRequest>(handlers::handle_hover)?
            ;

        Ok(())
    }

    fn on_notification(&mut self, not: lsp_server::Notification) -> Result<(), Result<(), LspError>> {
        debug(format!("Notification: {}", not.method));
        NotificationDispatcher { not, state: self }
            .on::<DidSaveTextDocument>(
                |state, p| validate::start_checking(p.text_document.uri, state.sender.clone())
            )?
            .on::<lsp_types::notification::DidOpenTextDocument>(
                |state, p| validate::start_checking(p.text_document.uri, state.sender.clone())
            )?
            .on::<lsp_types::notification::DidCloseTextDocument>(
                |_state, _p| { Ok(()) /* TODO: remove from parsed document map */}
            )?
            ;

        Ok(())
    }

    fn complete(&mut self, resp: Response) {
        debug(format!("completed: {:?}", resp))
    }
}

pub fn debug<S: AsRef<str>>(s: S) {
    let mut f = std::fs::File::options()
        .append(true)
        .create(true)
        .open(Path::join(std::env::current_exe().unwrap().parent().unwrap(), "log.txt"))
        .expect("Failed to open");
    writeln!(f, "{}", s.as_ref()).unwrap();
}