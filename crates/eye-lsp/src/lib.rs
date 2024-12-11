#![allow(unused)]

mod lsp;
mod types;

use std::io::{BufRead, Read, Write};

use lsp::Lsp;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use types::Id;

#[derive(Debug)]
pub enum LspError {
    IO(std::io::Error),
}
impl From<std::io::Error> for LspError {
    fn from(value: std::io::Error) -> Self {
        Self::IO(value)
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Message<'a> {
    jsonrpc: &'a str,
    #[serde(flatten)]
    message: MessageType<'a>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(untagged)]
enum MessageType<'a> {
    #[serde(borrow)]
    Request(Request<'a>),
    #[serde(borrow)]
    Notification(Notification<'a>),
    Response(Response),
}

#[derive(Debug, Serialize, Deserialize)]
struct Request<'a> {
    id: Id,
    method: &'a str,
    params: Value,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(untagged)]
enum Response {
    Ok { id: Id, result: Value },
    Err { id: Id, error: ResponseError },
}

#[derive(Debug, Serialize, Deserialize)]
struct Notification<'a> {
    method: &'a str,
    params: Value,
}

#[derive(Debug, Serialize, Deserialize)]
struct ResponseError {
    code: i64,
    message: String,
    data: Value,
}

const ERROR_FAILED: i64 = -32803;
const ERROR_SERVER_NOT_INITIALIZED: i64 = -32002;
const ERROR_INVALID_REQUEST: i64 = -32600;

#[allow(clippy::large_enum_variant)]
enum State {
    Ready,
    Running { lsp: Lsp },
    Shutdown,
}

fn log(s: String) {
    eprintln!("{s}");
    let mut f = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(home::home_dir().unwrap().join("eye-lsp.txt"))
        .unwrap();

    f.write_all(s.as_bytes()).unwrap();
    f.write_all("\n".as_bytes()).unwrap();
}

pub fn run() -> Result<(), LspError> {
    let mut state = State::Ready;
    log(format!(
        "Starting lsp in {}",
        std::env::current_dir().unwrap().display()
    ));
    let mut stdin = std::io::stdin().lock();
    let mut buf = String::new();
    let mut content_buf = Vec::new();
    loop {
        buf.clear();
        stdin.read_line(&mut buf)?;
        buf.make_ascii_lowercase();
        let Some(len): Option<usize> = buf
            .strip_prefix("content-length: ")
            .and_then(|s| s.strip_suffix("\r\n"))
            .and_then(|s| s.parse().ok())
        else {
            log("invalid content-length header".to_owned());
            continue;
        };
        buf.clear();
        stdin.read_line(&mut buf)?;
        if buf != "\r\n" {
            log("invalid line after content-length header".to_owned());
            continue;
        }
        log(format!("reading a request of length {len}"));
        content_buf.clear();
        content_buf.resize(len, 0);
        stdin.read_exact(&mut content_buf)?;
        let message: Message = match serde_json::from_slice(&content_buf) {
            Ok(request) => request,
            Err(err) => {
                log(format!(
                    "invalid request: {err:?}, request is: {}",
                    String::from_utf8_lossy(&content_buf)
                ));
                continue;
            }
        };
        match &mut state {
            State::Ready => match message.message {
                MessageType::Request(request) if request.method == "initialize" => {
                    match serde_json::from_value::<types::Initialize>(request.params) {
                        Ok(initialize) => {
                            state = State::Running {
                                lsp: Lsp::new(initialize),
                            };
                            send_response(
                                request.id,
                                &types::InitializeResult {
                                    capabilities: types::ServerCapabilities {
                                        position_encoding: "utf-8".to_owned(),
                                        hover_provider: true,
                                    },
                                    server_info: types::ServerInfo {
                                        name: "eye-lsp".to_owned(),
                                        version: Some(env!("CARGO_PKG_VERSION").to_owned()),
                                    },
                                },
                            );
                        }
                        Err(err) => {
                            log(format!("invalid initialize request received: {err:?}"));
                            send_err_response(
                                request.id,
                                ERROR_INVALID_REQUEST,
                                format!("invalid initialize request: {err:?}"),
                            );
                        }
                    }
                }
                MessageType::Request(request) => send_err_response(
                    request.id,
                    ERROR_SERVER_NOT_INITIALIZED,
                    "the lsp is not initialized yet".to_owned(),
                ),
                _ => {}
            },
            State::Running { lsp } => match message.message {
                MessageType::Request(request) if request.method == "shutdown" => {
                    state = State::Shutdown;
                }
                MessageType::Request(request) => {
                    let response = match lsp.handle_request(request.method, request.params) {
                        Ok(result) => Response::Ok {
                            id: request.id,
                            result,
                        },
                        Err(error) => Response::Err {
                            id: request.id,
                            error,
                        },
                    };
                    send(
                        serde_json::to_string(&Message {
                            jsonrpc: "2.0",
                            message: MessageType::Response(response),
                        })
                        .unwrap(),
                    )
                }
                MessageType::Notification(notification) => lsp.handle_notification(notification),
                MessageType::Response(_) => {}
            },
            State::Shutdown => match message.message {
                MessageType::Notification(notification) if notification.method == "exit" => {
                    std::process::exit(0);
                }
                MessageType::Request(request) => send_err_response(
                    request.id,
                    ERROR_INVALID_REQUEST,
                    "server was shutdown".to_owned(),
                ),
                _ => {}
            },
        }
    }
}

fn send_response<T: Serialize>(id: Id, result: &T) {
    let result = serde_json::to_value(result).unwrap();
    let s = serde_json::to_string(&Message {
        jsonrpc: "2.0",
        message: MessageType::Response(Response::Ok { id, result }),
    })
    .unwrap();
    send(s);
}

fn send_err_response(id: Id, code: i64, message: String) {
    send(
        serde_json::to_string(&Message {
            jsonrpc: "2.0",
            message: MessageType::Response(Response::Err {
                id,
                error: ResponseError {
                    code,
                    message,
                    data: Value::Null,
                },
            }),
        })
        .unwrap(),
    );
}

fn send(s: String) {
    print!("Content-Length: {}\r\n\r\n{s}\n", s.len())
}
