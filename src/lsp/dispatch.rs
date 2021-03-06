use lsp_server::Response;
use serde::{de::DeserializeOwned, Serialize};

use super::{State, LspError};


pub struct RequestDispatcher<'a> {
    pub req: lsp_server::Request,
    pub state: &'a mut State
}

impl<'a> RequestDispatcher<'a> {
    pub fn on<R>(
        self,
        f: fn(&mut State, R::Params) -> Result<R::Result, LspError>,
    ) -> Result<Self, Result<(), LspError>>
    where
        R: lsp_types::request::Request + 'static,
        R::Params: DeserializeOwned + Send + std::fmt::Debug + 'static,
        R::Result: Serialize + 'static,
    {
        if self.req.method == R::METHOD {
            let r: R::Params = serde_json::from_value(self.req.params).map_err(|e| Err(e.into()))?;
            match f(self.state, r) {
                Ok(resp) => {
                    let resp = Response::new_ok(self.req.id, resp);
                    self.state.sender.send(lsp_server::Message::Response(resp)).map_err(|e| Err(e.into()))?;
                }
                Err(e) => return Err(Err(e))
            }
            Err(Ok(()))
        } else {
            Ok(self)
        }
    }
}

pub struct NotificationDispatcher<'a> {
    pub not: lsp_server::Notification,
    pub state: &'a mut State
}
impl<'a> NotificationDispatcher<'a> {
    pub fn on<N>(
        self,
        f: fn(&mut State, N::Params) -> Result<(), LspError>
    ) -> Result<Self, Result<(), LspError>>
    where
        N: lsp_types::notification::Notification + 'static,
        N::Params: DeserializeOwned + Send + std::fmt::Debug + 'static,
    {
        if self.not.method == N::METHOD {
            let n: N::Params = serde_json::from_value(self.not.params).map_err(|e| Err(e.into()))?;
            Err(f(self.state, n))
        } else {
            Ok(self)
        }
    }
}