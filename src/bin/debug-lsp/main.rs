use std::fmt::Display;
use std::sync::Arc;

use calypso_base::symbol::Ident;
use color_eyre::eyre;

use tethys::ast::{AstId, Node};
use tethys::ctxt::GlobalCtxt;
use tethys::parse::Span;
use tethys::{parse, resolve};
use tokio::sync::mpsc::{self, Receiver, Sender};
use tokio::sync::{Mutex, RwLock};
use tower_lsp::jsonrpc::Result;
use tower_lsp::jsonrpc::{Error as LspError, ErrorCode};
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use tracing::{debug, trace};
use tracing_subscriber::EnvFilter;

#[derive(Debug)]
struct Backend {
    client: Client,
    file: Arc<RwLock<Option<(Url, String)>>>,
    tx: Sender<Request>,
    rx: Arc<Mutex<Receiver<Result<Response>>>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Request {
    UpdateFile,
    GetAstId(u32),
    GetActualSpan(u32),
    GetDeclarationOf(AstId),
    GetSpanOf(AstId),
    GetIdent(AstId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Response {
    Ok,
    AstId(AstId),
    Span(Span),
    Ident(Ident),
    NoDeclaration,
}

impl Response {
    pub fn expect_ast_id(self) -> AstId {
        if let Response::AstId(ast_id) = self {
            ast_id
        } else {
            panic!("expected Response::AstId")
        }
    }

    pub fn expect_declaration(self) -> Option<AstId> {
        match self {
            Response::AstId(ast_id) => Some(ast_id),
            Response::NoDeclaration => None,
            _ => panic!("expected Response::AstId or Response::NoDeclaration"),
        }
    }

    pub fn expect_ok(self) {
        if let Response::Ok = self {
        } else {
            panic!("expected Response::Ok")
        }
    }

    pub fn expect_ident(self) -> Ident {
        if let Response::Ident(ident) = self {
            ident
        } else {
            panic!("expected Response::Ident");
        }
    }

    pub fn expect_span(self) -> Span {
        if let Response::Span(span) = self {
            span
        } else {
            panic!("expected Response::Span")
        }
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                definition_provider: Some(OneOf::Left(true)),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "Tethys Debugging LSP".to_string(),
                version: None,
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "server initialized!")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let file = self.file.read().await;
        if let Some((uri, src)) = file.as_ref() {
            if uri == &params.text_document_position_params.text_document.uri {
                let offset = offset_of(params.text_document_position_params.position, src);
                self.tx.send(Request::GetAstId(offset)).await.unwrap();
                let ast_id = self.rx.lock().await.recv().await.unwrap()?.expect_ast_id();
                self.tx
                    .send(Request::GetDeclarationOf(ast_id))
                    .await
                    .unwrap();
                let decl_ast_id = self
                    .rx
                    .lock()
                    .await
                    .recv()
                    .await
                    .unwrap()?
                    .expect_declaration();
                if decl_ast_id.is_none() {
                    return Ok(None);
                }
                self.tx
                    .send(Request::GetIdent(decl_ast_id.unwrap()))
                    .await
                    .unwrap();
                let ident = self.rx.lock().await.recv().await.unwrap()?.expect_ident();

                Ok(Some(GotoDefinitionResponse::Scalar(Location {
                    uri: uri.clone(),
                    range: range_of(ident.span.into(), src),
                })))
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let file = self.file.read().await;
        if let Some((uri, src)) = file.as_ref() {
            if uri == &params.text_document_position_params.text_document.uri {
                let offset = offset_of(params.text_document_position_params.position, src);
                self.tx.send(Request::GetAstId(offset)).await.unwrap();
                let ast_id = self.rx.lock().await.recv().await.unwrap()?.expect_ast_id();
                self.tx.send(Request::GetActualSpan(offset)).await.unwrap();
                let span = self.rx.lock().await.recv().await.unwrap()?.expect_span();

                Ok(Some(Hover {
                    contents: HoverContents::Scalar(MarkedString::String(format!(
                        "AST ID: {:?}",
                        ast_id
                    ))),
                    range: Some(range_of(span, src)),
                }))
            } else {
                Ok(Some(Hover {
                    contents: HoverContents::Scalar(MarkedString::String(
                        "No content available".to_string(),
                    )),
                    range: None,
                }))
            }
        } else {
            Ok(Some(Hover {
                contents: HoverContents::Scalar(MarkedString::String(
                    "No content available".to_string(),
                )),
                range: None,
            }))
        }
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let mut file = self.file.write().await;
        match file.take() {
            Some((uri, content)) => {
                if uri == params.text_document.uri {
                    *file = Some((uri, params.text_document.text));
                    drop(file);
                    self.tx.send(Request::UpdateFile).await.unwrap();
                    self.rx
                        .lock()
                        .await
                        .recv()
                        .await
                        .unwrap()
                        .unwrap()
                        .expect_ok();
                } else {
                    *file = Some((uri, content))
                }
            }
            None => {
                *file = Some((params.text_document.uri, params.text_document.text));
                drop(file);
                self.tx.send(Request::UpdateFile).await.unwrap();
                self.rx
                    .lock()
                    .await
                    .recv()
                    .await
                    .unwrap()
                    .unwrap()
                    .expect_ok();
            }
        }
    }
}

fn offset_of(pos: Position, src: &str) -> u32 {
    let mut cur_col = 0;
    let mut cur_line = 0;
    for (offset, ch) in src.char_indices() {
        if cur_line == pos.line && cur_col == pos.character {
            return offset.try_into().unwrap();
        }

        if ch == '\n' {
            cur_line += 1;
            cur_col = 0;
        } else {
            cur_col += 1;
        }
    }
    0
}

fn position_of(offset: u32, src: &str) -> Position {
    let mut cur_col = 0;
    let mut cur_line = 0;
    assert!(src.is_char_boundary(offset as usize));
    for (cur_offset, ch) in src.char_indices() {
        if cur_offset == offset as usize {
            return Position {
                line: cur_line,
                character: cur_col,
            };
        }

        if ch == '\n' {
            cur_line += 1;
            cur_col = 0;
        } else {
            cur_col += 1;
        }
    }
    if offset >= src.len() as u32 {
        return Position {
            line: cur_line,
            character: cur_col,
        };
    }
    Position {
        line: 0,
        character: 0,
    }
}

fn range_of(span: Span, src: &str) -> Range {
    Range {
        start: position_of(span.lo(), src),
        end: position_of(span.hi(), src),
    }
}

#[tokio::main]
async fn main() -> eyre::Result<()> {
    tracing_subscriber::fmt::fmt()
        .with_env_filter(EnvFilter::new("tower_lsp=trace,debug_lsp=trace"))
        .with_writer(std::io::stderr)
        .with_ansi(false)
        .init();
    color_eyre::install()?;

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (txreq, rxreq) = mpsc::channel(16);
    let (txres, rxres) = mpsc::channel(16);
    let file = Arc::new(RwLock::new(None));
    let file_worker = Arc::clone(&file);
    std::thread::spawn(|| worker_thread(file_worker, rxreq, txres));

    let (service, socket) = LspService::new(|client| Backend {
        client,
        file,
        tx: txreq,
        rx: Arc::new(Mutex::new(rxres)),
    });
    Server::new(stdin, stdout, socket).serve(service).await;

    Ok(())
}

fn worker_thread(
    file: Arc<RwLock<Option<(Url, String)>>>,
    mut rx: Receiver<Request>,
    tx: Sender<Result<Response>>,
) {
    let gcx = GlobalCtxt::new();
    let mut items = Vec::new();
    while let Some(req) = rx.blocking_recv() {
        match req {
            Request::UpdateFile => {
                items.clear();
                gcx.clear();
                let file_guard = file.blocking_read();
                let (url, src) = file_guard.as_ref().unwrap();
                items = parse::run(src.as_ref(), &gcx);
                match resolve::resolve_code_unit(&gcx, &items) {
                    Err(err) => tx.blocking_send(Err(stringify_error(err))).unwrap(),
                    Ok(_) => tx.blocking_send(Ok(Response::Ok)).unwrap(),
                }
                trace!("UpdateFile({}): done", url);
            }
            Request::GetAstId(offset) => match get_node(&gcx, offset) {
                Some(node) => {
                    let id = node.id(&gcx);
                    debug!("GetAstId({:?}): {:?}", offset, id);
                    tx.blocking_send(Ok(Response::AstId(id))).unwrap();
                }
                None => {
                    debug!("GetAstId({:?}): none found", offset);
                    tx.blocking_send(Err(stringify_error(
                        "Failed to find a node containing the given offset",
                    )))
                    .unwrap()
                }
            },
            Request::GetActualSpan(offset) => match get_node(&gcx, offset) {
                Some(node) => {
                    let span = node.span(&gcx);
                    debug!("GetActualSpan({:?}): {:?}", offset, span);
                    tx.blocking_send(Ok(Response::Span(span))).unwrap();
                }
                None => {
                    debug!("GetActualSpan({:?}): none found", offset);
                    tx.blocking_send(Err(stringify_error(
                        "Failed to find a node containing the given offset",
                    )))
                    .unwrap()
                }
            },
            Request::GetDeclarationOf(ast_id) => {
                if let Some(res) = gcx.arenas.ast.res_data.borrow().get_by_id(ast_id) {
                    let id = res.id();
                    if let Some(id) = id {
                        debug!("GetDeclarationOf({:?}: {:?}", ast_id, id);
                        tx.blocking_send(Ok(Response::AstId(id))).unwrap();
                    } else {
                        debug!(
                            "GetDeclarationOf({:?}): declaration found ({:?}), but it didn't have an id",
                            ast_id, id
                        );
                        tx.blocking_send(Ok(Response::NoDeclaration)).unwrap();
                    }
                } else {
                    debug!("GetDeclarationOf({:?}): none found", ast_id);
                    tx.blocking_send(Ok(Response::NoDeclaration)).unwrap();
                }
            }
            Request::GetSpanOf(ast_id) => {
                if let Some(node) = gcx.arenas.ast.get_node_by_id(ast_id) {
                    let span = node.span(&gcx);
                    debug!("GetSpanOf({:?}): {:?}", ast_id, span);
                    tx.blocking_send(Ok(Response::Span(span))).unwrap();
                } else {
                    debug!("GetSpanOf({:?}): none found", ast_id);
                    tx.blocking_send(Err(stringify_error(
                        "Failed to find a node by the given AST ID",
                    )))
                    .unwrap();
                }
            }
            Request::GetIdent(ast_id) => {
                if let Some(node) = gcx.arenas.ast.get_node_by_id(ast_id) {
                    let ident = node.ident(&gcx);
                    debug!("GetSymbol({:?}): {:?}", ast_id, ident);
                    let res = match ident {
                        Some(ident) => Ok(Response::Ident(ident)),
                        None => Err(stringify_error(
                            "Failed to find a symbol for the given AST ID",
                        )),
                    };
                    tx.blocking_send(res).unwrap();
                } else {
                    debug!("GetSpanOf({:?}): none found", ast_id);
                    tx.blocking_send(Err(stringify_error(
                        "Failed to find a node by the given AST ID",
                    )))
                    .unwrap();
                }
            }
        }
    }
}

/// Find the node with the smallest span that includes a given binary offset.
fn get_node(gcx: &GlobalCtxt, offset: u32) -> Option<Node> {
    gcx.arenas
        .ast
        .into_iter_nodes()
        .filter(|node| {
            let span = node.span(gcx);

            span.lo() <= offset && offset <= span.hi()
        })
        .min_by_key(|node| node.span(gcx).len())
}

fn stringify_error<E: Display>(e: E) -> LspError {
    LspError {
        code: ErrorCode::ServerError(0),
        data: None,
        message: e.to_string(),
    }
}
