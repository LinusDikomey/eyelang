use parser::ast::{
    Ast, Definition, Expr, ExprId, IdentPath, ScopeId, Token, TokenType, UnresolvedType,
};

use crate::dom::{Cond, Node, R};

type Cst = Ast<Token>;

pub fn module(cst: &Cst) -> Node {
    let mut nodes = Vec::new();
    let mut converter = Converter { cst, pos: 0 };
    converter.scope_contents(&mut nodes, cst.top_level_scope_id());
    converter.emit_whitespace(&mut nodes, &cst.src()[converter.pos as usize..]);
    Node::Group(nodes, R::Width(0))
}

struct Converter<'a> {
    cst: &'a Cst,
    pos: u32,
}

impl<'a> Converter<'a> {
    fn tok(&mut self, nodes: &mut Vec<Node>, token: Token) {
        self.tok_with_char(nodes, token, None);
    }

    fn tok_s(&mut self, nodes: &mut Vec<Node>, token: Token) {
        self.tok_with_char(nodes, token, Some(' '));
    }

    fn tok_with_char(&mut self, nodes: &mut Vec<Node>, token: Token, c: Option<char>) {
        let ws = &self.cst.src()[self.pos as usize..token.start as usize];
        debug_assert!(self.pos <= token.start);
        debug_assert!(token.start <= token.end);
        self.pos = token.end;
        self.emit_whitespace(nodes, ws);
        let mut text = self.cst.src()[token.start as usize..token.end as usize].to_owned();
        if let Some(c) = c {
            text.push(c);
        }
        nodes.push(Node::Text(text.into()));
    }

    #[must_use]
    fn ty(&mut self, ty: &UnresolvedType) -> Node {
        // TODO: types currently don't preserve comments, they will probably get merged into the
        // expr grammar anyways
        let mut s = String::new();
        ty.to_string(&mut s, self.cst.src());
        Node::Text(s.into_boxed_str())
    }

    fn scope_contents(&mut self, nodes: &mut Vec<Node>, scope: ScopeId) {
        let scope = &self.cst[scope];
        let mut defs: Vec<_> = scope.definitions.values().collect();
        // sort the items by their order of appearence so it is preserved
        defs.sort_by_key(|&def| match def {
            Definition::Expr { t_name, .. } => t_name.start,
            Definition::Use { t_use, .. } => t_use.start,
            &Definition::Global(global_id) => self.cst[global_id].t_name.start,
            Definition::Module(_) | Definition::Generic(_) => 0,
        });
        for item in defs {
            match item {
                &Definition::Expr {
                    t_name,
                    t_colon_colon,
                    id,
                } => {
                    let (expr, ty) = &self.cst[id];
                    self.tok_s(nodes, t_name);
                    match t_colon_colon {
                        parser::ast::Either::A(t) => self.tok_s(nodes, t),
                        parser::ast::Either::B((a, b)) => {
                            self.tok(nodes, a);
                            nodes.push(self.ty(ty));
                            self.tok_s(nodes, b);
                        }
                    }
                    self.expr(nodes, *expr);
                }
                &Definition::Use { t_use, path } => {
                    self.tok_s(nodes, t_use);
                    self.path(nodes, path);
                }
                Definition::Global(_global_id) => todo!(),
                Definition::Module(_) | Definition::Generic(_) => {}
            }
        }
    }

    fn path(&mut self, nodes: &mut Vec<Node>, path: IdentPath) {
        let s = &self.cst.src()[path.span().range()];
        // TODO: format paths
        nodes.push(Node::Text(s.into()));
    }

    fn expr(&mut self, nodes: &mut Vec<Node>, id: ExprId) {
        #[allow(unused_variables)] // FIXME: remove when all branches implemented
        match &self.cst[id] {
            Expr::Error(span) => {
                nodes.push(Node::Text(self.cst.src()[span.range()].into()));
            }
            &Expr::Block {
                t_open,
                scope,
                items,
                t_close,
            } => {
                let mut block_nodes = Vec::new();
                self.tok(&mut block_nodes, t_open);
                let mut content_nodes = Vec::new();
                self.scope_contents(&mut content_nodes, scope);
                let mut first = true;
                for item in items {
                    if !first || content_nodes.is_empty() {
                        content_nodes.push(Node::Text("\n".into()));
                    }
                    first = false;
                    self.expr(&mut content_nodes, item);
                }
                let empty = content_nodes.is_empty();
                block_nodes.push(Node::Indent(Box::new(Node::Group(
                    content_nodes,
                    R::Width(0),
                ))));
                if !empty {
                    block_nodes.push(Node::Text("\n".into()));
                }
                self.tok(&mut block_nodes, t_close);
                nodes.push(Node::Group(block_nodes, R::Width(0)));
            }
            &Expr::Nested {
                span,
                t_lparen,
                inner,
                t_rparen,
            } => {
                self.tok(nodes, t_lparen);
                self.expr(nodes, inner);
                self.tok(nodes, t_rparen);
            }
            Expr::IntLiteral { t, .. }
            | Expr::FloatLiteral { t, .. }
            | Expr::StringLiteral { t, .. }
            | Expr::Ident { t, .. } => self.tok(nodes, *t),
            &Expr::Array {
                t_lbracket,
                elements,
                t_rbracket,
                ..
            } => {
                let mut group = Vec::new();
                self.tok(&mut group, t_lbracket);
                let mut content = Vec::new();
                let mut first = true;
                content.push(Node::TextIf(Cond::Broken, "\n".into()));
                for elem in elements {
                    // TODO: not handling the comma as a token here so comments may get lost
                    if !first {
                        content.push(Node::Text(",".into()));
                        content.push(Node::TextIf(Cond::Flat, " ".into()));
                        content.push(Node::TextIf(Cond::Broken, "\n".into()));
                    }
                    first = false;
                    self.expr(&mut content, elem);
                }
                content.push(Node::TextIf(
                    Cond::Broken,
                    if !first { ",\n" } else { "\n" }.into(),
                ));
                group.push(Node::Indent(Box::new(Node::Group(content, R::Width(0)))));
                self.tok(&mut group, t_rbracket);
                nodes.push(Node::Group(group, R::Width(0)));
            }
            &Expr::Function { id } => self.function(nodes, id),
            Expr::DeclareWithVal {
                pat,
                t_colon_and_equals_or_colon_equals,
                annotated_ty,
                val,
            } => {
                self.expr(nodes, *pat);
                nodes.push(Node::Text(" ".into()));
                match *t_colon_and_equals_or_colon_equals {
                    parser::ast::Either::A((colon, equals)) => {
                        self.tok_s(nodes, colon);
                        nodes.push(self.ty(annotated_ty));
                        self.tok_s(nodes, equals);
                    }
                    parser::ast::Either::B(colon_equals) => {
                        self.tok_s(nodes, colon_equals);
                    }
                }
                self.expr(nodes, *val);
            }
            &Expr::BinOp { t_op, op: _, l, r } => {
                self.expr(nodes, l);
                nodes.push(Node::Text(" ".into()));
                self.tok_s(nodes, t_op);
                self.expr(nodes, r);
            }
            &Expr::Return { start, t_ret, val } => {
                self.tok_s(nodes, t_ret);
                self.expr(nodes, val);
            }
            expr => {
                // emit a fake token for now so that formatting can be tested before all Exprs
                // are implemented
                self.tok_s(
                    nodes,
                    Token {
                        start: expr.start(self.cst),
                        end: expr.end(self.cst),
                        new_line: false,
                        ty: TokenType::Eof,
                    },
                );
            }
        }
    }

    fn emit_whitespace(&self, nodes: &mut Vec<Node>, ws: &str) {
        let mut chars = ws.char_indices().peekable();
        enum State {
            WS,
            Single,
            Multi(u32),
        }
        let mut state = State::WS;
        let mut comment_start = 0;
        let mut newline_count = 0;
        loop {
            let Some((pos, c)) = chars.next() else {
                break;
            };
            match c {
                '#' if chars.next_if(|(_, c)| *c == '-').is_some() => match &mut state {
                    State::WS => {
                        if newline_count != 0 {
                            nodes.push(Node::Text("\n".repeat(newline_count).into_boxed_str()));
                            newline_count = 0;
                        }
                        state = State::Multi(1);
                        comment_start = pos;
                    }
                    State::Single => {}
                    State::Multi(n) => *n += 1,
                },
                '#' if matches!(state, State::WS) => {
                    if newline_count != 0 {
                        nodes.push(Node::Text("\n".repeat(newline_count).into_boxed_str()));
                        newline_count = 0;
                    }
                    state = State::Single;
                    comment_start = pos;
                }
                '-' if chars.next_if(|(_, c)| *c == '#').is_some() => match &mut state {
                    State::WS => panic!("Invalid closing multi-line comment in whitespace"),
                    State::Single => {}
                    State::Multi(n) => {
                        *n -= 1;
                        if *n == 0 {
                            nodes.push(Node::Text(ws[comment_start..pos + 2].into()));
                            state = State::WS;
                        }
                    }
                },
                '\n' => match state {
                    State::WS => newline_count += 1,
                    State::Single => {
                        nodes.push(Node::Text(ws[comment_start..pos + 1].into()));
                        state = State::WS;
                    }
                    State::Multi(_) => {}
                },
                _ => {}
            }
        }
        if newline_count != 0 {
            nodes.push(Node::Text("\n".repeat(newline_count).into_boxed_str()));
        }
    }

    fn function(&mut self, nodes: &mut Vec<Node>, id: parser::ast::FunctionId) {
        let function = &self.cst[id];
        // TODO: generics
        let mut group = Vec::new();
        if let Some((l, r)) = function.t_parens {
            self.tok(&mut group, function.t_fn);
            self.tok(&mut group, l);
            let mut args = Vec::new();
            let mut first = true;
            args.push(Node::TextIf(Cond::Broken, "\n".into()));
            for (name_span, ty) in &function.params {
                if !first {
                    args.push(Node::TextIf(Cond::Flat, ", ".into()));
                }
                first = false;
                // HACK: really tokens just need to be spans
                self.tok_s(
                    &mut args,
                    Token {
                        start: name_span.start,
                        end: name_span.end,
                        ty: TokenType::Ident,
                        new_line: false,
                    },
                );
                args.push(self.ty(ty));
                args.push(Node::TextIf(Cond::Broken, "\n".into()));
            }
            if let Some(t) = function.t_varargs {
                if !function.params.is_empty() {
                    args.push(Node::TextIf(Cond::Flat, ", ".into()));
                }
                self.tok(nodes, t);
            }
            group.push(Node::Indent(Box::new(Node::Group(args, R::Width(0)))));
            self.tok_s(&mut group, r);
        } else {
            self.tok_s(&mut group, function.t_fn);
        }
        if let Some(arrow) = function.t_arrow {
            self.tok_s(&mut group, arrow);
            group.push(self.ty(&function.return_type));
            group.push(Node::Text(" ".into()));
        }

        if let Some(t_extern) = function.t_extern {
            self.tok(&mut group, t_extern);
        }
        if let Some(t_colon) = function.t_colon {
            self.tok_s(&mut group, t_colon);
        } else {
            group.push(Node::Text(" ".into()));
        }

        if let Some(body) = function.body {
            self.expr(&mut group, body);
        }

        nodes.push(Node::Group(group, R::Width(0)));
        nodes.push(Node::Text("\n".into()));
    }
}
