pub mod ast;
mod lexer;
mod reader;
pub mod token;

use dmap::DHashMap;
pub use reader::ExpectedTokens;

use id::ModuleId;

use span::{IdentPath, Span, TSpan};
use token::Token;
use types::{Primitive, UnresolvedType};

use crate::{
    error::{CompileError, Error, Errors},
    parser::{ast::EnumVariantDefinition, reader::match_or_unexpected},
};

use self::{
    ast::{
        Definition, Expr, ExprId, Function, GenericDef, Global, Item, ScopeId, TraitDefinition,
        UnOp,
    },
    reader::{match_or_unexpected_value, Delimit},
    token::{Keyword, Operator, TokenType},
};

pub fn parse(
    source: String,
    errors: &mut Errors,
    module: ModuleId,
    definitions: DHashMap<String, Definition>,
) -> ast::Ast {
    let tokens = lexer::lex(&source, errors, module);
    let mut ast_builder = ast::AstBuilder::new();
    let mut parser = Parser {
        src: &source,
        ast: &mut ast_builder,
        toks: reader::TokenReader::new(tokens, module),
    };

    match parser.parse_module(definitions) {
        Ok(scope) => ast_builder.finish_with_top_level_scope(source, scope),
        Err(err) => {
            errors.emit_err(err);
            let scope = ast_builder.scope(ast::Scope {
                parent: None,
                definitions: dmap::new(),
                span: TSpan::new(0, source.len() as _),
            });
            ast_builder.finish_with_top_level_scope(source, scope)
        }
    }
}

type ParseResult<T> = Result<T, CompileError>;

struct Parser<'a> {
    src: &'a str,
    ast: &'a mut ast::AstBuilder,
    toks: reader::TokenReader,
}

impl<'a> Parser<'a> {
    /// Parses a delimited list. The `item` function parses an item and is supposed to handle the result itself.
    /// `delim` is a delimiter. Trailing delimiters are allowed, but optional here.
    /// `end` is the ending token. It will be returned from this function once parsed.
    fn parse_delimited<F, D>(
        &mut self,
        delim: TokenType,
        end: TokenType,
        mut item: F,
    ) -> ParseResult<Token>
    where
        F: FnMut(&mut Parser) -> Result<D, CompileError>,
        D: Into<Delimit>,
    {
        loop {
            if let Some(end_tok) = self.toks.step_if(end) {
                return Ok(end_tok);
            }
            let delimit = item(self)?.into();
            match delimit {
                Delimit::Yes => {
                    let delim_or_end = self.toks.step()?;
                    if delim_or_end.ty == delim {
                        continue;
                    }
                    if delim_or_end.ty == end {
                        return Ok(delim_or_end);
                    }
                    return Err(Error::UnexpectedToken {
                        expected: ExpectedTokens::AnyOf(vec![delim, end]),
                        found: delim_or_end.ty,
                    }
                    .at_span(delim_or_end.span().in_mod(self.toks.module)));
                }
                Delimit::No => {}
                Delimit::Optional => {
                    self.toks.step_if(delim);
                }
                Delimit::OptionalIfNewLine => {
                    if self.toks.step_if(delim).is_none() {
                        if let Some(after) = self.toks.peek() {
                            if !after.new_line && after.ty != end {
                                return Err(Error::UnexpectedToken {
                                    expected: ExpectedTokens::AnyOf(vec![delim, end]),
                                    found: after.ty,
                                }
                                .at_span(after.span().in_mod(self.toks.module)));
                            }
                        }
                    }
                }
            }
        }
    }

    fn parse_module(&mut self, module_defs: DHashMap<String, Definition>) -> ParseResult<ScopeId> {
        debug_assert!(
            self.toks.previous().is_none(),
            "parsing module not from start, start position wrong",
        );
        self.parse_items_until(
            0,
            None,
            module_defs,
            |p| p.toks.is_at_end(),
            Self::on_module_level_expr,
        )
    }

    fn parse_items_until(
        &mut self,
        start: u32,
        parent: Option<ScopeId>,
        definitions: DHashMap<String, Definition>,
        mut end: impl FnMut(&mut Self) -> bool,
        mut on_expr: impl FnMut(&mut Self, &mut ast::Scope, ScopeId, Expr, Span) -> ParseResult<()>,
    ) -> ParseResult<ScopeId> {
        let scope_id = self.ast.scope(ast::Scope::missing());
        let mut scope = ast::Scope {
            parent,
            definitions,
            span: TSpan::MISSING, // span will be updated at the end of this function
        };

        while !end(self) {
            let start = self.toks.current().unwrap().start;

            match self.parse_item(scope_id)? {
                Item::Definition {
                    name,
                    name_span,
                    annotated_ty,
                    value,
                } => {
                    if let &Expr::Function { id } = self.ast.get_expr(value) {
                        // this is a bit hacky but fine for now
                        self.ast.assign_function_name(id, name_span);
                    }
                    let prev = scope.definitions.insert(
                        name,
                        Definition::Expr {
                            value,
                            ty: annotated_ty,
                        },
                    );
                    if let Some(_) = prev {
                        return Err(Error::DuplicateDefinition.at(
                            name_span.start,
                            name_span.end,
                            self.toks.module,
                        ));
                    }
                }
                Item::Use(path) => {
                    let (_, _, name) = path.segments(self.src);
                    let name = name.map_or("root", |(name, _)| name).to_owned();
                    scope.definitions.insert(name, Definition::Path(path));
                }
                Item::Expr(r) => {
                    let span = Span {
                        start,
                        end: self.toks.current_end_pos(),
                        module: self.toks.module,
                    };
                    on_expr(self, &mut scope, scope_id, r, span)?;
                }
            };
        }
        let end = self.toks.current_end_pos();
        scope.span = TSpan::new(start, end);
        *self.ast.get_scope_mut(scope_id) = scope;
        Ok(scope_id)
    }

    fn on_module_level_expr(
        &mut self,
        scope: &mut ast::Scope,
        scope_id: ScopeId,
        expr: Expr,
        span: Span,
    ) -> ParseResult<()> {
        let expr = self.ast.expr(expr);
        let mut add_global = |s: &mut Parser,
                              pat: ExprId,
                              annotated_ty: UnresolvedType,
                              val: Option<ExprId>|
         -> ParseResult<()> {
            let start = s.ast.get_expr(expr).span_builder(s.ast).start;
            let end = if let Some(val) = val {
                s.ast.get_expr(val).span_builder(s.ast).end
            } else {
                annotated_ty.span().end
            };
            let name = match s.ast.get_expr(pat) {
                Expr::Ident { span } => Ok(*span),
                expr => Err(Error::InvalidGlobalVarPattern
                    .at_span(expr.span_builder(s.ast).in_mod(s.toks.module))),
            }?;
            let name = s.src[name.range()].to_owned();
            let id = s.ast.global(Global {
                name: name.clone().into_boxed_str(),
                scope: scope_id,
                ty: annotated_ty,
                val,
                span: TSpan::new(start, end),
            });
            scope.definitions.insert(name, Definition::Global(id));
            Ok(())
        };
        match self.ast.get_expr(expr) {
            Expr::Declare { pat, annotated_ty } => {
                add_global(self, *pat, annotated_ty.clone(), None)?;
            }
            Expr::DeclareWithVal {
                pat,
                annotated_ty,
                val,
            } => {
                add_global(self, *pat, annotated_ty.clone(), Some(*val))?;
            }
            _ => {
                return Err(CompileError {
                    err: Error::InvalidTopLevelBlockItem,
                    span,
                })
            }
        };
        Ok(())
    }

    fn parse_block_or_expr(&mut self, scope: ScopeId) -> ParseResult<Expr> {
        match_or_unexpected!(
            self.toks.peek()
                .ok_or_else(|| Error::UnexpectedEndOfFile.at(
                    self.toks.last_src_pos(),
                    self.toks.last_src_pos(),
                    self.toks.module
                ))?,
            self.toks.module,
            TokenType::LBrace = TokenType::LBrace => self.parse_block(scope),
            TokenType::Colon = TokenType::Colon => {
                self.toks.step_expect(TokenType::Colon)?;
                self.parse_expr(scope)
            }
        )
    }

    fn parse_block(&mut self, parent: ScopeId) -> ParseResult<Expr> {
        let lbrace = self.toks.step_expect(TokenType::LBrace)?;
        self.parse_block_from_lbrace(lbrace, parent)
    }

    fn parse_block_from_lbrace(&mut self, lbrace: Token, parent: ScopeId) -> ParseResult<Expr> {
        debug_assert_eq!(lbrace.ty, TokenType::LBrace);
        let mut items = Vec::new();

        let mut end = u32::MAX;

        let scope = self.parse_items_until(
            lbrace.start,
            Some(parent),
            dmap::new(),
            |p| {
                p.toks
                    .step_if(TokenType::RBrace)
                    .inspect(|rbrace| end = rbrace.end)
                    .is_some()
            },
            |_, _, _, expr, _| {
                items.push(expr);
                Ok(())
            },
        )?;

        debug_assert_ne!(end, u32::MAX);

        let items = self.ast.exprs(items);
        Ok(Expr::Block { scope, items })
    }

    fn parse_item(&mut self, scope: ScopeId) -> Result<Item, CompileError> {
        let cur = self.toks.current()?;
        Ok(match cur.ty {
            // use statement
            TokenType::Keyword(Keyword::Use) => {
                self.toks.step_assert(TokenType::Keyword(Keyword::Use));
                let path = self.parse_path()?;
                Item::Use(path)
            }
            // either a variable or constant definition or just an identifier
            TokenType::Ident => {
                let ident = self.toks.step_assert(TokenType::Ident);
                let ident_span = ident.span();
                let name = ident.get_val(self.src);
                match self.toks.peek().map(|t| t.ty) {
                    // constant definition
                    Some(TokenType::DoubleColon) => {
                        let double_colon = self.toks.step_assert(TokenType::DoubleColon);
                        let value = self.parse_expr(scope)?;
                        let value = self.ast.expr(value);
                        Item::Definition {
                            name: name.to_owned(),
                            name_span: ident_span,
                            annotated_ty: UnresolvedType::Infer(double_colon.span()),
                            value,
                        }
                    }
                    // Variable or constant declaration with explicit type
                    Some(TokenType::Colon) => {
                        self.toks.step_assert(TokenType::Colon);
                        let annotated_ty = self.parse_type()?;
                        if self.toks.step_if(TokenType::Equals).is_some() {
                            // typed variable with initial value
                            let pat = self.ast.expr(Expr::Ident { span: ident_span });
                            let val = self.parse_expr(scope)?;
                            let val = self.ast.expr(val);
                            Item::Expr(Expr::DeclareWithVal {
                                pat,
                                annotated_ty,
                                val,
                            })
                        } else if self.toks.step_if(TokenType::Colon).is_some() {
                            // typed constant
                            let value = self.parse_expr(scope)?;
                            Item::Definition {
                                name: name.to_owned(),
                                name_span: ident_span,
                                annotated_ty,
                                value: self.ast.expr(value),
                            }
                        } else {
                            // typed variable without initial value
                            let pat = self.ast.expr(Expr::Ident { span: ident_span });
                            Item::Expr(Expr::Declare { pat, annotated_ty })
                        }
                    }
                    // Variable declaration with inferred type
                    Some(TokenType::Declare) => {
                        let decl = self.toks.step_assert(TokenType::Declare);
                        let pat = self.ast.expr(Expr::Ident { span: ident_span });
                        let val = self.parse_expr(scope)?;

                        Item::Expr(Expr::DeclareWithVal {
                            pat,
                            annotated_ty: UnresolvedType::Infer(decl.span()),
                            val: self.ast.expr(val),
                        })
                    }
                    _ => {
                        let var = Expr::Ident { span: ident_span };
                        let expr = self.parse_stmt_starting_with(var, scope)?;
                        Item::Expr(expr)
                    }
                }
            }
            _ => Item::Expr(self.parse_stmt(scope)?),
        })
    }

    fn parse_function_def(
        &mut self,
        fn_tok: Token,
        scope: ScopeId,
        associated_name: TSpan,
        inherited_generics: Vec<GenericDef>,
    ) -> ParseResult<Function> {
        let mut func =
            self.parse_function_header(fn_tok, scope, associated_name, inherited_generics)?;
        if let Some(body) = self.parse_function_body(func.scope)? {
            self.attach_func_body(&mut func, body)
        }
        Ok(func)
    }

    fn attach_func_body(&mut self, func: &mut Function, body: ExprId) {
        func.body = Some(body);
        let new_end = self.ast.get_expr(body).span_builder(&self.ast).end;
        self.ast.get_scope_mut(func.scope).span.end = new_end;
    }

    fn struct_definition(
        &mut self,
        struct_tok: Token,
        scope: ScopeId,
    ) -> ParseResult<ast::StructDefinition> {
        debug_assert_eq!(struct_tok.ty, TokenType::Keyword(Keyword::Struct));
        let generics = self.parse_optional_generics(Vec::new())?;

        let scope = {
            let scope = ast::Scope::from_generics(scope, self.src, &generics, TSpan::MISSING);
            self.ast.scope(scope)
        };

        self.toks.step_expect(TokenType::LBrace)?;

        let mut members: Vec<(TSpan, UnresolvedType)> = Vec::new();
        let mut methods = dmap::new();
        let rbrace = self.parse_delimited(TokenType::Comma, TokenType::RBrace, |p| {
            let ident = p.toks.step_expect(TokenType::Ident)?;
            if p.toks.step_if(TokenType::DoubleColon).is_some() {
                let fn_tok = p.toks.step_expect(TokenType::Keyword(Keyword::Fn))?;
                let method =
                    p.parse_function_def(fn_tok, scope, ident.span(), generics.to_vec())?;
                let func_id = p.ast.function(method);
                let name = ident.get_val(p.src).to_owned();
                if let Some(_existing) = methods.insert(name, func_id) {
                    return Err(CompileError::new(
                        Error::DuplicateDefinition,
                        ident.span().in_mod(p.toks.module),
                    ));
                }
                Ok(Delimit::No)
            } else {
                let member_span = ident.span();
                let member_type = p.parse_type()?;
                members.push((member_span, member_type));
                Ok(Delimit::OptionalIfNewLine)
            }
        })?;
        self.ast.get_scope_mut(scope).span = TSpan::new(struct_tok.start, rbrace.end);
        Ok(ast::StructDefinition {
            generics,
            scope,
            members,
            methods,
        })
    }

    fn enum_definition(
        &mut self,
        enum_tok: Token,
        scope: ScopeId,
    ) -> ParseResult<ast::EnumDefinition> {
        debug_assert_eq!(enum_tok.ty, TokenType::Keyword(Keyword::Enum));
        let generics = self.parse_optional_generics(Vec::new())?;

        let scope = {
            let scope = ast::Scope::from_generics(scope, self.src, &generics, TSpan::MISSING);
            self.ast.scope(scope)
        };

        self.toks.step_expect(TokenType::LBrace)?;
        let mut variants = Vec::new();
        let mut methods = dmap::new();

        let rbrace = self.parse_delimited(TokenType::Comma, TokenType::RBrace, |p| {
            let ident = p.toks.step_expect(TokenType::Ident)?;
            match p.toks.peek().map(|t| t.ty) {
                Some(TokenType::LParen) => {
                    p.toks.step_assert(TokenType::LParen);
                    let name_span = ident.span();
                    let mut args = vec![];
                    let end = p
                        .parse_delimited(TokenType::Comma, TokenType::RParen, |p| {
                            p.parse_type().map(|ty| args.push(ty))
                        })?
                        .end;
                    variants.push(EnumVariantDefinition {
                        name_span,
                        args: args.into_boxed_slice(),
                        end,
                    });
                    Ok(Delimit::OptionalIfNewLine)
                }
                Some(TokenType::DoubleColon) => {
                    p.toks.step_assert(TokenType::DoubleColon);

                    let fn_tok = p.toks.step_expect(TokenType::Keyword(Keyword::Fn))?;
                    let method =
                        p.parse_function_def(fn_tok, scope, ident.span(), generics.to_vec())?;
                    let func_id = p.ast.function(method);
                    let name = ident.get_val(p.src).to_owned();
                    if let Some(_existing) = methods.insert(name, func_id) {
                        return Err(CompileError::new(
                            Error::DuplicateDefinition,
                            ident.span().in_mod(p.toks.module),
                        ));
                    }
                    Ok(Delimit::No)
                }
                _ => {
                    // enum variant without arguments
                    let name_span = ident.span();
                    variants.push(EnumVariantDefinition {
                        name_span,
                        args: Box::new([]),
                        end: name_span.end,
                    });
                    Ok(Delimit::OptionalIfNewLine)
                }
            }
        })?;

        self.ast.get_scope_mut(scope).span = TSpan::new(enum_tok.start, rbrace.end);

        Ok(ast::EnumDefinition {
            generics,
            scope,
            variants: variants.into_boxed_slice(),
            methods,
        })
    }

    /// Will just return a function with the body always set to `None`
    fn parse_function_header(
        &mut self,
        fn_tok: Token,
        scope: ScopeId,
        associated_name: TSpan,
        inherited_generics: Vec<GenericDef>,
    ) -> ParseResult<Function> {
        debug_assert_eq!(fn_tok.ty, TokenType::Keyword(Keyword::Fn));
        let start = fn_tok.start;
        let mut end = fn_tok.end;
        let generics = self.parse_optional_generics(inherited_generics)?;

        let mut params = Vec::new();
        let mut varargs = false;

        if self.toks.step_if(TokenType::LParen).is_some() {
            let rparen = self.parse_delimited(TokenType::Comma, TokenType::RParen, |p| {
                if varargs {
                    let tok = p.toks.step()?;
                    // no further tokens after varargs are allowed
                    return Err(Error::UnexpectedToken {
                        expected: ExpectedTokens::Specific(TokenType::RParen),
                        found: tok.ty,
                    }
                    .at(tok.start, tok.end, p.toks.module));
                }
                if p.toks.step_if(TokenType::TripleDot).is_some() {
                    varargs = true;
                } else {
                    let name_tok = p.toks.step_expect(TokenType::Ident)?;
                    let name_span = TSpan::new(name_tok.start, name_tok.end);
                    let ty = p.parse_type()?;
                    params.push((name_span, ty));
                }
                Ok(Delimit::OptionalIfNewLine)
            })?;
            end = rparen.end;
        }
        let return_type = if self.toks.step_if(TokenType::Arrow).is_some() {
            let ty = self.parse_type()?;
            end = ty.span().end;
            ty
        } else {
            UnresolvedType::Primitive {
                ty: Primitive::Unit,
                span_start: self.toks.previous().unwrap().start,
            }
        };

        let span = TSpan::new(start, end);
        let function_scope = self
            .ast
            .scope(ast::Scope::from_generics(scope, self.src, &generics, span));

        Ok(Function {
            generics,
            params,
            varargs,
            return_type,
            body: None,
            scope: function_scope,
            signature_span: TSpan::new(start, end),
            associated_name,
        })
    }

    fn parse_function_body(&mut self, scope: ScopeId) -> ParseResult<Option<ExprId>> {
        let first = self.toks.step()?;
        Ok(match_or_unexpected! {first, self.toks.module,
            TokenType::LBrace = TokenType::LBrace => {
                let block = self.parse_block_from_lbrace(first, scope)?;
                Some(self.ast.expr(block))
            },
            TokenType::Colon = TokenType::Colon => {
                let val = self.parse_expr(scope)?;
                Some(self.ast.expr(val))
            },
            TokenType::Keyword(Keyword::Extern) = TokenType::Keyword(Keyword::Extern) => {
                None
            }
        })
    }

    fn parse_trait_def(
        &mut self,
        trait_tok: Token,
        parent_scope: ScopeId,
        associated_name: TSpan,
    ) -> ParseResult<TraitDefinition> {
        debug_assert_eq!(trait_tok.ty, TokenType::Keyword(Keyword::Trait));
        let self_generic = GenericDef {
            name: TSpan::MISSING,
            requirements: Vec::new(),
        };
        let generics = self.parse_optional_generics(vec![self_generic])?;
        let scope = ast::Scope::from_generics(parent_scope, self.src, &generics, TSpan::MISSING);
        let scope = self.ast.scope(scope);
        self.toks.step_expect(TokenType::LBrace)?;
        let mut functions = Vec::new();
        let end = loop {
            let next = self.toks.step()?;
            match_or_unexpected! {next, self.toks.module,
                TokenType::RBrace = TokenType::RBrace => break next.end,
                TokenType::Ident = TokenType::Ident => {
                    let name_span = next.span();
                    self.toks.step_expect(TokenType::DoubleColon)?;
                    let fn_tok = self.toks.step_expect(TokenType::Keyword(Keyword::Fn))?;
                    let mut func = self.parse_function_header(fn_tok, scope, name_span, generics.to_vec())?;
                    if matches!(
                        self.toks.peek().map(|t| t.ty),
                        Some(TokenType::Colon | TokenType::LBrace)
                    ) {
                        if let Some(body) = self.parse_function_body(func.scope)? {
                            self.attach_func_body(&mut func, body);
                        }
                    }
                    functions.push((name_span, func));
                }
            }
        };
        let mut impls = Vec::new();
        if self
            .toks
            .step_if(TokenType::Keyword(Keyword::For))
            .is_some()
        {
            self.toks.step_expect(TokenType::LBrace)?;
            loop {
                let next = self.toks.step()?;
                match_or_unexpected! {next, self.toks.module,
                    TokenType::RBrace = TokenType::RBrace => break,
                    TokenType::Keyword(Keyword::Impl) = TokenType::Keyword(Keyword::Impl) => {
                        let start = next.start;
                        let generics = self.parse_optional_generics(Vec::new())?;
                        let impl_scope = self.ast
                            .scope(ast::Scope::from_generics(parent_scope, self.src, &generics, TSpan::MISSING));
                        let ty = self.parse_type()?;
                        let lbrace = self.toks.step_expect(TokenType::LBrace)?;
                        let (functions, end) = self.parse_trait_impl_body(lbrace, impl_scope, &generics)?;
                        self.ast.get_scope_mut(impl_scope).span = TSpan::new(start, end);
                        impls.push((impl_scope, generics, ty, functions));
                    }
                }
            }
        }
        let span = TSpan::new(trait_tok.start, end);
        self.ast.get_scope_mut(scope).span = span;

        Ok(TraitDefinition {
            generics,
            scope,
            functions,
            impls: impls.into_boxed_slice(),
            associated_name,
        })
    }

    fn parse_trait_impl_body(
        &mut self,
        lbrace: Token,
        scope: ScopeId,
        impl_generics: &[GenericDef],
    ) -> ParseResult<(Box<[(TSpan, ast::FunctionId)]>, u32)> {
        debug_assert_eq!(lbrace.ty, TokenType::LBrace);
        let mut functions = Vec::new();
        let last = self.parse_delimited(TokenType::Comma, TokenType::RBrace, |p| {
            let name = p.toks.step_expect(TokenType::Ident)?;
            let name_span = name.span();
            p.toks.step_expect(TokenType::DoubleColon)?;
            let fn_tok = p.toks.step_expect(TokenType::Keyword(Keyword::Fn))?;
            // TODO: figure out inherited generics here
            let func = p.parse_function_def(fn_tok, scope, name_span, impl_generics.to_vec())?;
            let func_id = p.ast.function(func);
            functions.push((name_span, func_id));
            Ok(Delimit::OptionalIfNewLine)
        })?;
        Ok((functions.into_boxed_slice(), last.end))
    }

    fn parse_stmt(&mut self, scope: ScopeId) -> ParseResult<Expr> {
        let expr = self.parse_expr(scope)?;
        self.stmt_postfix(expr, scope)
    }

    fn parse_stmt_starting_with(&mut self, expr: Expr, scope: ScopeId) -> ParseResult<Expr> {
        let lhs = self.parse_factor_postfix(expr, true, scope)?;
        let expr = self.parse_bin_op_rhs(0, lhs, scope)?;
        self.stmt_postfix(expr, scope)
    }

    fn stmt_postfix(&mut self, expr: Expr, scope: ScopeId) -> ParseResult<Expr> {
        let expr = if self.toks.step_if(TokenType::Colon).is_some() {
            let annotated_ty = self.parse_type()?;
            match self.toks.step_if(TokenType::Equals) {
                Some(_) => {
                    let val = self.parse_expr(scope)?;
                    Expr::DeclareWithVal {
                        pat: self.ast.expr(expr),
                        annotated_ty,
                        val: self.ast.expr(val),
                    }
                }
                None => Expr::Declare {
                    pat: self.ast.expr(expr),
                    annotated_ty,
                },
            }
        } else if let Some(declare) = self.toks.step_if(TokenType::Declare) {
            let val = self.parse_expr(scope)?;
            Expr::DeclareWithVal {
                pat: self.ast.expr(expr),
                annotated_ty: UnresolvedType::Infer(declare.span()),
                val: self.ast.expr(val),
            }
        } else {
            return Ok(expr);
        };
        Ok(expr)
    }

    fn parse_expr(&mut self, scope: ScopeId) -> ParseResult<Expr> {
        let lhs = self.parse_factor(true, scope)?;
        self.parse_bin_op_rhs(0, lhs, scope)
    }

    fn parse_factor(&mut self, include_as: bool, scope: ScopeId) -> ParseResult<Expr> {
        let first = self.toks.step()?;
        let start = first.start;
        let expr = match_or_unexpected_value!(first,
            self.toks.module, ExpectedTokens::Expr,
            TokenType::Keyword(Keyword::Fn) => {
                let func = self.parse_function_def(first, scope, TSpan::EMPTY, Vec::new())?;
                Expr::Function { id: self.ast.function(func) }
            },
            TokenType::Keyword(Keyword::Struct) => {
                let struct_def = self.struct_definition(first, scope)?;
                let id = self.ast.type_def(ast::TypeDef::Struct(struct_def));
                Expr::Type { id }
            },
            TokenType::Keyword(Keyword::Enum) => {
                let enum_def = self.enum_definition(first, scope)?;
                let id = self.ast.type_def(ast::TypeDef::Enum(enum_def));
                Expr::Type { id }
            },
            TokenType::Keyword(Keyword::Trait) => {
                let trait_def = self.parse_trait_def(first, scope, TSpan::MISSING)?;
                let id = self.ast.trait_def(trait_def);
                Expr::Trait { id }
            },
            TokenType::LBrace => {
                let block = self.parse_block_from_lbrace(first, scope)?;
                return Ok(self.parse_factor_postfix(block, true, scope)?);
            },
            TokenType::LBracket => {
                let mut elems = Vec::new();
                let closing = self.parse_delimited(TokenType::Comma, TokenType::RBracket, |p| {
                    elems.push(p.parse_expr(scope)?);
                    Ok(Delimit::OptionalIfNewLine)
                })?;
                Expr::Array(TSpan::new(start, closing.end), self.ast.exprs(elems))
            },
            TokenType::LParen => {
                if let Some(closing) = self.toks.step_if(TokenType::RParen) {
                    Expr::Unit(TSpan::new(start, closing.end))
                } else {
                    let expr = self.parse_expr(scope)?;
                    let after_expr = self.toks.step()?;
                    match_or_unexpected! { after_expr, self.toks.module,
                        TokenType::RParen = TokenType::RParen
                        => Expr::Nested(TSpan::new(start, after_expr.end), self.ast.expr(expr)),
                        TokenType::Comma = TokenType::Comma => {
                            // tuple
                            let mut elems = vec![expr];
                            let end = self.parse_delimited(TokenType::Comma, TokenType::RParen, |p| {
                                elems.push(p.parse_expr(scope)?);
                                Ok(())
                            })?.end;
                            Expr::Tuple(TSpan::new(start, end), self.ast.exprs(elems))
                        }
                    }
                }
            },
            TokenType::Minus => {
                let val = self.parse_factor(false, scope)?;
                Expr::UnOp(start, UnOp::Neg, self.ast.expr(val))
            },
            TokenType::Bang => {
                let val = self.parse_factor(false, scope)?;
                Expr::UnOp(start, UnOp::Not, self.ast.expr(val))
            },
            TokenType::Ampersand => {
                let val = self.parse_factor(false, scope)?;
                Expr::UnOp(
                    start,
                    UnOp::Ref,
                    self.ast.expr(val),
                )
            },
            TokenType::Keyword(Keyword::Ret) => {
                if self.toks.more_on_line() {
                    let val = self.parse_expr(scope)?;
                    let val = self.ast.expr(val);
                    Expr::Return { start, val }
                } else {
                    Expr::ReturnUnit { start }
                }
            },
            TokenType::IntLiteral => Expr::IntLiteral(first.span()),
            TokenType::FloatLiteral => Expr::FloatLiteral(first.span()),
            TokenType::StringLiteral => Expr::StringLiteral(TSpan::new(first.start, first.end)),
            TokenType::Keyword(Keyword::True) => Expr::BoolLiteral { start, val: true },
            TokenType::Keyword(Keyword::False) => Expr::BoolLiteral { start, val: false },
            TokenType::Ident => Expr::Ident { span: first.span() },
            TokenType::Underscore => Expr::Hole(first.start),
            TokenType::Keyword(Keyword::If) => {
                let cond = self.parse_expr(scope)?;
                let cond = self.ast.expr(cond);
                let pat_value = self.toks.step_if(TokenType::Declare).map(|_| {
                    let pat_value = self.parse_expr(scope)?;
                    Ok(self.ast.expr(pat_value))
                }).transpose()?;
                let then = self.parse_block_or_expr(scope)?;
                let then = self.ast.expr(then);

                let else_ = if let Some(tok) = self.toks.peek() {
                    if tok.ty == TokenType::Keyword(Keyword::Else) {
                        let tok = self.toks.step_assert(TokenType::Keyword(Keyword::Else));
                        let else_pos = tok.end;
                        self.toks.peek()
                            .ok_or_else(|| Error::UnexpectedEndOfFile.at(else_pos, else_pos, self.toks.module))?;

                        let else_ = self.parse_expr(scope)?;
                        Some(self.ast.expr(else_))
                    } else { None }
                } else { None };

                match (pat_value, else_) {
                    (None, None) => Expr::If { start, cond, then },
                    (None, Some(else_)) => Expr::IfElse { start, cond, then, else_ },
                    (Some(value), None) => Expr::IfPat { start, pat: cond, value, then },
                    (Some(value), Some(else_)) => Expr::IfPatElse { start, pat: cond, value, then, else_ },
                }
            },
            TokenType::Keyword(Keyword::Match) => {
                let val = self.parse_expr(scope)?;
                let val = self.ast.expr(val);
                let lbrace = self.toks.step_expect(TokenType::LBrace)?;

                let mut branches = Vec::new();
                let rbrace = self.parse_delimited(TokenType::Comma, TokenType::RBrace, |p| {
                    let pat = p.parse_expr(scope)?;
                    let next = p.toks.step()?;
                    let (branch, delimit) = match_or_unexpected!{next, p.toks.module,
                        TokenType::Colon = TokenType::Colon => {
                            (p.parse_expr(scope)?, Delimit::Yes)
                        },
                        TokenType::LBrace = TokenType::LBrace => {
                            (p.parse_block_from_lbrace(next, scope)?, Delimit::Optional)
                        }
                    };
                    branches.extend([pat, branch]);
                    Ok(delimit)
                })?;
                debug_assert_eq!(branches.len() % 2, 0);
                let branch_count = (branches.len() / 2) as u32;
                let extra_branches = self.ast.exprs(branches).idx;
                Expr::Match {
                    span: TSpan::new(lbrace.start, rbrace.end),
                    val,
                    extra_branches,
                    branch_count,
                }
            },
            TokenType::Keyword(Keyword::While) => self.parse_while_from_cond(first, scope)?,
            TokenType::Keyword(Keyword::Primitive(primitive)) => Expr::Primitive {
                primitive,
                start: first.start,
            },
            TokenType::Keyword(Keyword::Root) => {
                Expr::Root(start)
            },
            TokenType::Dot => {
                let tok = self.toks.step()?;
                match_or_unexpected! {tok, self.toks.module,
                    TokenType::Ident = TokenType::Ident => {
                        let (args, end) = self.parse_enum_args(scope)?;
                        let args = self.ast.exprs(args);
                        let span = TSpan::new(start, end.unwrap_or(tok.end));
                        Expr::EnumLiteral { span, ident: tok.span(), args }
                    },
                    TokenType::LBrace = TokenType::LBrace => {
                        unimplemented!("no more record syntax")
                    }
                }

            },
            TokenType::Keyword(Keyword::Asm) => {
                self.toks.step_expect(TokenType::LParen)?;
                let asm_str_span = self.toks.step_expect(TokenType::StringLiteral)?.span();
                let mut args = Vec::new();
                let end = loop {
                    let paren_or_comma = self.toks.step_expect([TokenType::Comma, TokenType::RParen])?;
                    match paren_or_comma.ty {
                        TokenType::Comma => {}
                        TokenType::RParen => break paren_or_comma.end,
                        _ => unreachable!()
                    }
                    args.push(self.parse_expr(scope)?);
                };
                Expr::Asm { span: TSpan::new(start, end), asm_str_span, args: self.ast.exprs(args) }
            }
        );
        self.parse_factor_postfix(expr, include_as, scope)
    }

    fn parse_factor_postfix(
        &mut self,
        mut expr: Expr,
        include_as: bool,
        scope: ScopeId,
    ) -> ParseResult<Expr> {
        loop {
            expr = match self.toks.peek().map(|t| t.ty) {
                Some(TokenType::LParen) => {
                    if !self.toks.more_on_line() {
                        // LParen is on new line, ignore
                        break Ok(expr);
                    }
                    let open_paren_start = self.toks.step_assert(TokenType::LParen).start;

                    // function call
                    let mut args = Vec::new();
                    let end = self
                        .parse_delimited(TokenType::Comma, TokenType::RParen, |p| {
                            args.push(p.parse_expr(scope)?);
                            Ok(Delimit::OptionalIfNewLine)
                        })?
                        .end;
                    let called_expr = self.ast.expr(expr);
                    let args = self.ast.exprs(args);
                    let call = self.ast.call(ast::Call {
                        called_expr,
                        open_paren_start,
                        args,
                        end,
                    });
                    Expr::FunctionCall(call)
                }
                Some(TokenType::LBracket) => {
                    if !self.toks.more_on_line() {
                        // LBracket is on new line, ignore
                        break Ok(expr);
                    }
                    self.toks.step_assert(TokenType::LBracket);

                    // array index
                    let idx = self.parse_expr(scope)?;
                    let idx = self.ast.expr(idx);

                    let end = self.toks.step_expect(TokenType::RBracket)?.end;

                    Expr::Index {
                        expr: self.ast.expr(expr),
                        idx,
                        end,
                    }
                }
                Some(TokenType::Dot) => {
                    let dot = self.toks.step_assert(TokenType::Dot);
                    let tok = self.toks.step()?;
                    match_or_unexpected! {tok, self.toks.module,
                        TokenType::Ident = TokenType::Ident => {
                            Expr::MemberAccess {
                                left: self.ast.expr(expr),
                                name: tok.span(),
                            }
                        },
                        TokenType::IntLiteral = TokenType::IntLiteral => {
                            let idx = self.src[tok.span().range()].parse().unwrap();
                            Expr::TupleIdx { left: self.ast.expr(expr), idx, end: tok.end }
                        },
                        TokenType::LBrace = TokenType::LBrace => {
                            if dot.new_line {
                                // record literal on new line, ignore
                                self.toks.step_back();
                                self.toks.step_back();
                                break Ok(expr);
                            }
                            /*Expr::Record {
                                span,
                                names,
                                values,
                            }*/
                            todo!("record parsing")
                        }
                    }
                }
                Some(TokenType::Caret) => {
                    let caret = self.toks.step_assert(TokenType::Caret);
                    Expr::UnOp(caret.end, UnOp::Deref, self.ast.expr(expr))
                }
                Some(TokenType::Keyword(Keyword::As)) if include_as => {
                    self.toks.step_assert(TokenType::Keyword(Keyword::As));
                    let target_ty = self.parse_type()?;
                    Expr::As(self.ast.expr(expr), target_ty)
                }
                _ => break Ok(expr),
            };
        }
    }

    fn parse_bin_op_rhs(
        &mut self,
        expr_prec: u8,
        mut lhs: Expr,
        scope: ScopeId,
    ) -> ParseResult<Expr> {
        while let Some(op) = self
            .toks
            .peek()
            .and_then(|t| Option::<Operator>::from(t.ty))
        {
            let op_prec = op.precedence();
            if op_prec < expr_prec {
                break;
            }
            self.toks.step().unwrap(); // op
            let mut rhs = self.parse_factor(true, scope)?;

            // If BinOp binds less tightly with RHS than the operator after RHS, let
            // the pending operator take RHS as its LHS.
            if let Some(next_op) = self
                .toks
                .peek()
                .and_then(|t| Option::<Operator>::from(t.ty))
            {
                if op_prec < next_op.precedence() {
                    rhs = self.parse_bin_op_rhs(op.precedence() + 1, rhs, scope)?;
                }
            }
            lhs = Expr::BinOp(op, self.ast.expr(lhs), self.ast.expr(rhs));
        }
        Ok(lhs)
    }

    /// Starts after the while keyword has already been parsed
    fn parse_while_from_cond(&mut self, while_tok: Token, scope: ScopeId) -> ParseResult<Expr> {
        debug_assert_eq!(while_tok.ty, TokenType::Keyword(Keyword::While));
        let cond = self.parse_expr(scope)?;
        let cond = self.ast.expr(cond);
        if self.toks.step_if(TokenType::Declare).is_some() {
            let val = self.parse_expr(scope)?;
            let val = self.ast.expr(val);
            let body = self.parse_block_or_expr(scope)?;
            let body = self.ast.expr(body);
            Ok(Expr::WhilePat {
                start: while_tok.start,
                pat: cond,
                val,
                body,
            })
        } else {
            let body = self.parse_block_or_expr(scope)?;
            Ok(Expr::While {
                start: while_tok.start,
                cond,
                body: self.ast.expr(body),
            })
        }
    }

    fn parse_path(&mut self) -> ParseResult<IdentPath> {
        let first = self
            .toks
            .step_expect([TokenType::Keyword(Keyword::Root), TokenType::Ident])?;
        let (s, e) = (first.start, first.end);
        self.parse_rest_of_path(s, e)
    }

    fn parse_rest_of_path(&mut self, start: u32, mut end: u32) -> ParseResult<IdentPath> {
        while self.toks.step_if(TokenType::Dot).is_some() {
            end = self.toks.step_expect(TokenType::Ident)?.end;
        }
        Ok(IdentPath::new(TSpan::new(start, end)))
    }

    /*
    fn parse_record(&mut self, lbrace: Token, ident_count: &mut Counts) -> ParseResult<Expr> {
        debug_assert_eq!(lbrace.ty, TokenType::LBrace);
        let start = lbrace.start;
        let mut names = vec![];
        let mut values = vec![];
        let end = self.parse_delimited(TokenType::Comma, TokenType::RBrace, |p| {
            let name = p.toks.step_expect(TokenType::Ident)?.span();
            p.toks.step_expect(TokenType::Colon)?;
            let val = p.parse_expr(ident_count)?;
            names.push(name);
            values.push(val);
            Ok(Delimit::OptionalIfNewLine)
        })?.end;
        debug_assert_eq!(names.len(), values.len());
        let values = self.ast.add_extra(&values);
        Ok(Expr::Record {
            span: TSpan::new(start, end),
            values: values.idx,
            names
        })
    }
    */

    fn parse_type(&mut self) -> ParseResult<UnresolvedType> {
        let type_tok = self.toks.step()?;
        match_or_unexpected_value!(type_tok,
            self.toks.module, ExpectedTokens::Type,
            TokenType::Keyword(Keyword::Root) => {
                let (s, e) = (type_tok.start, type_tok.end);
                Ok(UnresolvedType::Unresolved(
                    self.parse_rest_of_path(s, e)?,
                    self.parse_optional_generic_instance()?
                ))
            },
            TokenType::Ident => {
                let (s, e) = (type_tok.start, type_tok.end);
                Ok(UnresolvedType::Unresolved(
                    self.parse_rest_of_path(s, e)?,
                    self.parse_optional_generic_instance()?
                ))
            },
            TokenType::Keyword(Keyword::Primitive(primitive)) => {
                Ok(UnresolvedType::Primitive {
                    ty: primitive,
                    span_start: type_tok.start,
                })
            },
            TokenType::LParen => {
                let lparen_start = type_tok.start;
                if let Some(_) = self.toks.step_if(TokenType::RParen) {
                    return Ok(UnresolvedType::Primitive {
                        ty: Primitive::Unit,
                        span_start: lparen_start,
                    })
                }
                let mut tuple_types = Vec::new();
                let rparen_end = self.parse_delimited(TokenType::Comma, TokenType::RParen, |p| {
                    tuple_types.push(p.parse_type()?);
                    Ok(())
                })?.end;
                Ok(UnresolvedType::Tuple(tuple_types, TSpan::new(lparen_start, rparen_end)))

            },
            TokenType::LBracket => {
                let elem_ty = self.parse_type()?;
                self.toks.step_expect(TokenType::Semicolon)?;
                let count = if self.toks.step_if(TokenType::Underscore).is_some() {
                    None
                } else {
                    let int_span = self.toks.step_expect(TokenType::IntLiteral)?.span();
                    match self.src[int_span.range()].parse::<u64>()
                        .expect("Int Literal Error")
                        .try_into()
                    {
                        Ok(count) => Some(count),
                        Err(_) => return Err(CompileError::new(
                            Error::ArrayTooLarge,
                            int_span.in_mod(self.toks.module)
                        ))
                    }
                };
                let end = self.toks.step_expect(TokenType::RBracket)?.end;
                Ok(UnresolvedType::Array(Box::new((elem_ty, count, TSpan::new(type_tok.start, end)))))
            },
            TokenType::Star => {
                Ok(UnresolvedType::Pointer(Box::new((self.parse_type()?, type_tok.start))))
            },
            TokenType::Bang => {
                Ok(UnresolvedType::Primitive { ty: Primitive::Never, span_start: type_tok.start })
            },
            TokenType::Keyword(Keyword::Fn) => {
                let start = type_tok.start;
                let mut params = Vec::new();
                let end = if self.toks.step_if(TokenType::LParen).is_some() {
                    self.parse_delimited(TokenType::Comma, TokenType::RParen, |p| {
                        params.push(p.parse_type()?);
                        Ok(Delimit::OptionalIfNewLine)
                    })?.end
                } else {
                    type_tok.end
                };
                let return_type = if self.toks.step_if(TokenType::Arrow).is_some() {
                    self.parse_type()?
                } else {
                    UnresolvedType::Primitive {ty: Primitive::Unit, span_start: end }
                };
                Ok(UnresolvedType::Function {
                    span_and_return_type: Box::new((TSpan::new(start, end), return_type)),
                    params: params.into_boxed_slice(),
                })
            },
            TokenType::Underscore => Ok(UnresolvedType::Infer(type_tok.span()))
        )
    }

    fn parse_optional_generics(
        &mut self,
        inherited: Vec<GenericDef>,
    ) -> ParseResult<Box<[GenericDef]>> {
        if !self.toks.step_if(TokenType::LBracket).is_some() {
            return Ok(inherited.into_boxed_slice());
        }
        let mut generics = inherited;
        self.parse_delimited(TokenType::Comma, TokenType::RBracket, |p| {
            let name = p.toks.step_expect(TokenType::Ident)?.span();
            let mut requirements = Vec::new();
            if p.toks.step_if(TokenType::Colon).is_some() {
                loop {
                    requirements.push(p.parse_path()?);
                    if p.toks.step_if(TokenType::Plus).is_none() {
                        break;
                    }
                }
                p.toks.step_if(TokenType::Ident);
            }
            generics.push(GenericDef { name, requirements });
            Ok(Delimit::OptionalIfNewLine)
        })?;
        let generic_count: Result<u8, _> = generics.len().try_into();
        if generic_count.is_err() {
            let start = generics[0].span().start;
            let end = generics.last().unwrap().span().end;
            return Err(Error::TooManyGenerics(generics.len())
                .at_span(TSpan::new(start, end).in_mod(self.toks.module)));
        };
        Ok(generics.into_boxed_slice())
    }

    fn parse_optional_generic_instance(
        &mut self,
    ) -> ParseResult<Option<(Box<[UnresolvedType]>, TSpan)>> {
        self.toks
            .step_if(TokenType::LBracket)
            .map(|l_bracket| {
                let mut types = Vec::new();
                let r_bracket =
                    self.parse_delimited(TokenType::Comma, TokenType::RBracket, |p| {
                        types.push(p.parse_type()?);
                        Ok(())
                    })?;
                Ok((
                    types.into_boxed_slice(),
                    TSpan::new(l_bracket.start, r_bracket.end),
                ))
            })
            .transpose()
    }

    /// parses optional arguments of an enum and returns them and the end position if arguments are
    /// present.
    fn parse_enum_args(&mut self, scope: ScopeId) -> ParseResult<(Vec<Expr>, Option<u32>)> {
        let mut args = vec![];
        let end = self
            .toks
            .peek()
            .is_some_and(|tok| tok.ty == TokenType::LParen && !tok.new_line)
            .then(|| {
                self.toks.step_assert(TokenType::LParen);
                self.parse_delimited(TokenType::Comma, TokenType::RParen, |p| {
                    args.push(p.parse_expr(scope)?);
                    Ok(Delimit::OptionalIfNewLine)
                })
                .map(|end_tok| end_tok.end)
            })
            .transpose()?;

        Ok((args, end))
    }
}
