use dmap::DHashMap;

use std::collections::hash_map::Entry;

use crate::ast::{
    self, Attribute, Definition, EnumVariantDefinition, Expr, ExprIds, Function, GenericDef,
    Global, InherentImpl, Item, ItemValue, StructMember, TraitDefinition, TraitFunctions,
    TreeToken, UnOp,
};

use crate::unexpected;
use crate::{Delimit, ParseResult, Parser, ast::ScopeId};

use error::{CompileError, Error};
use span::{IdentPath, Span, TSpan};
use token::{self, ExpectedTokens, Keyword, Operator, Token, TokenType};
use types::UnresolvedType;

macro_rules! step_or_unexpected {
    (
        $parser: ident,
        $tok: ident,
        $($tok_ty: ident $($kw: ident $(($kw_val: ident))? )? => $res: expr),*
    ) => {{
        let $tok = $parser.toks.step();
        match $tok.ty {
            $(
                TokenType::$tok_ty $((Keyword::$kw $(($kw_val))* ))* => $res,
            )*
            _ => return Err(unexpected(
                $tok,
                $parser.toks.module,
                ExpectedTokens::AnyOf(Box::new([ $(TokenType::$tok_ty $((Keyword::$kw))*),* ])),
            ))
        }
    }};
}

fn t<T: TreeToken>(t: Token) -> T {
    T::t(t)
}

impl<T: TreeToken> Parser<'_, T> {
    pub fn parse_module(&mut self, module_defs: DHashMap<String, Definition<T>>) -> ScopeId {
        self.parse_items_until(0, None, module_defs, None, Self::on_module_level_expr)
            .0
    }

    /// Parses a delimited list. The `item` function parses an item and is supposed to handle the
    /// result itself.
    /// `delim` is a delimiter. Trailing delimiters are allowed, but optional here.
    /// `end` is the ending token. It will be returned from this function once parsed.
    fn parse_delimited<F, D>(
        &mut self,
        open: Token,
        delim: TokenType,
        close: TokenType,
        mut item: F,
    ) -> ParseResult<Token>
    where
        F: FnMut(&mut Parser<T>) -> Result<D, CompileError>,
        D: Into<Delimit>,
    {
        loop {
            if let Some(end_tok) = self.toks.step_if(close) {
                return Ok(end_tok);
            }
            match item(self).map(Into::into) {
                Ok(Delimit::Yes) => match self.toks.step() {
                    tok if tok.ty == delim => continue,
                    tok if tok.ty == close => return Ok(tok),
                    tok => {
                        return Err(unexpected(
                            tok,
                            self.toks.module,
                            ExpectedTokens::AnyOf(Box::new([delim, close])),
                        ));
                    }
                },
                Ok(Delimit::No) => {}
                Ok(Delimit::Optional) => {
                    self.toks.step_if(delim);
                }
                Ok(Delimit::OptionalIfNewLine) => {
                    if self.toks.step_if(delim).is_none() {
                        let after = self.toks.peek();
                        if after.ty != TokenType::Eof && !after.new_line && after.ty != close {
                            self.recover_in_delimited(open.ty, close);
                            return Err(Error::UnexpectedToken {
                                expected: ExpectedTokens::AnyOf(Box::new([delim, close])),
                                found: after.ty,
                            }
                            .at_span(after.span().in_mod(self.toks.module)));
                        }
                    }
                }
                Err(err) => {
                    self.recover_in_delimited(open.ty, close);
                    return Err(err);
                }
            }
        }
    }

    fn recover_in_delimited(&mut self, open: TokenType, close: TokenType) {
        let mut open_count: u32 = 0;
        // try to find the close of the current enclosed delimited
        loop {
            match self.toks.step().ty {
                ty if ty == open => open_count += 1,
                ty if ty == close => {
                    if let Some(x) = open_count.checked_sub(1) {
                        open_count = x
                    } else {
                        break;
                    }
                }
                TokenType::Eof => break,
                _ => {}
            }
        }
    }

    /// parses items until end token or eof if end is None
    /// returns the end position
    fn parse_items_until(
        &mut self,
        start: u32,
        parent: Option<ScopeId>,
        definitions: DHashMap<String, Definition<T>>,
        start_end: Option<(Token, TokenType)>,
        mut on_expr: impl FnMut(&mut Self, &mut ast::Scope<T>, ScopeId, Expr<T>, Span),
    ) -> (ScopeId, Token) {
        let scope_id = self.ast.scope(ast::Scope::missing());
        let mut scope = ast::Scope {
            parent,
            braces: T::opt_none(),
            definitions,
            span: TSpan::MISSING, // span will be updated at the end of this function
            has_errors: false,
        };

        let end_tok = loop {
            if let Some((_, end)) = start_end {
                if let Some(end_tok) = self.toks.step_if(end) {
                    break end_tok;
                }
            } else if let Some(eof) = self.toks.step_if(TokenType::Eof) {
                break eof;
            }

            let item = match self.parse_item(scope_id) {
                Ok(item) => item,
                Err(err) => {
                    scope.has_errors = true;
                    self.toks.errors.emit_err(err);
                    continue;
                }
            };
            match item.value {
                ItemValue::Definition {
                    t_name,
                    name,
                    name_span,
                    t_colon_colon,
                    annotated_ty,
                    value,
                } => {
                    // try to assign names of definitions
                    // this is a bit hacky but works for now
                    match *self.ast.get_expr(value) {
                        Expr::Function { id } => self.ast.assign_function_name(id, name_span),
                        Expr::Trait { id } => self.ast.assign_trait_name(id, name_span),
                        _ => {}
                    }
                    match scope.definitions.entry(name) {
                        Entry::Occupied(_) => {
                            scope.has_errors = true;
                            self.toks.errors.emit_err(Error::DuplicateDefinition.at(
                                name_span.start,
                                name_span.end,
                                self.toks.module,
                            ));
                        }
                        Entry::Vacant(vacant_entry) => {
                            vacant_entry.insert(Definition::Expr {
                                t_name,
                                t_colon_colon,
                                id: self.ast.def_expr(value, annotated_ty),
                            });
                        }
                    }
                }
                ItemValue::Use { t_use, path } => {
                    let (_, _, name) = path.segments(self.toks.src);
                    let name_span = name.map_or_else(|| path.span(), |(_, span)| span);
                    let name = name.map_or("root", |(name, _)| name).to_owned();
                    match scope.definitions.entry(name) {
                        Entry::Occupied(_) => {
                            scope.has_errors = true;
                            self.toks.errors.emit_err(
                                Error::DuplicateDefinition
                                    .at_span(name_span.in_mod(self.toks.module)),
                            )
                        }
                        Entry::Vacant(entry) => {
                            entry.insert(Definition::Use { t_use, path });
                        }
                    }
                }
                ItemValue::Expr(r) => {
                    let span = Span {
                        start,
                        end: self.toks.pos(),
                        module: self.toks.module,
                    };
                    on_expr(self, &mut scope, scope_id, r, span);
                }
            };
        };
        if let Some((start, _)) = start_end {
            scope.braces = T::opt((t(start), t(end_tok)));
        }
        scope.span = TSpan::new(start, end_tok.end);
        *self.ast.get_scope_mut(scope_id) = scope;
        (scope_id, end_tok)
    }

    fn on_module_level_expr(
        &mut self,
        scope: &mut ast::Scope<T>,
        scope_id: ScopeId,
        expr: Expr<T>,
        _: Span,
    ) {
        let expr = self.ast.expr(expr);
        match self.ast.get_expr(expr) {
            Expr::DeclareWithVal {
                pat,
                annotated_ty,
                val,
                t_colon_and_equals_or_colon_equals,
            } => {
                let start = self.ast.get_expr(expr).span_builder(self.ast).start;
                let end = self.ast.get_expr(*val).span_builder(self.ast).end;
                match self.ast.get_expr(*pat) {
                    Expr::Ident { span, t } => {
                        let name = self.toks.src[span.range()].to_owned();
                        let id = self.ast.global(Global {
                            name: name.clone().into_boxed_str(),
                            t_name: t.clone(),
                            scope: scope_id,
                            t_colon_and_equals_or_colon_equals: t_colon_and_equals_or_colon_equals
                                .clone(),
                            ty: annotated_ty.clone(),
                            val: *val,
                            span: TSpan::new(start, end),
                        });
                        scope.definitions.insert(name, Definition::Global(id));
                    }
                    expr => {
                        let span = expr.span_builder(self.ast).in_mod(self.toks.module);
                        self.ast.get_scope_mut(scope_id).has_errors = true;
                        self.toks
                            .errors
                            .emit_err(Error::InvalidGlobalVarPattern.at_span(span));
                    }
                }
            }
            _ => self.toks.errors.emit_err(CompileError {
                err: Error::InvalidTopLevelBlockItem,
                span: self
                    .ast
                    .get_expr(expr)
                    .span_builder(self.ast)
                    .in_mod(self.toks.module),
            }),
        };
    }

    fn parse_block_or_stmt(&mut self, scope: ScopeId) -> ParseResult<Expr<T>> {
        step_or_unexpected! {self, tok,
            LBrace => Ok(self.parse_block_from_lbrace(tok, scope)),
            Colon => {
                self.parse_stmt(scope)
            }
        }
    }

    fn parse_block_from_lbrace(&mut self, lbrace: Token, parent: ScopeId) -> Expr<T> {
        debug_assert_eq!(lbrace.ty, TokenType::LBrace);
        let mut items = Vec::new();

        let (scope, rbrace) = self.parse_items_until(
            lbrace.start,
            Some(parent),
            dmap::new(),
            Some((lbrace, TokenType::RBrace)),
            |_, _, _, expr, _| items.push(expr),
        );

        let items = self.ast.exprs(items);
        Expr::Block {
            t_open: T::t(lbrace),
            scope,
            items,
            t_close: T::t(rbrace),
        }
    }

    fn parse_item(&mut self, scope: ScopeId) -> Result<Item<T>, CompileError> {
        let attributes = self.parse_attributes(scope)?;
        let value = match self.toks.peek().ty {
            // use statement
            TokenType::Keyword(Keyword::Use) => {
                let t_use = self.toks.step_assert(TokenType::Keyword(Keyword::Use));
                let path = self.parse_path()?;
                ItemValue::Use {
                    t_use: t(t_use),
                    path,
                }
            }
            // either a variable or constant definition or just an identifier
            TokenType::Ident => {
                let ident = self.toks.step_assert(TokenType::Ident);
                let ident_span = ident.span();
                let name = ident.get_val(self.toks.src);
                match self.toks.peek().ty {
                    // constant definition
                    TokenType::DoubleColon => {
                        let double_colon = self.toks.step_assert(TokenType::DoubleColon);
                        let value = self.parse_expr(scope).unwrap_or_else(|err| {
                            let span = err.span;
                            self.toks.errors.emit_err(err);
                            Expr::Error(span.tspan())
                        });
                        let value = self.ast.expr(value);
                        ItemValue::Definition {
                            t_name: t(ident),
                            t_colon_colon: T::either_a(t(double_colon)),
                            name: name.to_owned(),
                            name_span: ident_span,
                            annotated_ty: UnresolvedType::Infer(double_colon.span()),
                            value,
                        }
                    }
                    // Variable or constant declaration with explicit type
                    TokenType::Colon => {
                        let colon = self.toks.step_assert(TokenType::Colon);
                        let annotated_ty = self.parse_type()?;
                        if let Some(equals) = self.toks.step_if(TokenType::Equals) {
                            // typed variable with initial value
                            let pat = self.ast.expr(Expr::Ident {
                                span: ident_span,
                                t: T::t(ident),
                            });
                            let val = self.parse_expr(scope)?;
                            let val = self.ast.expr(val);
                            ItemValue::Expr(Expr::DeclareWithVal {
                                pat,
                                annotated_ty,
                                t_colon_and_equals_or_colon_equals: T::either_a((
                                    t(colon),
                                    t(equals),
                                )),
                                val,
                            })
                        } else if let Some(second_colon) = self.toks.step_if(TokenType::Colon) {
                            // typed constant
                            let value = self.parse_expr(scope)?;
                            ItemValue::Definition {
                                t_name: t(ident),
                                name: name.to_owned(),
                                name_span: ident_span,
                                t_colon_colon: T::either_b((t(colon), t(second_colon))),
                                annotated_ty,
                                value: self.ast.expr(value),
                            }
                        } else {
                            // typed variable without initial value
                            let pat = self.ast.expr(Expr::Ident {
                                span: ident_span,
                                t: t(ident),
                            });
                            ItemValue::Expr(Expr::Declare {
                                pat,
                                t_colon: t(colon),
                                annotated_ty,
                            })
                        }
                    }
                    // Variable declaration with inferred type
                    TokenType::Declare => {
                        let decl = self.toks.step_assert(TokenType::Declare);
                        let pat = self.ast.expr(Expr::Ident {
                            span: ident_span,
                            t: t(ident),
                        });
                        let val = self.parse_expr(scope)?;

                        ItemValue::Expr(Expr::DeclareWithVal {
                            pat,
                            t_colon_and_equals_or_colon_equals: T::either_b(t(decl)),
                            annotated_ty: UnresolvedType::Infer(decl.span()),
                            val: self.ast.expr(val),
                        })
                    }
                    _ => {
                        let var = Expr::Ident {
                            span: ident_span,
                            t: t(ident),
                        };
                        let expr = self.parse_stmt_starting_with(var, scope)?;
                        ItemValue::Expr(expr)
                    }
                }
            }
            _ => ItemValue::Expr(self.parse_stmt(scope)?),
        };
        Ok(Item { attributes, value })
    }

    fn parse_attributes(&mut self, scope: ScopeId) -> ParseResult<Box<[Attribute]>> {
        let mut attributes = Vec::new();
        while let Some(at) = self.toks.step_if(TokenType::At) {
            let path = self.parse_path()?;
            let mut args = Vec::new();
            let peeked = self.toks.peek();
            let end = if peeked.ty == TokenType::LParen && !peeked.new_line {
                let lparen = self.toks.step_assert(TokenType::LParen);
                self.parse_delimited(lparen, TokenType::Comma, TokenType::RParen, |p| {
                    args.push(p.parse_expr(scope)?);
                    Ok(Delimit::OptionalIfNewLine)
                })?
                .end
            } else {
                path.span().end
            };
            attributes.push(Attribute {
                path,
                args: self.ast.exprs(args),
                span: TSpan::new(at.start, end),
            });
        }
        Ok(attributes.into_boxed_slice())
    }

    fn parse_function_def(
        &mut self,
        fn_tok: Token,
        scope: ScopeId,
        associated_name: TSpan,
        inherited_generics: Vec<GenericDef<T>>,
    ) -> ParseResult<Function<T>> {
        let mut func =
            self.parse_function_header(fn_tok, scope, associated_name, inherited_generics)?;
        self.parse_function_body(&mut func)?;
        Ok(func)
    }

    fn struct_definition(
        &mut self,
        struct_tok: Token,
        scope: ScopeId,
    ) -> ParseResult<ast::TypeDef<T>> {
        debug_assert_eq!(struct_tok.ty, TokenType::Keyword(Keyword::Struct));
        let (generics, brackets) = self.parse_optional_generics(Vec::new())?;

        let scope = {
            let scope = ast::Scope::from_generics(
                scope,
                self.toks.src,
                &generics,
                TSpan::MISSING,
                brackets,
            );
            self.ast.scope(scope)
        };

        let lbrace = self.toks.step_expect(TokenType::LBrace)?;
        let mut members = Vec::new();
        let mut methods = dmap::new();
        let mut impls = Vec::new();

        let rbrace = self.parse_delimited(lbrace, TokenType::Comma, TokenType::RBrace, |p| {
            let attributes = p.parse_attributes(scope)?;
            if let Some(impl_tok) = p.toks.step_if(TokenType::Keyword(Keyword::Impl)) {
                impls.push(p.parse_inherent_impl(impl_tok, scope, &generics)?);
                return Ok(Delimit::No);
            }
            let ident = p.toks.step_expect(TokenType::Ident)?;
            if p.toks.step_if(TokenType::DoubleColon).is_some() {
                let fn_tok = p.toks.step_expect(TokenType::Keyword(Keyword::Fn))?;
                let method =
                    p.parse_function_def(fn_tok, scope, ident.span(), generics.to_vec())?;
                let func_id = p.ast.function(method);
                let name = ident.get_val(p.toks.src).to_owned();
                if let Some(_existing) = methods.insert(name, func_id) {
                    return Err(CompileError::new(
                        Error::DuplicateDefinition,
                        ident.span().in_mod(p.toks.module),
                    ));
                }
                Ok(Delimit::No)
            } else {
                let name = ident.span();
                let ty = p.parse_type()?;
                members.push(StructMember {
                    attributes,
                    name,
                    ty,
                });
                Ok(Delimit::OptionalIfNewLine)
            }
        })?;
        self.ast.get_scope_mut(scope).span = TSpan::new(struct_tok.start, rbrace.end);
        Ok(ast::TypeDef {
            t_introducer: t(struct_tok),
            generics,
            scope,
            methods,
            impls: impls.into_boxed_slice(),
            content: ast::TypeContent::Struct { members },
        })
    }

    fn enum_definition(&mut self, enum_tok: Token, scope: ScopeId) -> ParseResult<ast::TypeDef<T>> {
        debug_assert_eq!(enum_tok.ty, TokenType::Keyword(Keyword::Enum));
        let (generics, brackets) = self.parse_optional_generics(Vec::new())?;

        let scope = self.ast.scope(ast::Scope::from_generics(
            scope,
            self.toks.src,
            &generics,
            TSpan::MISSING,
            brackets,
        ));

        let mut variants = Vec::new();
        let mut methods = dmap::new();
        let mut impls = Vec::new();

        let lbrace = self.toks.step_expect(TokenType::LBrace)?;
        let rbrace = self.parse_delimited(lbrace, TokenType::Comma, TokenType::RBrace, |p| {
            if let Some(impl_tok) = p.toks.step_if(TokenType::Keyword(Keyword::Impl)) {
                impls.push(p.parse_inherent_impl(impl_tok, scope, &generics)?);
                return Ok(Delimit::No);
            }
            let ident = p.toks.step_expect(TokenType::Ident)?;
            match p.toks.peek().ty {
                TokenType::LParen => {
                    let lparen = p.toks.step_assert(TokenType::LParen);

                    let name_span = ident.span();
                    let mut args = vec![];
                    let end = p
                        .parse_delimited(lparen, TokenType::Comma, TokenType::RParen, |p| {
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
                TokenType::DoubleColon => {
                    p.toks.step_assert(TokenType::DoubleColon);

                    let fn_tok = p.toks.step_expect(TokenType::Keyword(Keyword::Fn))?;
                    let method =
                        p.parse_function_def(fn_tok, scope, ident.span(), generics.to_vec())?;
                    let func_id = p.ast.function(method);
                    let name = ident.get_val(p.toks.src).to_owned();
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

        Ok(ast::TypeDef {
            t_introducer: t(enum_tok),
            generics,
            scope,
            methods,
            impls: impls.into_boxed_slice(),
            content: ast::TypeContent::Enum {
                variants: variants.into_boxed_slice(),
            },
        })
    }

    /// Will just return a function with the body always set to `None`
    fn parse_function_header(
        &mut self,
        fn_tok: Token,
        scope: ScopeId,
        associated_name: TSpan,
        inherited_generics: Vec<GenericDef<T>>,
    ) -> ParseResult<Function<T>> {
        debug_assert_eq!(fn_tok.ty, TokenType::Keyword(Keyword::Fn));
        let start = fn_tok.start;
        let mut end = fn_tok.end;
        let (generics, generics_brackets) = self.parse_optional_generics(inherited_generics)?;

        let mut params = Vec::new();
        let mut named_params = Vec::new();
        let mut varargs = false;
        let mut t_varargs = T::opt_none();

        let t_parens = if let Some(lparen) = self.toks.step_if(TokenType::LParen) {
            let rparen =
                self.parse_delimited(lparen, TokenType::Comma, TokenType::RParen, |p| {
                    if varargs {
                        // can't be an RParen since parse_delimited would have returned otherwise
                        let err = p.toks.step_expect(TokenType::RParen).unwrap_err();
                        return Err(err);
                    }
                    if let Some(tok) = p.toks.step_if(TokenType::TripleDot) {
                        varargs = true;
                        t_varargs = T::opt(t(tok));
                    } else {
                        let name_tok = p.toks.step_expect(TokenType::Ident)?;
                        let name_span = TSpan::new(name_tok.start, name_tok.end);
                        let equals = p.toks.step_if(TokenType::Equals);
                        let ty = if let Some(equals) = equals {
                            UnresolvedType::Infer(equals.span())
                        } else if !matches!(p.toks.peek().ty, TokenType::RParen | TokenType::Comma)
                        {
                            p.parse_type()?
                        } else {
                            UnresolvedType::Infer(name_span)
                        };
                        if equals.is_some() || p.toks.step_if(TokenType::Equals).is_some() {
                            let default_value = p.parse_expr(scope)?;
                            // TODO: should check no duplicate params exist here or in check_signature
                            named_params.push((name_span, ty, Some(p.ast.expr(default_value))));
                        } else {
                            params.push((name_span, ty));
                        }
                    }
                    Ok(Delimit::OptionalIfNewLine)
                })?;
            end = rparen.end;
            T::opt((t(lparen), t(rparen)))
        } else {
            T::opt_none()
        };
        let (t_arrow, return_type) = if let Some(arrow) = self.toks.step_if(TokenType::Arrow) {
            let ty = self.parse_type()?;
            end = ty.span().end;
            (T::opt(t(arrow)), ty)
        } else {
            (
                T::opt_none(),
                UnresolvedType::Tuple(Vec::new(), TSpan::new(end, end)),
            )
        };

        let span = TSpan::new(start, end);
        let function_scope = self.ast.scope(ast::Scope::from_generics(
            scope,
            self.toks.src,
            &generics,
            span,
            generics_brackets,
        ));

        Ok(Function {
            t_fn: t(fn_tok),
            generics,
            t_parens,
            params: params.into_boxed_slice(),
            named_params: named_params.into_boxed_slice(),
            varargs,
            t_varargs,
            t_arrow,
            return_type,
            t_colon: T::opt_none(),
            t_extern: T::opt_none(),
            body: None,
            scope: function_scope,
            signature_span: TSpan::new(start, end),
            associated_name,
        })
    }

    fn parse_function_body(&mut self, func: &mut Function<T>) -> ParseResult<()> {
        let body = step_or_unexpected! {self, tok,
            LBrace => {
                let block = self.parse_block_from_lbrace(tok, func.scope);
                Some(self.ast.expr(block))
            },
            Colon => {
                let val = self.parse_expr(func.scope)?;
                func.t_colon = T::opt(t(tok));
                Some(self.ast.expr(val))
            },
            Keyword Extern => {
                func.t_extern = T::opt(t(tok));
                None
            }
        };
        if let Some(body) = body {
            func.body = Some(body);
            let new_end = self.ast.get_expr(body).span_builder(self.ast).end;
            self.ast.get_scope_mut(func.scope).span.end = new_end;
        }
        Ok(())
    }

    fn parse_trait_def(
        &mut self,
        trait_tok: Token,
        parent_scope: ScopeId,
        associated_name: TSpan,
    ) -> ParseResult<TraitDefinition<T>> {
        debug_assert_eq!(trait_tok.ty, TokenType::Keyword(Keyword::Trait));
        let self_generic = GenericDef {
            name: TSpan::MISSING,
            t_name: T::opt_none(),
            bounds: Box::new([]),
        };
        let (generics, brackets) = self.parse_optional_generics(vec![self_generic])?;
        let scope = ast::Scope::from_generics(
            parent_scope,
            self.toks.src,
            &generics,
            TSpan::MISSING,
            brackets,
        );
        let scope = self.ast.scope(scope);
        self.toks.step_expect(TokenType::LBrace)?;
        let mut functions = Vec::new();
        let end = loop {
            step_or_unexpected! {self, tok,
                RBrace => break tok.end,
                Ident => {
                    let name_span = tok.span();
                    self.toks.step_expect(TokenType::DoubleColon)?;
                    let fn_tok = self.toks.step_expect(TokenType::Keyword(Keyword::Fn))?;
                    let mut func = self.parse_function_header(
                        fn_tok,
                        scope,
                        name_span,
                        generics.to_vec(),
                    )?;
                    if matches!(self.toks.peek().ty, TokenType::Colon | TokenType::LBrace) {
                        self.parse_function_body(&mut func)?;
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
                step_or_unexpected! {self, tok,
                    RBrace => break,
                    Keyword Impl => {
                        let start = tok.start;
                        let (generics, brackets) = self.parse_optional_generics(Vec::new())?;
                        let underscore_end = self.toks.step_expect(TokenType::Underscore)?.end;
                        let trait_generics = self.parse_optional_generic_instance()?
                            .unwrap_or_else(|| (Box::new([]), TSpan::new(underscore_end, underscore_end)));
                        let t_for = t(self.toks.step_expect(TokenType::Keyword(Keyword::For))?);
                        let impl_scope = self.ast.scope(ast::Scope::from_generics(
                            parent_scope,
                            self.toks.src,
                            &generics,
                            TSpan::MISSING,
                            brackets,
                        ));
                        let implemented_type = self.parse_type()?;
                        let lbrace = self.toks.step_expect(TokenType::LBrace)?;
                        let (functions, end) = self.parse_trait_impl_body(
                            lbrace,
                            impl_scope,
                            &generics,
                        )?;
                        self.ast.get_scope_mut(impl_scope).span = TSpan::new(start, end);
                        impls.push(ast::Impl {
                            t_impl: t(tok),
                            implemented_type,
                            t_for,
                            base: ast::BaseImpl {
                                scope: impl_scope,
                                generics,
                                trait_generics,
                                functions,
                            }
                        });
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
        impl_generics: &[GenericDef<T>],
    ) -> ParseResult<(TraitFunctions, u32)> {
        debug_assert_eq!(lbrace.ty, TokenType::LBrace);
        let mut functions = Vec::new();
        let last = self.parse_delimited(lbrace, TokenType::Comma, TokenType::RBrace, |p| {
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

    fn parse_inherent_impl(
        &mut self,
        impl_tok: Token,
        outer_scope: ScopeId,
        type_generics: &[GenericDef<T>],
    ) -> ParseResult<InherentImpl<T>> {
        let (impl_generics, brackets) = self.parse_optional_generics(type_generics.to_vec())?;
        let scope = self.ast.scope(ast::Scope::from_generics(
            outer_scope,
            self.toks.src,
            &impl_generics,
            TSpan::MISSING,
            brackets,
        ));
        let implemented_trait = self.parse_path()?;
        let trait_generics = self
            .parse_optional_generic_instance()?
            .unwrap_or((Box::new([]), implemented_trait.span()));
        let lbrace = self.toks.step_expect(TokenType::LBrace)?;
        let (functions, end) = self.parse_trait_impl_body(lbrace, scope, &impl_generics)?;
        self.ast.get_scope_mut(scope).span = TSpan::new(impl_tok.start, end);
        Ok(InherentImpl {
            implemented_trait,
            base: ast::BaseImpl {
                scope,
                generics: impl_generics,
                trait_generics,
                functions,
            },
        })
    }

    fn parse_stmt(&mut self, scope: ScopeId) -> ParseResult<Expr<T>> {
        let expr = self.parse_expr(scope)?;
        self.stmt_postfix(expr, scope)
    }

    fn parse_stmt_starting_with(&mut self, expr: Expr<T>, scope: ScopeId) -> ParseResult<Expr<T>> {
        let lhs = self.parse_factor_postfix(expr, true, scope)?;
        let expr = self.parse_bin_op_rhs(0, lhs, scope)?;
        self.stmt_postfix(expr, scope)
    }

    fn stmt_postfix(&mut self, expr: Expr<T>, scope: ScopeId) -> ParseResult<Expr<T>> {
        let expr = if let Some(colon) = self.toks.step_if(TokenType::Colon) {
            let annotated_ty = self.parse_type()?;
            match self.toks.step_if(TokenType::Equals) {
                Some(equals) => {
                    let val = self.parse_expr(scope)?;
                    Expr::DeclareWithVal {
                        pat: self.ast.expr(expr),
                        t_colon_and_equals_or_colon_equals: T::either_a((t(colon), t(equals))),
                        annotated_ty,
                        val: self.ast.expr(val),
                    }
                }
                None => Expr::Declare {
                    pat: self.ast.expr(expr),
                    t_colon: t(colon),
                    annotated_ty,
                },
            }
        } else if let Some(declare) = self.toks.step_if(TokenType::Declare) {
            let val = self.parse_expr(scope)?;
            Expr::DeclareWithVal {
                pat: self.ast.expr(expr),
                t_colon_and_equals_or_colon_equals: T::either_b(t(declare)),
                annotated_ty: UnresolvedType::Infer(declare.span()),
                val: self.ast.expr(val),
            }
        } else if let Some(eq) = self.toks.step_if(TokenType::Equals) {
            let val = self.parse_expr(scope)?;
            Expr::BinOp {
                t_op: t(eq),
                op: Operator::Assignment(token::AssignType::Assign),
                l: self.ast.expr(expr),
                r: self.ast.expr(val),
            }
        } else {
            return Ok(expr);
        };
        Ok(expr)
    }

    fn parse_expr(&mut self, scope: ScopeId) -> ParseResult<Expr<T>> {
        let lhs = self.parse_factor(true, scope)?;
        self.parse_bin_op_rhs(0, lhs, scope)
    }

    fn parse_factor(&mut self, include_as: bool, scope: ScopeId) -> ParseResult<Expr<T>> {
        let first = self.toks.step();
        let expr = match first.ty {
            TokenType::Keyword(Keyword::Fn) => {
                let func = self.parse_function_def(first, scope, TSpan::EMPTY, Vec::new())?;
                Expr::Function {
                    id: self.ast.function(func),
                }
            }
            TokenType::Keyword(Keyword::Struct) => {
                let def = self.struct_definition(first, scope)?;
                let id = self.ast.type_def(def);
                Expr::Type { id }
            }
            TokenType::Keyword(Keyword::Enum) => {
                let def = self.enum_definition(first, scope)?;
                let id = self.ast.type_def(def);
                Expr::Type { id }
            }
            TokenType::Keyword(Keyword::Trait) => {
                let trait_def = self.parse_trait_def(first, scope, TSpan::MISSING)?;
                let id = self.ast.trait_def(trait_def);
                Expr::Trait { id }
            }
            TokenType::LBrace => {
                let block = self.parse_block_from_lbrace(first, scope);
                return self.parse_factor_postfix(block, true, scope);
            }
            TokenType::LBracket => {
                let mut elems = Vec::new();
                let rbracket =
                    self.parse_delimited(first, TokenType::Comma, TokenType::RBracket, |p| {
                        elems.push(p.parse_expr(scope)?);
                        Ok(Delimit::OptionalIfNewLine)
                    })?;
                Expr::Array {
                    span: TSpan::new(first.start, rbracket.end),
                    t_lbracket: t(first),
                    elements: self.ast.exprs(elems),
                    t_rbracket: t(rbracket),
                }
            }
            TokenType::LParen => {
                if let Some(rparen) = self.toks.step_if(TokenType::RParen) {
                    Expr::Tuple {
                        span: TSpan::new(first.start, rparen.end),
                        t_lparen: t(first),
                        elements: ExprIds::EMPTY,
                        t_rparen: t(rparen),
                    }
                } else {
                    let expr = self.parse_expr(scope)?;
                    step_or_unexpected! { self, tok,
                        RParen => Expr::Nested {
                            span: TSpan::new(first.start, tok.end),
                            t_lparen: t(first),
                            inner: self.ast.expr(expr),
                            t_rparen: t(tok),
                        },
                        Comma => {
                            // tuple
                            let mut elems = vec![expr];
                            let rparen = self.parse_delimited(first, TokenType::Comma, TokenType::RParen, |p| {
                                elems.push(p.parse_expr(scope)?);
                                Ok(())
                            })?;
                            Expr::Tuple {
                                span: TSpan::new(first.start, rparen.end),
                                t_lparen: t(first),
                                elements: self.ast.exprs(elems),
                                t_rparen: t(rparen),
                            }
                        }
                    }
                }
            }
            TokenType::Minus => {
                let val = self.parse_factor(false, scope)?;
                Expr::UnOp(first.start, UnOp::Neg, self.ast.expr(val))
            }
            TokenType::Bang => {
                let val = self.parse_factor(false, scope)?;
                Expr::UnOp(first.start, UnOp::Not, self.ast.expr(val))
            }
            TokenType::Ampersand => {
                let val = self.parse_factor(false, scope)?;
                Expr::UnOp(first.start, UnOp::Ref, self.ast.expr(val))
            }
            TokenType::Keyword(Keyword::Ret) => {
                if !self.toks.peek().new_line {
                    let val = self.parse_expr(scope)?;
                    let val = self.ast.expr(val);
                    Expr::Return {
                        start: first.start,
                        t_ret: t(first),
                        val,
                    }
                } else {
                    Expr::ReturnUnit { start: first.start }
                }
            }
            TokenType::IntLiteral => Expr::IntLiteral {
                span: first.span(),
                t: t(first),
            },
            TokenType::FloatLiteral => Expr::FloatLiteral {
                span: first.span(),
                t: t(first),
            },
            TokenType::StringLiteral => Expr::StringLiteral {
                span: TSpan::new(first.start, first.end),
                t: t(first),
            },
            TokenType::Ident => Expr::Ident {
                span: first.span(),
                t: t(first),
            },
            TokenType::Underscore => Expr::Hole {
                loc: first.start,
                t: t(first),
            },
            TokenType::Keyword(Keyword::If) => {
                let cond = self.parse_expr(scope)?;
                let cond = self.ast.expr(cond);
                let pat_value = self
                    .toks
                    .step_if(TokenType::Declare)
                    .map(|_| {
                        let pat_value = self.parse_expr(scope)?;
                        Ok(self.ast.expr(pat_value))
                    })
                    .transpose()?;
                let then = self.parse_block_or_stmt(scope)?;
                let then = self.ast.expr(then);

                let else_ = if self
                    .toks
                    .step_if(TokenType::Keyword(Keyword::Else))
                    .is_some()
                {
                    let else_ = self.parse_stmt(scope)?;
                    Some(self.ast.expr(else_))
                } else {
                    None
                };

                let start = first.start;
                match (pat_value, else_) {
                    (None, None) => Expr::If { start, cond, then },
                    (None, Some(else_)) => Expr::IfElse {
                        start,
                        cond,
                        then,
                        else_,
                    },
                    (Some(value), None) => Expr::IfPat {
                        start,
                        pat: cond,
                        value,
                        then,
                    },
                    (Some(value), Some(else_)) => Expr::IfPatElse {
                        start,
                        pat: cond,
                        value,
                        then,
                        else_,
                    },
                }
            }
            TokenType::Keyword(Keyword::Match) => {
                let val = self.parse_expr(scope)?;
                let val = self.ast.expr(val);
                let lbrace = self.toks.step_expect(TokenType::LBrace)?;

                let mut branches = Vec::new();
                let rbrace =
                    self.parse_delimited(lbrace, TokenType::Comma, TokenType::RBrace, |p| {
                        let pat = p.parse_expr(scope)?;
                        let (branch, delimit) = step_or_unexpected! {p, tok,
                            Colon => {
                                (p.parse_expr(scope)?, Delimit::Yes)
                            },
                            LBrace => {
                                (p.parse_block_from_lbrace(tok, scope), Delimit::Optional)
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
            }
            TokenType::Keyword(Keyword::While) => self.parse_while_from_cond(first, scope)?,
            TokenType::Keyword(Keyword::For) => {
                //self.parse_
                let pat = self.parse_expr(scope)?;
                self.toks.step_expect(TokenType::Keyword(Keyword::In))?;
                let iter = self.parse_expr(scope)?;
                let body = self.parse_block_or_stmt(scope)?;
                Expr::For {
                    start: first.start,
                    pat: self.ast.expr(pat),
                    iter: self.ast.expr(iter),
                    body: self.ast.expr(body),
                }
            }
            TokenType::Keyword(Keyword::Primitive(primitive)) => Expr::Primitive {
                primitive,
                start: first.start,
                t: t(first),
            },
            TokenType::Keyword(Keyword::Root) => Expr::Root(first.start),
            TokenType::Dot => {
                step_or_unexpected! {self, tok,
                    Ident => {
                        let (args, parens) = self.parse_enum_args(scope)?;
                        let args = self.ast.exprs(args);
                        let span = TSpan::new(first.start, parens.map_or(tok.end, |(_, rparen)| rparen.end));
                        Expr::EnumLiteral { span,
                            t_dot: t(first),
                            ident: tok.span(),
                            t_ident: t(tok),
                            t_parens: parens.map_or(T::opt_none(), |(l, r)| T::opt((t(l), t(r)))),
                            args,
                        }
                    },
                    LBrace => {
                        unimplemented!("no more record syntax")
                    }
                }
            }
            TokenType::Keyword(Keyword::Asm) => {
                self.toks.step_expect(TokenType::LParen)?;
                let asm_str_span = self.toks.step_expect(TokenType::StringLiteral)?.span();
                let mut args = Vec::new();
                let end = loop {
                    let paren_or_comma = self
                        .toks
                        .step_expect([TokenType::Comma, TokenType::RParen])?;
                    match paren_or_comma.ty {
                        TokenType::Comma => {}
                        TokenType::RParen => break paren_or_comma.end,
                        _ => unreachable!(),
                    }
                    args.push(self.parse_expr(scope)?);
                };
                Expr::Asm {
                    span: TSpan::new(first.start, end),
                    asm_str_span,
                    args: self.ast.exprs(args),
                }
            }
            TokenType::Keyword(Keyword::Break) => Expr::Break { start: first.start },
            TokenType::Keyword(Keyword::Continue) => Expr::Continue { start: first.start },
            _ => {
                return Err(unexpected(first, self.toks.module, ExpectedTokens::Expr));
            }
        };
        self.parse_factor_postfix(expr, include_as, scope)
    }

    fn parse_factor_postfix(
        &mut self,
        mut expr: Expr<T>,
        include_as: bool,
        scope: ScopeId,
    ) -> ParseResult<Expr<T>> {
        loop {
            let tok = self.toks.peek();
            expr = match tok.ty {
                TokenType::LParen if !tok.new_line => {
                    let lparen = self.toks.step_assert(TokenType::LParen);

                    // function call
                    let mut args = Vec::new();
                    let mut named_args = Vec::new();
                    let rparen =
                        self.parse_delimited(lparen, TokenType::Comma, TokenType::RParen, |p| {
                            let expr = p.parse_expr(scope)?;
                            if p.toks.step_if(TokenType::Colon).is_some() {
                                let value = p.parse_expr(scope)?;
                                let Expr::Ident {
                                    span: name_span, ..
                                } = expr
                                else {
                                    p.toks.errors.emit_err(
                                        Error::NameExpected.at_span(
                                            expr.span_builder(p.ast).in_mod(p.toks.module),
                                        ),
                                    );
                                    return Ok(Delimit::OptionalIfNewLine);
                                };
                                named_args.push((name_span, p.ast.expr(value)));
                            } else {
                                args.push(expr);
                            }
                            Ok(Delimit::OptionalIfNewLine)
                        })?;
                    let called_expr = self.ast.expr(expr);
                    let args = self.ast.exprs(args);
                    let call = self.ast.call(ast::Call {
                        called_expr,
                        t_lparen: t(lparen),
                        open_paren_start: lparen.start,
                        args,
                        named_args,
                        t_rparen: t(rparen),
                        end: rparen.end,
                    });
                    Expr::FunctionCall(call)
                }
                TokenType::LBracket if !tok.new_line => {
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
                TokenType::Dot => {
                    self.toks.step_assert(TokenType::Dot);
                    step_or_unexpected! {self, tok,
                        Ident => {
                            Expr::MemberAccess {
                                left: self.ast.expr(expr),
                                name: tok.span(),
                            }
                        },
                        IntLiteral => {
                            let idx = self.toks.src[tok.span().range()].parse().unwrap();
                            Expr::TupleIdx { left: self.ast.expr(expr), idx, end: tok.end }
                        }
                    }
                }
                TokenType::Caret => {
                    let caret = self.toks.step_assert(TokenType::Caret);
                    Expr::UnOp(caret.end, UnOp::Deref, self.ast.expr(expr))
                }
                TokenType::Keyword(Keyword::As) if include_as => {
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
        mut lhs: Expr<T>,
        scope: ScopeId,
    ) -> ParseResult<Expr<T>> {
        while let Some(op) = Option::<Operator>::from(self.toks.peek().ty) {
            let op_prec = op.precedence();
            if op_prec < expr_prec {
                break;
            }
            let op_token = self.toks.step(); // op
            let mut rhs = self.parse_factor(true, scope)?;

            // If BinOp binds less tightly with RHS than the operator after RHS, let
            // the pending operator take RHS as its LHS.
            if let Some(next_op) = Option::<Operator>::from(self.toks.peek().ty)
                && op_prec < next_op.precedence()
            {
                rhs = self.parse_bin_op_rhs(op.precedence() + 1, rhs, scope)?;
            }
            lhs = Expr::BinOp {
                t_op: t(op_token),
                op,
                l: self.ast.expr(lhs),
                r: self.ast.expr(rhs),
            };
        }
        Ok(lhs)
    }

    /// Starts after the while keyword has already been parsed
    fn parse_while_from_cond(&mut self, while_tok: Token, scope: ScopeId) -> ParseResult<Expr<T>> {
        debug_assert_eq!(while_tok.ty, TokenType::Keyword(Keyword::While));
        let cond = self.parse_expr(scope)?;
        let cond = self.ast.expr(cond);
        if self.toks.step_if(TokenType::Declare).is_some() {
            let val = self.parse_expr(scope)?;
            let val = self.ast.expr(val);
            let body = self.parse_block_or_stmt(scope)?;
            let body = self.ast.expr(body);
            Ok(Expr::WhilePat {
                start: while_tok.start,
                pat: cond,
                val,
                body,
            })
        } else {
            let body = self.parse_block_or_stmt(scope)?;
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

    fn parse_type(&mut self) -> ParseResult<UnresolvedType> {
        let tok = self.toks.step();
        match tok.ty {
            TokenType::Keyword(Keyword::Root) => Ok(UnresolvedType::Unresolved(
                self.parse_rest_of_path(tok.start, tok.end)?,
                self.parse_optional_generic_instance()?,
            )),
            TokenType::Ident => Ok(UnresolvedType::Unresolved(
                self.parse_rest_of_path(tok.start, tok.end)?,
                self.parse_optional_generic_instance()?,
            )),
            TokenType::Keyword(Keyword::Primitive(primitive)) => Ok(UnresolvedType::Primitive {
                ty: primitive,
                span_start: tok.start,
            }),
            TokenType::LParen => {
                let mut tuple_types = Vec::new();
                let rparen_end = self
                    .parse_delimited(tok, TokenType::Comma, TokenType::RParen, |p| {
                        tuple_types.push(p.parse_type()?);
                        Ok(())
                    })?
                    .end;
                Ok(UnresolvedType::Tuple(
                    tuple_types,
                    TSpan::new(tok.start, rparen_end),
                ))
            }
            TokenType::LBracket => {
                let elem_ty = self.parse_type()?;
                self.toks.step_expect(TokenType::Semicolon)?;
                let count = if self.toks.step_if(TokenType::Underscore).is_some() {
                    None
                } else {
                    let int_span = self.toks.step_expect(TokenType::IntLiteral)?.span();
                    match self.toks.src[int_span.range()]
                        .parse::<u64>()
                        .expect("Int Literal Error")
                        .try_into()
                    {
                        Ok(count) => Some(count),
                        Err(_) => {
                            return Err(CompileError::new(
                                Error::ArrayTooLarge,
                                int_span.in_mod(self.toks.module),
                            ));
                        }
                    }
                };
                let end = self.toks.step_expect(TokenType::RBracket)?.end;
                Ok(UnresolvedType::Array(Box::new((
                    elem_ty,
                    count,
                    TSpan::new(tok.start, end),
                ))))
            }
            TokenType::Star => Ok(UnresolvedType::Pointer(Box::new((
                self.parse_type()?,
                tok.start,
            )))),
            TokenType::Keyword(Keyword::Fn) => {
                let start = tok.start;
                let mut params = Vec::new();
                let end = if let Some(lparen) = self.toks.step_if(TokenType::LParen) {
                    self.parse_delimited(lparen, TokenType::Comma, TokenType::RParen, |p| {
                        params.push(p.parse_type()?);
                        Ok(Delimit::OptionalIfNewLine)
                    })?
                    .end
                } else {
                    tok.end
                };
                let return_type = if self.toks.step_if(TokenType::Arrow).is_some() {
                    self.parse_type()?
                } else {
                    UnresolvedType::Tuple(Vec::new(), TSpan::new(end, end))
                };
                Ok(UnresolvedType::Function {
                    span_and_return_type: Box::new((TSpan::new(start, end), return_type)),
                    params: params.into_boxed_slice(),
                })
            }
            TokenType::Underscore => Ok(UnresolvedType::Infer(tok.span())),
            _ => Err(unexpected(tok, self.toks.module, ExpectedTokens::Type)),
        }
    }

    fn parse_optional_generics(
        &mut self,
        inherited: Vec<GenericDef<T>>,
    ) -> ParseResult<(Box<[GenericDef<T>]>, Option<(Token, Token)>)> {
        let Some(lbracket) = self.toks.step_if(TokenType::LBracket) else {
            return Ok((inherited.into_boxed_slice(), None));
        };
        let mut generics = inherited;
        let rbracket =
            self.parse_delimited(lbracket, TokenType::Comma, TokenType::RBracket, |p| {
                let name = p.toks.step_expect(TokenType::Ident)?;
                let name_span = name.span();
                let mut requirements = Vec::new();
                if p.toks.step_if(TokenType::Colon).is_some() {
                    loop {
                        let path = p.parse_path()?;
                        let (generics, generics_span) =
                            p.parse_optional_generic_instance()?.unwrap_or_else(|| {
                                (Box::new([]), TSpan::new(path.span().end, path.span().end))
                            });
                        requirements.push(ast::TraitBound {
                            path,
                            generics,
                            generics_span,
                        });
                        if p.toks.step_if(TokenType::Plus).is_none() {
                            break;
                        }
                    }
                    p.toks.step_if(TokenType::Ident);
                }
                generics.push(GenericDef {
                    name: name_span,
                    t_name: T::opt(t(name)),
                    bounds: requirements.into_boxed_slice(),
                });
                Ok(Delimit::OptionalIfNewLine)
            })?;
        let generic_count: Result<u8, _> = generics.len().try_into();
        if generic_count.is_err() {
            let start = generics[0].span().start;
            let end = generics.last().unwrap().span().end;
            return Err(Error::TooManyGenerics(generics.len())
                .at_span(TSpan::new(start, end).in_mod(self.toks.module)));
        };
        Ok((generics.into_boxed_slice(), Some((lbracket, rbracket))))
    }

    fn parse_optional_generic_instance(
        &mut self,
    ) -> ParseResult<Option<(Box<[UnresolvedType]>, TSpan)>> {
        self.toks
            .step_if(TokenType::LBracket)
            .map(|lbracket| {
                let mut types = Vec::new();
                let r_bracket =
                    self.parse_delimited(lbracket, TokenType::Comma, TokenType::RBracket, |p| {
                        types.push(p.parse_type()?);
                        Ok(())
                    })?;
                Ok((
                    types.into_boxed_slice(),
                    TSpan::new(lbracket.start, r_bracket.end),
                ))
            })
            .transpose()
    }

    /// parses optional arguments of an enum and returns them and the end position if arguments are
    /// present.
    fn parse_enum_args(
        &mut self,
        scope: ScopeId,
    ) -> ParseResult<(Vec<Expr<T>>, Option<(Token, Token)>)> {
        let mut args = vec![];
        let lparen = self.toks.peek();
        let rparen = (lparen.ty == TokenType::LParen && !lparen.new_line)
            .then(|| {
                let lparen = self.toks.step_assert(TokenType::LParen);
                self.parse_delimited(lparen, TokenType::Comma, TokenType::RParen, |p| {
                    args.push(p.parse_expr(scope)?);
                    Ok(Delimit::OptionalIfNewLine)
                })
            })
            .transpose()?;
        Ok((args, rparen.map(|rparen| (lparen, rparen))))
    }
}
