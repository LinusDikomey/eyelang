pub mod ast;
pub mod token;
mod lexer;
mod reader;

pub use reader::ExpectedTokens;

use id::ModuleId;

use span::{TSpan, Span, IdentPath};
use token::Token;
use types::{UnresolvedType, Primitive};

use crate::{error::{CompileError, Error, Errors}, parser::reader::match_or_unexpected};

use self::{
    ast::{Expr, Item, Global, GenericDef, StructDefinition, Function, ExprId, TraitDefinition, TraitImpl, UnOp, TypeDef, IdentId},
    token::{TokenType, Keyword, Operator}, reader::{Delimit, match_or_unexpected_value},
};

pub fn parse(
    source: &str,
    errors: &mut Errors,
    module: ModuleId,
) -> Option<ast::Ast> {
    let tokens = lexer::lex(&source, errors, module)?;
    let mut ast_builder = ast::AstBuilder::new();
    let mut parser = Parser {
        src: &source,
        ast: &mut ast_builder,
        toks: reader::TokenReader::new(tokens, module),
    };

    match parser.parse_module() {
        Ok(scope) => Some(ast_builder.finish_with_top_level_scope(scope)),
        Err(err) => {
            errors.emit_err(err);
            None
        }
    }
}

type ParseResult<T> = Result<T, CompileError>;

#[derive(Debug, Clone, Copy)]
pub struct Counts {
    pub idents: u32,
}
impl Counts {
    fn new() -> Self {
        Self { idents: 0 }
    }
    fn ident(&mut self) -> IdentId {
        self.idents +=1;
        IdentId(self.idents - 1)
    }
}

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
                                dbg!(after);
                                return Err(Error::UnexpectedToken {
                                    expected: ExpectedTokens::AnyOf(vec![delim, end]),
                                    found: after.ty
                                }.at_span(after.span().in_mod(self.toks.module)));
                            }
                        }
                    }

                }
            }
        }
    }

    fn parse_module(&mut self) -> ParseResult<ast::Scope> {
        let mut definitions = dmap::new();
        let mut impls = Vec::new();

        while !self.toks.is_at_end() {
            let start = self.toks.current().unwrap().start;
            let name_pat = |pat: &Expr, s: &Self|  match pat {
                Expr::Variable { span, .. } => Ok(*span),
                expr => {
                    Err(Error::InvalidGlobalVarPattern.at_span(expr.span_in(s.ast, s.toks.module)))
                }
            };
            
            let mut item_counts = Counts::new();

            let def = match self.parse_item(&mut item_counts)? {
                Item::Definition {
                    name,
                    name_span,
                    value,
                    counts,
                } => Some((name, name_span, def)),
                Item::Impl(impl_) => {
                    impls.push(impl_);
                    None
                }
                Item::Expr(r) => match &self.ast.get_expr(r) {
                    Expr::Declare {
                        pat,
                        annotated_ty,
                    } => {
                        let name = name_pat(self.ast.get_expr(*pat), self)?;
                        let id = self.ast.add_global(Global {
                            ty: annotated_ty.clone(),
                            val: None
                        });
                        Some((
                            self.src[name.range()].to_owned(),
                            name,
                            Definition::Global(id),
                        ))
                    },
                    Expr::DeclareWithVal {
                        pat,
                        annotated_ty,
                        val,
                    } => {
                        let name = name_pat(self.ast.get_expr(*pat), self)?;
                        let id = self.ast.add_global(Global {
                            ty: annotated_ty.clone(),
                            val: Some((*val, item_counts))
                        });
                        Some((
                            self.src[name.range()].to_owned(),
                            name,
                            Definition::Global(id),
                        ))
                    },
                    _ => {
                        return Err(CompileError {
                            err: Error::InvalidTopLevelBlockItem,
                            span: Span {
                                start,
                                end: self.toks.current_end_pos(),
                                module: self.toks.module,
                            },
                        })
                    }
                },
            };
            if let Some((name, name_span, def)) = def {
                if let Some(_existing) = definitions.insert(name, def) {
                    return Err(Error::DuplicateDefinition.at(
                        name_span.start,
                        name_span.end,
                        self.toks.module,
                    ));
                }
            }
        }
        Ok(ast::Scope {
            definitions: self.ast.add_defs(definitions),
            impls,
        })
    }

    fn parse_block_or_expr(&mut self, counts: &mut Counts) -> ParseResult<Expr> {
        match_or_unexpected!(
            self.toks.peek()
                .ok_or_else(|| Error::UnexpectedEndOfFile.at(
                    self.toks.last_src_pos(),
                    self.toks.last_src_pos(),
                    self.toks.module
                ))?,
            self.toks.module,
            TokenType::LBrace = TokenType::LBrace => self.parse_block(counts),
            TokenType::Colon = TokenType::Colon => {
                self.toks.step_expect(TokenType::Colon)?;
                self.parse_expr(counts)
            }
        )
    }

    fn parse_block(&mut self, counts: &mut Counts) -> ParseResult<Expr> {
        let lbrace = self.toks.step_expect(TokenType::LBrace)?;
        self.parse_block_from_lbrace(lbrace, counts)
    }

    fn parse_block_from_lbrace(&mut self, lbrace: Token, counts: &mut Counts) -> ParseResult<Expr> {
        debug_assert_eq!(lbrace.ty, TokenType::LBrace);

        let mut definitions = dmap::new();
        let mut impls = Vec::new();
        let mut items = Vec::new();

        while self.toks.current()?.ty != TokenType::RBrace {
            let start = self.toks.current().unwrap().start;
            match self.parse_item(counts)? {
                Item::Definition {
                    name,
                    name_span: _,
                    value,
                    counts,
                } => {
                    if let Some(_existing) = definitions.insert(name, (value, counts)) {
                        let end = self.toks.current().unwrap().end;
                        return Err(Error::DuplicateDefinition.at(start, end, self.toks.module));
                    }
                }
                Item::Impl(impl_) => impls.push(impl_),
                Item::Expr(item) => items.push(item),
            }
        }
        let rbrace = self.toks.step_expect(TokenType::RBrace)?;
        let items = self.ast.exprs(items);

        let scope = self.ast.scope(ast::Scope {
            definitions,
            impls,
        });

        Ok(Expr::Block {
            scope,
            items,
            span: TSpan::new(lbrace.start, rbrace.end),
        })
    }

    fn parse_item(&mut self, counts: &mut Counts) -> Result<Item, CompileError> {
        let cur = self.toks.current()?;
        Ok(match cur.ty {
            // use statement
            TokenType::Keyword(Keyword::Use) => {
                self.toks.step_assert(TokenType::Keyword(Keyword::Use));
                let use_tok = self.toks.current().unwrap();
                let use_start = use_tok.start;
                let use_end = use_tok.end;

                let path = self.parse_path()?;

                Item::Use(path)
            }
            // Trait implementation
            TokenType::Keyword(Keyword::Impl) => {
                let impl_tok = self.toks.step_assert(TokenType::Keyword(Keyword::Impl));
                Item::Impl(self.parse_trait_impl(impl_tok)?)
            }
            // either a struct, constant or a variable
            TokenType::Ident => {
                let ident = self.toks.step_assert(TokenType::Ident);
                let ident_span = ident.span();
                let name = ident.get_val(self.src);
                match self.toks.peek().map(|t| t.ty) {
                    // Struct definition, constant or enum
                    Some(TokenType::DoubleColon) => {
                        self.toks.step_assert(TokenType::DoubleColon);

                        /*
                        let def = if let Some(struct_tok) =
                            self.toks.step_if(TokenType::Keyword(Keyword::Struct))
                        {
                            let def = self.struct_definition(name, struct_tok)?;
                            Definition::Type(self.ast.add_type(TypeDef::Struct(def)))
                        } else if self
                            .toks
                            .step_if(TokenType::Keyword(Keyword::Enum))
                            .is_some()
                        {
                            let def = self.enum_definition(name.to_owned())?;
                            Definition::Type(self.ast.add_type(TypeDef::Enum(def)))
                        } else if let Some(trait_tok) =
                            self.toks.step_if(TokenType::Keyword(Keyword::Trait))
                        {
                            let def = self.parse_trait_def(trait_tok)?;
                            Definition::Trait(self.ast.add_trait(def))
                        } else {
                            let mut counts = Counts::new();
                            let val = self.parse_expr(&mut counts)?;
                            Definition::Const {
                                ty: UnresolvedType::Infer(0),
                                val,
                                counts,
                            }
                        };
                        */
                        let mut counts = Counts::new();
                        let value = self.ast.expr(self.parse_expr(&mut counts)?);
                        Item::Definition {
                            name: name.to_owned(),
                            name_span: ident_span,
                            value,
                            counts,
                        }
                    }
                    // Variable or constant declaration with explicit type
                    Some(TokenType::Colon) => {
                        self.toks.step_assert(TokenType::Colon);
                        let ty = self.parse_type()?;
                        if self.toks.step_if(TokenType::Equals).is_some() {
                            // typed variable with initial value
                            let pat = self.ast.expr(Expr::Variable { span: ident_span, id: counts.ident() });
                            let val = self.ast.expr(self.parse_expr(counts)?);
                            Item::Expr(Expr::DeclareWithVal {
                                pat,
                                annotated_ty: ty,
                                val,
                            })
                        } else if self.toks.step_if(TokenType::Colon).is_some() {
                            // typed constant
                            let mut counts = Counts::new();
                            Item::Definition {
                                name: name.to_owned(),
                                name_span: ident_span,
                                value: self.ast.expr(self.parse_expr(&mut counts)?),
                                counts,
                            }
                        } else {
                            // typed variable without initial value
                            let pat = self.ast.expr(Expr::Variable { span: ident_span, id: counts.ident() });
                            Item::Expr(Expr::Declare {
                                pat,
                                annotated_ty: ty,
                            })
                        }
                    }
                    // Variable declaration with inferred type
                    Some(TokenType::Declare) => {
                        let decl_start = self.toks.step_assert(TokenType::Declare).start;
                        let pat = self.ast.expr(Expr::Variable { span: ident_span, id: counts.ident() });
                        let val = self.ast.expr(self.parse_expr(counts)?);

                        Item::Expr(Expr::DeclareWithVal {
                            pat,
                            annotated_ty: UnresolvedType::Infer(decl_start),
                            val,
                        })
                    }
                    _ => {
                        let var = self.ast.expr(Expr::Variable { span: ident_span, id: counts.ident() });
                        let expr = self.parse_stmt_starting_with(var, counts)?;
                        Item::Expr(expr)
                    }
                }
            }
            _ => Item::Expr(self.parse_stmt(counts)?),
        })
    }

    fn parse_function_def(&mut self, fn_tok: Token) -> ParseResult<Function> {
        let mut func = self.parse_function_header(fn_tok)?;
        func.body = self.parse_function_body(&mut func.counts)?;
        Ok(func)
    }

    fn struct_definition(&mut self, name: &str, struct_tok: Token) -> Result<StructDefinition, Error> {
        debug_assert_eq!(struct_tok.ty, TokenType::Keyword(Keyword::Struct));
        let generics = self.parse_optional_generics()?;

        self.toks.step_expect(TokenType::LBrace)?;

        let mut members: Vec<(String, UnresolvedType, u32, u32)> = Vec::new();
        let mut methods = dmap::new();
        self.parse_delimited(TokenType::Comma, TokenType::RBrace, |p| {
            let ident = p.toks.step_expect(TokenType::Ident)?;
            if p.toks.step_if(TokenType::DoubleColon).is_some() {
                let fn_tok = p.toks.step_expect(TokenType::Keyword(Keyword::Fn))?;
                let method = p.parse_function_def(fn_tok)?;
                let func_id = p.ast.add_func(method);
                let name = ident.get_val(p.src).to_owned();
                if let Some(_existing) = methods.insert(name, func_id) {
                    return Err(CompileError::new(
                        Error::DuplicateDefinition,
                        ident.span().in_mod(p.toks.module),
                    ));
                }
                Ok(Delimit::No)
            } else {
                let member_name = ident.get_val(p.src);
                let member_type = p.parse_type()?;
                let end = member_type.span().end;
                members.push((member_name.to_owned(), member_type, ident.start, end));
                Ok(Delimit::OptionalIfNewLine)
            }
        })?;
        Ok(StructDefinition {
            name: name.to_owned(),
            generics: generics.map_or(Vec::new(), |g| g.1),
            members,
            methods,
        })
    }

    fn enum_definition(&mut self, name: String) -> ParseResult<ast::EnumDefinition> {
        let generics = self.parse_optional_generics()?;

        self.toks.step_expect(TokenType::LBrace)?;
        let mut variants = Vec::new();
        let mut methods = dmap::new();

        self.parse_delimited(TokenType::Comma, TokenType::RBrace, |p| {
            let ident = p.toks.step_expect(TokenType::Ident)?;
            match p.toks.peek().map(|t| t.ty) {
                Some(TokenType::LParen) => { 
                    p.toks.step_assert(TokenType::LParen);
                    let mut span = ident.span();
                    let variant = ident.get_val(p.src).to_owned();
                    let mut args = vec![];
                    span.end = p.parse_delimited(
                        TokenType::Comma,
                        TokenType::RParen,
                        |p| p.parse_type().map(|ty| args.push(ty)),
                    )?.end;
                    variants.push((span, variant, args));
                    Ok(Delimit::OptionalIfNewLine)
                }
                Some(TokenType::DoubleColon) => {
                    p.toks.step_assert(TokenType::DoubleColon);

                    let fn_tok = p.toks.step_expect(TokenType::Keyword(Keyword::Fn))?;
                    let method = p.parse_function_def(fn_tok)?;
                    let func_id = p.ast.add_func(method);
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
                    variants.push((ident.span(), ident.get_val(p.src).to_owned(), Vec::new()));
                    Ok(Delimit::OptionalIfNewLine)
                }
            }
        })?;

        Ok(ast::EnumDefinition {
            name,
            generics: generics.map_or(Vec::new(), |g| g.1),
            variants,
            methods,
        })
    }
    
    /// Will just return a function with the body always set to `None`
    fn parse_function_header(&mut self, fn_tok: Token) -> ParseResult<Function> {
        debug_assert_eq!(fn_tok.ty, TokenType::Keyword(Keyword::Fn));
        let start = fn_tok.start;
        let generics = self.parse_optional_generics()?.map_or(Vec::new(), |g| g.1);

        let mut params = Vec::new();
        let mut varargs = false;

        if self.toks.step_if(TokenType::LParen).is_some() {
            self.parse_delimited(TokenType::Comma, TokenType::RParen, |p| {
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
                    let name = name_tok.get_val(p.src).to_owned();
                    let (s, e) = (name_tok.start, name_tok.end);
                    let ty = p.parse_type()?;
                    params.push((name, ty, s, e));
                }
                Ok(())
            })?;
        }
        let return_type = if self.toks.step_if(TokenType::Arrow).is_some() {
            self.parse_type()?
        } else {
            UnresolvedType::Primitive {
                ty: Primitive::Unit, 
                span_start: self.toks.previous().unwrap().start,
            }
        };

        let end = self.toks.previous().unwrap().end;

        let ident_count = params.len() as u32;

        Ok(Function {
            generics,
            params,
            varargs,
            return_type,
            body: None,
            counts: Counts { idents: ident_count },
            span: TSpan { start, end },
        })
    }

    fn parse_function_body(&mut self, counts: &mut Counts) -> ParseResult<Option<Expr>> {
        let first = self.toks.step()?;
        Ok(match_or_unexpected! {first, self.toks.module,
            TokenType::LBrace = TokenType::LBrace => Some(self.parse_block_from_lbrace(first, counts)?),
            TokenType::Colon = TokenType::Colon => {
                Some(self.parse_expr(counts)?)
            },
            TokenType::Keyword(Keyword::Extern) = TokenType::Keyword(Keyword::Extern) => {
                None
            }
        })
    }

    fn parse_trait_def(&mut self, trait_tok: Token) -> ParseResult<TraitDefinition> {
        debug_assert_eq!(trait_tok.ty, TokenType::Keyword(Keyword::Trait));
        let generics = self.parse_optional_generics()?.map_or(Vec::new(), |g| g.1);
        self.toks.step_expect(TokenType::LBrace)?;
        let mut functions = dmap::new();
        loop {
            let next = self.toks.step()?;
            match_or_unexpected! {next, self.toks.module,
                TokenType::RBrace = TokenType::RBrace => break,
                TokenType::Ident = TokenType::Ident => {
                    let name = next.get_val(self.src).to_owned();
                    let name_span = next.span();
                    self.toks.step_expect(TokenType::DoubleColon)?;
                    let fn_tok = self.toks.step_expect(TokenType::Keyword(Keyword::Fn))?;
                    let mut func = self.parse_function_header(fn_tok)?;
                    if matches!(
                        self.toks.peek().map(|t| t.ty),
                        Some(TokenType::Colon | TokenType::LBrace)
                    ) {
                        func.body = self.parse_function_body(&mut func.counts)?
                            .map(|body| self.ast.expr(body));
                    }
                    let previous = functions.insert(name, (name_span, func));
                    if previous.is_some() {
                        return Err(CompileError::new(
                            Error::DuplicateDefinition,
                            name_span.in_mod(self.toks.module)
                        ))
                    }
                }
            }
        }

        Ok(TraitDefinition {
            generics,
            functions,
        })
    }

    fn parse_trait_impl(&mut self, impl_tok: Token) -> ParseResult<TraitImpl> {
        debug_assert_eq!(impl_tok.ty, TokenType::Keyword(Keyword::Impl));
        let impl_generics = self.parse_optional_generics()?;
        let trait_path = self.parse_path()?;
        let trait_generics = self.parse_optional_generic_instance()?;
        self.toks.step_expect(TokenType::Keyword(Keyword::For))?;
        let ty = self.parse_type()?;

        let mut functions = dmap::new();

        self.toks.step_expect(TokenType::LBrace)?;
        self.parse_delimited(TokenType::Comma, TokenType::RBrace, |p| {
            let name = p.toks.step_expect(TokenType::Ident)?;
            let name_span = name.span();
            let name = name.get_val(p.src).to_owned();
            p.toks.step_expect(TokenType::DoubleColon)?;
            let fn_tok = p.toks.step_expect(TokenType::Keyword(Keyword::Fn))?;
            let func = p.parse_function_def(fn_tok)?;
            let func_id = p.ast.add_func(func);
            let previous = functions.insert(name, func_id);
            if previous.is_some() {
                return Err(CompileError::new(
                    Error::DuplicateDefinition,
                    name_span.in_mod(p.toks.module)
                ));
            }
            Ok(Delimit::OptionalIfNewLine)
        })?;
        Ok(TraitImpl {
            impl_generics: impl_generics.map_or(Vec::new(), |g| g.1),
            trait_path,
            trait_generics,
            ty,
            functions,
            impl_keyword_start: impl_tok.start,
        })
    }

    fn parse_stmt(&mut self, ident_count: &mut Counts) -> ParseResult<ExprId> {
        let expr = self.parse_expr(ident_count)?;
        self.stmt_postfix(expr, ident_count)
    }

    fn parse_stmt_starting_with(&mut self, expr: ExprId, ident_count: &mut Counts) -> ParseResult<Expr> {
        let lhs = self.parse_factor_postfix(expr, true, ident_count)?;
        let expr = self.parse_bin_op_rhs(0, lhs, ident_count)?;
        self.stmt_postfix(expr, ident_count)
    }

    fn stmt_postfix(&mut self, expr: ExprId, ident_count: &mut Counts) -> ParseResult<ExprId> {
        let expr = if self.toks.step_if(TokenType::Colon).is_some() {
            let annotated_ty = self.parse_type()?;
            match self.toks.step_if(TokenType::Equals) {
                Some(_) => Expr::DeclareWithVal {
                    pat: expr,
                    annotated_ty,
                    val: self.parse_expr(ident_count)?,
                },
                None => Expr::Declare {
                    pat: expr,
                    annotated_ty,
                }
            }
            
        } else if let Some(declare) = self.toks.step_if(TokenType::Declare) {
            Expr::DeclareWithVal {
                pat: expr,
                annotated_ty: UnresolvedType::Infer(declare.start),
                val: self.parse_expr(ident_count)?
            }
        } else {
            return Ok(expr);
        };
        Ok(self.ast.expr(expr))
    }

    fn parse_expr(&mut self, counts: &mut Counts) -> ParseResult<Expr> {
        let lhs = self.parse_factor(true, counts)?;
        self.parse_bin_op_rhs(0, lhs, counts)
    }

    

    fn parse_factor(&mut self, include_as: bool, counts: &mut Counts) -> ParseResult<Expr> {
        let first = self.toks.step()?;
        let start = first.start;
        let expr = match_or_unexpected_value!(first,
            self.toks.module, ExpectedTokens::Expr,
            TokenType::Keyword(Keyword::Fn) => {
                let func = self.parse_function_def(first)?;
                Expr::Function { id: self.ast.function(func) }
            },
            TokenType::LBrace => {
                let block = self.parse_block_from_lbrace(first, counts)?;
                return Ok(self.parse_factor_postfix(block, true, counts)?);
            },
            TokenType::LBracket => {
                let mut elems = Vec::new();
                let closing = self.parse_delimited(TokenType::Comma, TokenType::RBracket, |p| {
                    elems.push(p.parse_expr(counts)?);
                    Ok(())
                })?;
                Expr::Array(TSpan::new(start, closing.end), self.ast.exprs(elems))
            },
            TokenType::LParen => {
                if let Some(closing) = self.toks.step_if(TokenType::RParen) {
                    Expr::Unit(TSpan::new(start, closing.end))
                } else {
                    let expr = self.parse_expr(counts)?;
                    let after_expr = self.toks.step()?;
                    match_or_unexpected! { after_expr, self.toks.module,
                        TokenType::RParen = TokenType::RParen
                        => Expr::Nested(TSpan::new(start, after_expr.end), self.ast.expr(expr)),
                        TokenType::Comma = TokenType::Comma => {
                            // tuple
                            let mut elems = vec![expr];
                            let end = self.parse_delimited(TokenType::Comma, TokenType::RParen, |p| {
                                elems.push(p.parse_expr(counts)?);
                                Ok(())
                            })?.end;
                            Expr::Tuple(TSpan::new(start, end), self.ast.exprs(elems))
                        }
                    }
                }
            },
            TokenType::Minus => Expr::UnOp(start, UnOp::Neg, self.ast.expr(self.parse_factor(false, counts)?)),
            TokenType::Bang => Expr::UnOp(start, UnOp::Not, self.ast.expr(self.parse_factor(false, counts)?)),
            TokenType::Ampersand => Expr::UnOp(start, UnOp::Ref, self.ast.expr(self.parse_factor(false, counts)?)),
            TokenType::Keyword(Keyword::Ret) => {
                if self.toks.more_on_line() {
                    let val = self.ast.expr(self.parse_expr(counts)?);
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
            TokenType::Ident => Expr::Variable { span: first.span(), id: counts.ident() },
            TokenType::Underscore => Expr::Hole(first.start),
            TokenType::Keyword(Keyword::If) => {
                let cond = self.ast.expr(self.parse_expr(counts)?);
                let pat_value = self.toks.step_if(TokenType::Declare).map(|_| {
                    Ok(self.ast.expr(self.parse_expr(counts)?))
                }).transpose()?;
                let then = self.ast.expr(self.parse_block_or_expr(counts)?);

                let else_ = if let Some(tok) = self.toks.peek() {
                    if tok.ty == TokenType::Keyword(Keyword::Else) {
                        let tok = self.toks.step_assert(TokenType::Keyword(Keyword::Else));
                        let else_pos = tok.end;
                        self.toks.peek()
                            .ok_or_else(|| Error::UnexpectedEndOfFile.at(else_pos, else_pos, self.toks.module))?;

                        Some(self.ast.expr(self.parse_expr(counts)?))
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
                let val = self.ast.expr(self.parse_expr(counts)?);
                let lbrace = self.toks.step_expect(TokenType::LBrace)?;

                let mut branches = Vec::new();
                let rbrace = self.parse_delimited(TokenType::Comma, TokenType::RBrace, |p| {
                    let pat = p.parse_expr(counts)?;
                    let next = p.toks.step()?;
                    let (branch, delimit) = match_or_unexpected!{next, p.toks.module,
                        TokenType::Colon = TokenType::Colon => {
                            (p.parse_expr(counts)?, Delimit::Yes)
                        },
                        TokenType::LBrace = TokenType::LBrace => {
                            (p.parse_block_from_lbrace(next, counts)?, Delimit::Optional)
                        }
                    };
                    branches.extend([pat, branch]);
                    Ok(delimit)
                })?;
                let extra_branches = self.ast.exprs(branches).idx;
                debug_assert_eq!(branches.len() % 2, 0);
                let branch_count = (branches.len() / 2) as u32;
                Expr::Match {
                    span: TSpan::new(lbrace.start, rbrace.end),
                    val,
                    extra_branches,
                    branch_count,
                }
            },
            TokenType::Keyword(Keyword::While) => self.parse_while_from_cond(first, counts)?,
            TokenType::Keyword(Keyword::Primitive(p)) => todo!("handle primitive exprs"),
            TokenType::Keyword(Keyword::Root) => {
                Expr::Root(start)
            },
            TokenType::Dot => {
                let tok = self.toks.step()?;
                match_or_unexpected! {tok, self.toks.module,
                    TokenType::Ident = TokenType::Ident => {
                        let (args, end) = self.parse_enum_args(counts)?;
                        let args = self.ast.add_extra(&args);
                        let span = TSpan::new(start, end.unwrap_or(tok.end));
                        Expr::EnumLiteral { span, ident: tok.span(), args }
                    },
                    TokenType::LBrace = TokenType::LBrace => {
                        self.parse_record(tok, counts)?
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
                    args.push(self.parse_expr(counts)?);
                };
                Expr::Asm { span: TSpan::new(start, end), asm_str_span, args: self.ast.add_extra(&args) }
            }
        );
        let expr = self.ast.add_expr(expr);
        self.parse_factor_postfix(expr, include_as, counts)
    }

    fn parse_factor_postfix(&mut self, mut expr: Expr, include_as: bool, ident_count: &mut Counts) -> ParseResult<Expr> {
        loop {
            expr = match self.toks.peek().map(|t| t.ty) {
                Some(TokenType::LParen) => {
                    if !self.toks.more_on_line() {
                        // LParen is on new line, ignore
                        break Ok(expr);
                    }
                    self.toks.step_assert(TokenType::LParen);

                    // function call
                    let mut args = Vec::new();
                    let end = self
                        .parse_delimited(TokenType::Comma, TokenType::RParen, |p| {
                            args.push(p.parse_expr(ident_count)?);
                            Ok(())
                        })?
                        .end;
                    let args = self.ast.exprs(args);
                    let call = self.ast.call(ast::Call {
                        called_expr: self.ast.expr(expr),
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
                    let idx = self.ast.expr(self.parse_expr(ident_count)?);

                    let end = self.toks.step_expect(TokenType::RBracket)?.end;

                    Expr::Index { expr: self.ast.expr(expr), idx, end }
                }
                Some(TokenType::Dot) => {
                    let dot = self.toks.step_assert(TokenType::Dot);
                    let tok = self.toks.step()?;
                    match_or_unexpected! {tok, self.toks.module,
                        TokenType::Ident = TokenType::Ident => {
                            Expr::MemberAccess { left: self.ast.expr(expr), name: tok.span(), }
                        },
                        TokenType::IntLiteral = TokenType::IntLiteral => {
                            let idx = self.src[tok.span().range()].parse().unwrap();
                            Expr::TupleIdx { expr: self.ast.expr(expr), idx, end: tok.end }
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
                    let span =
                        TSpan::new(expr.start(self.ast), self.toks.current_end_pos());
                    let target_ty = self.parse_type()?;
                    Expr::Cast(span, target_ty, self.ast.expr(expr))
                }
                _ => break Ok(expr),
            };
        }
    }

    fn parse_bin_op_rhs(&mut self, expr_prec: u8, mut lhs: Expr, ident_count: &mut Counts) -> ParseResult<Expr> {
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
            let mut rhs = self.parse_factor(true, ident_count)?;

            // If BinOp binds less tightly with RHS than the operator after RHS, let
            // the pending operator take RHS as its LHS.
            if let Some(next_op) = self
                .toks
                .peek()
                .and_then(|t| Option::<Operator>::from(t.ty))
            {
                if op_prec < next_op.precedence() {
                    rhs = self.parse_bin_op_rhs(op.precedence() + 1, rhs, ident_count)?;
                }
            }
            lhs = Expr::BinOp(op, self.ast.expr(lhs), self.ast.expr(rhs));
        }
        Ok(lhs)
    }

    /// Starts after the while keyword has already been parsed
    fn parse_while_from_cond(&mut self, while_tok: Token, ident_count: &mut Counts) -> ParseResult<Expr> {
        debug_assert_eq!(while_tok.ty, TokenType::Keyword(Keyword::While));
        let cond = self.ast.expr(self.parse_expr(ident_count)?);
        if self.toks.step_if(TokenType::Declare).is_some() {
            let val = self.ast.expr(self.parse_expr(ident_count)?);
            let body = self.ast.expr(self.parse_block_or_expr(ident_count)?);
            Ok(Expr::WhilePat {
                start: while_tok.start,
                pat: cond,
                val,
                body,
            })
        } else {
            let body = self.ast.expr(self.parse_block_or_expr(ident_count)?);
            Ok(Expr::While {
                start: while_tok.start,
                cond,
                body,
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
                if let Some(rparen) = self.toks.step_if(TokenType::RParen) {
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
            TokenType::Underscore => Ok(UnresolvedType::Infer(type_tok.start))
        )
    }

    fn parse_optional_generics(&mut self) -> Result<Option<(TSpan, Vec<GenericDef>)>, CompileError> {
        self.toks
            .step_if(TokenType::LBracket)
            .map(|l| {
                let mut generics = Vec::new();
                let r = self.parse_delimited(TokenType::Comma, TokenType::RBracket, |p| {
                    let name = p.toks.step_expect(TokenType::Ident)?.span();
                    let mut requirements = Vec::new();
                    if p.toks.step_if(TokenType::Colon).is_some() {
                        loop {
                            requirements.push(p.parse_path()?);
                            if p.toks.step_if(TokenType::Plus).is_none() { break }
                        }
                        p.toks.step_if(TokenType::Ident);
                    }
                    generics.push(GenericDef { name, requirements });
                    Ok(Delimit::OptionalIfNewLine)
                })?;
                Ok((TSpan::new(l.start, r.end), generics))
            })
            .transpose()
    }

    fn parse_optional_generic_instance(
        &mut self,
    ) -> ParseResult<Option<(Vec<UnresolvedType>, TSpan)>> {
        self.toks
            .step_if(TokenType::LBracket)
            .map(|l_bracket| {
                let mut types = Vec::new();
                let r_bracket =
                    self.parse_delimited(TokenType::Comma, TokenType::RBracket, |p| {
                        types.push(p.parse_type()?);
                        Ok(())
                    })?;
                Ok((types, TSpan::new(l_bracket.start, r_bracket.end)))
            })
            .transpose()
    }

    /// parses optional arguments of an enum and returns them and the end position if arguments are
    /// present.
    fn parse_enum_args(&mut self, counts: &mut Counts) -> ParseResult<(Vec<Expr>, Option<u32>)> {
        let mut args = vec![];
        let end = self.toks.peek().is_some_and(|tok| tok.ty == TokenType::LParen && !tok.new_line).then(|| {
            self.toks.step_assert(TokenType::LParen);
            self.parse_delimited(TokenType::Comma, TokenType::RParen, |p| {
                args.push(p.parse_expr(counts)?);
                Ok(Delimit::OptionalIfNewLine)
            }).map(|end_tok| end_tok.end)
        }).transpose()?;

        Ok((args, end))
    }
}
