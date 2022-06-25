use std::collections::HashMap;
use crate::{
    ast::*,
    error::{CompileError, EyeResult, Error},
    lexer::tokens::{Keyword, Token, TokenType, Operator},
    types::Primitive, span::{TSpan, Span}
};

mod tokens;
use tokens::*;
pub use tokens::TokenTypes;

pub struct Parser<'a> {
    src: &'a str,
    toks: Tokens,
    ast: &'a mut Ast
}


impl<'a> Parser<'a> {
    pub fn new(tokens: Vec<Token>, src: &'a str, ast: &'a mut Ast, module: ModuleId) -> Self {
        Self { src, toks: Tokens::new(tokens, module), ast }
    }

    pub fn parse(&mut self) -> Result<Module, CompileError> {
        self.parse_module()
    }

    /// Parses a delimited list. The `item` function parses an item and is supposed to handle the result itself.
    /// `delim` is a delimiter. Trailing delimiters are allowed, but optional here.
    /// `end` is the ending token. It will be returned from this function once parsed.
    fn parse_delimited<F, D>(&mut self, delim: TokenType, end: TokenType, mut item: F) -> Result<Token, CompileError>
    where
        F: FnMut(&mut Parser) -> Result<D, CompileError>,
        D: Into<Delimit>,
    {
        loop {
            if let Some(end_tok) = self.toks.step_if(end) { return Ok(end_tok) }
            let delimit = item(self)?.into();
            match delimit {
                Delimit::Yes => {
                    let delim_or_end = self.toks.step()?;
                    if delim_or_end.ty == delim { continue }
                    if delim_or_end.ty == end {
                        return Ok(delim_or_end)
                    }
                    return Err(CompileError::new(
                        Error::UnexpectedToken,
                        delim_or_end.span().in_mod(self.toks.module)
                    ))
                }
                Delimit::No => {}
                Delimit::Optional => { self.toks.step_if(delim); }
            }
        }
    }

    fn parse_module(&mut self) -> Result<Module, CompileError> {
        let mut definitions = HashMap::new();
        let mut uses = Vec::new();
        
        while !self.toks.is_at_end() {
            let start = self.toks.current().unwrap().start;
            match self.parse_item()? {
                Item::Definition { name, name_span, def } => if let Some(_existing) = definitions.insert(name, def) {
                    return Err(Error::DuplicateDefinition.at(
                        name_span.start,
                        name_span.end,
                        self.toks.module
                    ));
                }
                Item::Expr(_) => return Err(
                    CompileError {
                        err: Error::InvalidTopLevelBlockItem,
                        span: Span { start, end: self.toks.current_end_pos(), module: self.toks.module }
                    }
                )
            }
        }
        uses.shrink_to_fit();
        Ok(Module { definitions: self.ast.expr_builder.defs(definitions), uses })
    }

    fn parse_block_or_expr(&mut self) -> EyeResult<ExprRef> {
        match_or_unexpected!(
            self.toks.peek()
                .ok_or_else(|| Error::UnexpectedEndOfFile.at(
                    self.toks.last_src_pos(),
                    self.toks.last_src_pos(),
                    self.toks.module
                ))?,
            self.toks.module,
            TokenType::LBrace => self.parse_block(),
            TokenType::Colon => {
                self.toks.step_expect(TokenType::Colon)?;
                self.parse_expr()
            }
        )
    }

    fn parse_block(&mut self) -> EyeResult<ExprRef> {
        let lbrace = self.toks.step_expect(TokenType::LBrace)?;
        self.parse_block_from_lbrace(lbrace)
    }

    fn parse_block_from_lbrace(&mut self, lbrace: Token) -> EyeResult<ExprRef> {
        debug_assert_eq!(lbrace.ty, TokenType::LBrace);

        let mut defs = HashMap::new();
        let mut items = Vec::new();

        while self.toks.current()?.ty != TokenType::RBrace {
            let start = self.toks.current().unwrap().start;
            match self.parse_item()? {
                Item::Definition { name, name_span: _, def } => if let Some(_existing) = defs.insert(name, def) {
                    let end = self.toks.current().unwrap().end;
                    return Err(Error::DuplicateDefinition.at(start, end, self.toks.module));
                }
                Item::Expr(item) => items.push(item),
            }
        }
        let rbrace = self.toks.step_expect(TokenType::RBrace)?;
        let items = self.ast.extra(&items);
        let defs = self.ast.expr_builder.defs(defs);
        
        Ok(self.ast.add_expr(Expr::Block { span: TSpan::new(lbrace.start, rbrace.end), items, defs }))
    }

    fn parse_item(&mut self) -> Result<Item, CompileError> {
        let cur = self.toks.current()?;
        Ok(match cur.ty {
            // use statement
            TokenType::Keyword(Keyword::Use) => {
                self.toks.step_assert(TokenType::Keyword(Keyword::Use));
                let use_tok = self.toks.current().unwrap();
                let use_start = use_tok.start;
                let use_end = use_tok.end;
                
                let path = self.parse_path()?;
                let last = path.segments(self.src).2
                    .ok_or(CompileError {
                        err: Error::CantUseRootPath,
                        span: Span::new(use_start, use_end, self.toks.module)
                    })?;
                Item::Definition {
                    name: last.0.to_owned(),
                    name_span: last.1,
                    def: Definition::Use(path)
                }
            }
            // function definition
            TokenType::Keyword(Keyword::Fn) => {
                let fn_tok = self.toks.step_assert(Keyword::Fn);
                let (name, name_span, func) = self.parse_function_def(fn_tok)?;
                Item::Definition { name, name_span, def: Definition::Function(func) }
            }
            // trait definition
            TokenType::Keyword(Keyword::Trait) => {
                let trait_tok = self.toks.step_assert(Keyword::Trait);
                let (name, name_span, trait_) = self.parse_trait_def(trait_tok)?;
                Item::Definition { name, name_span, def: Definition::Trait(trait_) }
            }
            // either a struct, constant or a variable
            TokenType::Ident => {
                let ident = self.toks.step_expect(TokenType::Ident)?;
                let ident_span = ident.span();
                let name = ident.get_val(self.src);
                let generics = self.parse_optional_generics()?;
                match self.toks.peek().map(|t| t.ty) {
                    // Struct definition, constant or enum
                    Some(TokenType::DoubleColon) => {
                        self.toks.step_assert(TokenType::DoubleColon);
                        let def = if self.toks.step_if(TokenType::LBrace).is_some() {
                            let mut members: Vec<(String, UnresolvedType, u32, u32)> = Vec::new();
                            let mut methods = HashMap::new();
                            self.parse_delimited(TokenType::Comma, TokenType::RBrace, |p| {
                                let ident_or_fn = p.toks.step()?;
                                Ok(match_or_unexpected!{ident_or_fn, p.toks.module,
                                    TokenType::Ident => {
                                        let member_name = ident_or_fn.get_val(p.src);
                                        let member_type = p.parse_type()?;
                                        let end = member_type.span().end;
                                        members.push((member_name.to_owned(), member_type, ident.start, end));
                                        Delimit::Yes
                                    },
                                    TokenType::Keyword(Keyword::Fn) => {
                                        let (name, name_span, method) = p.parse_function_def(ident_or_fn)?;
                                        if let Some(_existing) = methods.insert(name, method) {
                                            return Err(CompileError::new(
                                                Error::DuplicateDefinition,
                                                name_span.in_mod(p.toks.module)
                                            ))
                                        }
                                        Delimit::No
                                    }
                                })
                            })?;
                            Definition::Struct(StructDefinition {
                                generics: generics.map_or(Vec::new(), |g| g.1),
                                members,
                                methods
                            })
                        } else if self.toks.step_if(TokenType::Keyword(Keyword::Enum)).is_some() {
                            self.toks.step_expect(TokenType::LBrace)?;
                            let mut variants = Vec::new();
                            while self.toks.step_if(TokenType::RBrace).is_none() {
                                let tok = self.toks.step_expect(TokenType::Ident)?;
                                let span = tok.span();
                                let variant = tok.get_val(self.src).to_owned();
                                variants.push((span, variant));
                            }
                            Definition::Enum(EnumDefinition {
                                generics: generics.map_or(Vec::new(), |g| g.1),
                                variants
                            })
                        } else {
                            Definition::Const(UnresolvedType::Infer(0), self.parse_expr()?)
                        };
                        Item::Definition { name: name.to_owned(), name_span: ident_span, def }
                    }
                    // Variable declaration with explicit type
                    Some(TokenType::Colon) => {
                        if let Some((span, _)) = generics {
                            return Err(CompileError::new(Error::UnexpectedGenerics, span.in_mod(self.toks.module)))
                        }
                        self.toks.step_assert(TokenType::Colon);
                        let ty = self.parse_type()?;
                        Item::Expr(if self.toks.step_if(TokenType::Equals).is_some() {
                            let val = self.parse_expr()?;
                            self.ast.add_expr(Expr::DeclareWithVal {
                                name: ident_span,
                                annotated_ty: ty,
                                val
                            })
                        } else {
                            self.ast.add_expr(Expr::Declare {
                                name: ident_span,
                                annotated_ty: ty,
                                end: self.toks.previous().unwrap().end
                            })
                        })
                    }
                    // Variable declaration with inferred type
                    Some(TokenType::Declare) => {
                        if let Some((span, _)) = generics {
                            return Err(CompileError::new(Error::UnexpectedGenerics, span.in_mod(self.toks.module)))
                        }
                        let decl_start = self.toks.step_assert(TokenType::Declare).start;
                        let val = self.parse_expr()?;
                        
                        Item::Expr(self.ast.add_expr(Expr::DeclareWithVal {
                            name: ident_span,
                            annotated_ty: UnresolvedType::Infer(decl_start),
                            val
                        }))
                    }
                    _ => {
                        if let Some((span, _)) = generics {
                            return Err(CompileError::new(Error::UnexpectedGenerics, span.in_mod(self.toks.module)))
                        }
                        let var = self.ast.add_expr(Expr::Variable(ident_span));
                        let expr = self.parse_expr_starting_with(var)?;
                        Item::Expr(expr)
                    }
                }
            }
            _ => Item::Expr(self.parse_expr()?)
        })
    }

    fn parse_function_def(&mut self, fn_tok: Token) -> EyeResult<(String, TSpan, Function)> {
        let (name, name_span, mut func) = self.parse_function_header(fn_tok)?;
        func.body = self.parse_function_body()?;

        Ok((name, name_span, func))
    }

    /// Will just return a function with the body always set to `None`
    fn parse_function_header(&mut self, fn_tok: Token) -> EyeResult<(String, TSpan, Function)> {
        debug_assert_eq!(fn_tok.ty, TokenType::Keyword(Keyword::Fn));
        let name_tok = self.toks.step_expect(TokenType::Ident)?;
        let name = name_tok.get_val(self.src).to_owned();
        let name_span = name_tok.span();
        
        let generics = self.parse_optional_generics()?.map_or(Vec::new(), |g| g.1);
        
        let mut params = Vec::new();
        let mut varargs = false;

        if self.toks.step_if(TokenType::LParen).is_some() { 
            self.parse_delimited(TokenType::Comma, TokenType::RParen, |p| {
                if varargs {
                    let tok = p.toks.step()?;
                    // no further tokens after varargs are allowed
                    return Err(Error::UnexpectedToken.at(tok.start, tok.end, p.toks.module));
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
        //FIXME: this is a pretty ugly hack for determining wether to parse a type
        let return_type = if matches!(
            self.toks.peek().map(|tok| tok.ty),
            Some(
                TokenType::LBrace | TokenType::Colon | TokenType::Keyword(Keyword::Extern)
                | TokenType::Keyword(Keyword::Fn) | TokenType::RBrace
            )
        ) {
            UnresolvedType::Primitive(Primitive::Unit, self.toks.previous().unwrap().span())
        } else {
            self.parse_type()?
        };
        Ok((name, name_span, Function {
            params,
            generics,
            varargs,
            return_type,
            body: None
        }))
    }

    fn parse_function_body(&mut self) -> EyeResult<Option<ExprRef>> {
        let first = self.toks.step()?;
        Ok(match_or_unexpected!{first, self.toks.module,
            TokenType::LBrace => Some(self.parse_block_from_lbrace(first)?),
            TokenType::Colon => {
                Some(self.parse_expr()?)
            },
            TokenType::Keyword(Keyword::Extern) => {
                None
            }
        })
    }

    fn parse_trait_def(&mut self, trait_tok: Token) -> EyeResult<(String, TSpan, TraitDefinition)> {
        debug_assert_eq!(trait_tok.ty, TokenType::Keyword(Keyword::Trait));
        let name_tok = self.toks.step_expect(TokenType::Ident)?;
        let name = name_tok.get_val(self.src).to_owned();
        let name_span = name_tok.span();
        
        let generics = self.parse_optional_generics()?.map_or(Vec::new(), |g| g.1);
        self.toks.step_expect(TokenType::LBrace)?;
        let mut functions = HashMap::new();
        loop {
            let next = self.toks.step()?;
            match_or_unexpected!{next, self.toks.module,
                TokenType::RBrace => break,
                TokenType::Keyword(Keyword::Fn) => {
                    let (name, name_span, mut func) = self.parse_function_header(next)?;
                    if matches!(
                        self.toks.peek().map(|t| t.ty),
                        Some(TokenType::Colon | TokenType::LBrace)
                    ) {
                        func.body = self.parse_function_body()?;
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
        
        Ok((name, name_span, TraitDefinition {
            generics,
            functions,
        }))
    }

    fn parse_expr(&mut self) -> EyeResult<ExprRef> {
        let lhs = self.parse_factor(true)?;
        self.parse_bin_op_rhs(0, lhs)
    }

    fn parse_expr_starting_with(&mut self, expr: ExprRef) -> Result<ExprRef, CompileError> {
        let lhs = self.parse_factor_postfix(expr, true)?;
        self.parse_bin_op_rhs(0, lhs)
    } 

    fn parse_factor(&mut self, include_as: bool) -> Result<ExprRef, CompileError> {
        let first = self.toks.step()?;
        let start = first.start;
        let expr = match_or_unexpected!(first,
            self.toks.module,
            TokenType::LBrace => {
                let block = self.parse_block_from_lbrace(first)?;
                return self.parse_factor_postfix(block, true);
            },
            TokenType::LBracket => {
                let mut elems = Vec::new();
                let closing = self.parse_delimited(TokenType::Comma, TokenType::RBracket, |p| {
                    elems.push(p.parse_expr()?);
                    Ok(())
                })?;
                Expr::Array(TSpan::new(start, closing.end), self.ast.extra(&elems))
            },
            TokenType::LParen => {
                if let Some(closing) = self.toks.step_if(TokenType::RParen) {
                    Expr::Unit(TSpan::new(start, closing.end))
                } else {
                    let expr = self.parse_expr()?;
                    let after_expr = self.toks.step()?;
                    match_or_unexpected! { after_expr, self.toks.module,
                        TokenType::RParen => Expr::Nested(TSpan::new(start, after_expr.end), expr),
                        TokenType::Comma => {
                            // tuple
                            let mut elems = vec![expr];
                            let end = self.parse_delimited(TokenType::Comma, TokenType::RParen, |p| {
                                elems.push(p.parse_expr()?);
                                Ok(())
                            })?.end;
                            Expr::Tuple(TSpan::new(start, end), self.ast.extra(&elems))
                        }
                    }
                }
            },
            TokenType::Minus => Expr::UnOp(start, UnOp::Neg, self.parse_factor(false)?),
            TokenType::Bang => Expr::UnOp(start, UnOp::Not, self.parse_factor(false)?),
            TokenType::Ampersand => Expr::UnOp(start, UnOp::Ref, self.parse_factor(false)?),
            TokenType::Keyword(Keyword::Ret) => Expr::Return { start, val: self.parse_expr()? },
            TokenType::IntLiteral => Expr::IntLiteral(first.span()),
            TokenType::FloatLiteral => Expr::FloatLiteral(first.span()),
            TokenType::StringLiteral => Expr::StringLiteral(TSpan::new(first.start, first.end)),
            TokenType::Keyword(Keyword::True) => Expr::BoolLiteral { start, val: true },
            TokenType::Keyword(Keyword::False) => Expr::BoolLiteral { start, val: false },
            TokenType::Ident => Expr::Variable(first.span()),
            TokenType::Keyword(Keyword::If) => {
                let cond = self.parse_expr()?;
                let then = self.parse_block_or_expr()?;
                
                let else_ = if let Some(tok) = self.toks.peek() {
                    if tok.ty == TokenType::Keyword(Keyword::Else) {
                        let tok = self.toks.step_assert(TokenType::Keyword(Keyword::Else));
                        let else_pos = tok.end;
                        self.toks.peek()
                            .ok_or_else(|| Error::UnexpectedEndOfFile.at(else_pos, else_pos, self.toks.module))?;
                        
                        Some(self.parse_expr()?)
                    } else { None }
                } else { None };

                if let Some(else_) = else_ {
                    Expr::IfElse { start, cond, then, else_ }
                } else {
                    Expr::If { start, cond, then }
                }
            },
            TokenType::Keyword(Keyword::While) => self.parse_while_from_cond(first)?,
            TokenType::Keyword(Keyword::Primitive(p)) => {
                let prim_span = first.span();
                let inner = self.parse_factor(false)?;
                Expr::Cast(
                    TSpan::new(start, self.toks.current_end_pos()),
                    UnresolvedType::Primitive(p, prim_span),
                    inner
                )
            },
            TokenType::Keyword(Keyword::Root) => {
                Expr::Root(start)
            },
            TokenType::Dot => {
                let ident = self.toks.step_expect(TokenType::Ident)?.span();
                Expr::EnumLiteral { dot: start, ident }
            }
        );
        let expr = self.ast.add_expr(expr);
        self.parse_factor_postfix(expr, include_as)
    }

    fn parse_factor_postfix(&mut self, mut expr: ExprRef, include_as: bool) -> EyeResult<ExprRef> {
        loop {
            let cur = match self.toks.peek().map(|t| t.ty) {
                Some(TokenType::LParen) => {
                    self.toks.step_assert(TokenType::LParen);
                    // function call
                    let mut args = Vec::new();
                    let end = self.parse_delimited(TokenType::Comma, TokenType::RParen, |p| {
                        args.push(p.parse_expr()?);
                        Ok(())
                    })?.end;
                    Expr::FunctionCall { func: expr, args: self.ast.extra(&args), end }
                }
                Some(TokenType::Dot) => {
                    self.toks.step_assert(TokenType::Dot);
                    let tok = self.toks.step()?;
                    match_or_unexpected!{tok, self.toks.module,
                        TokenType::Ident => {
                            Expr::MemberAccess { left: expr, name: tok.span() }
                        },
                        TokenType::IntLiteral => {
                            let idx = self.src[tok.span().range()].parse().unwrap();
                            Expr::TupleIdx { expr, idx, end: tok.end }
                        }
                    }
                }
                Some(TokenType::Caret) => {
                    self.toks.step_assert(TokenType::Caret);
                    Expr::UnOp(self.toks.current_end_pos(), UnOp::Deref, expr)
                }
                Some(TokenType::Keyword(Keyword::As)) if include_as => {
                    self.toks.step_assert(TokenType::Keyword(Keyword::As));
                    let span = TSpan::new(self.ast[expr].start(self.ast), self.toks.current_end_pos());
                    let target_ty = self.parse_type()?;
                    Expr::Cast(span, target_ty, expr)
                }
                _ => break Ok(expr)
            };
            expr = self.ast.add_expr(cur);
        }
    }

    fn parse_bin_op_rhs(&mut self, expr_prec: u8, mut lhs: ExprRef) -> EyeResult<ExprRef> {
        while let Some(op) = self.toks.peek().and_then(|t| Option::<Operator>::from(t.ty)) {
            let op_prec = op.precedence();
            if op_prec < expr_prec { break; }
            self.toks.step().unwrap(); // op
            let mut rhs = self.parse_factor(true)?;

            // If BinOp binds less tightly with RHS than the operator after RHS, let
            // the pending operator take RHS as its LHS.
            if let Some(next_op) = self.toks.peek().and_then(|t| Option::<Operator>::from(t.ty)) {
                if op_prec < next_op.precedence() {
                    rhs = self.parse_bin_op_rhs(op.precedence() + 1, rhs)?;
                }
            }
            lhs = self.ast.add_expr(Expr::BinOp(op, lhs, rhs));
        }
        Ok(lhs)
    }

    /// Starts after the while keyword has already been parsed
    fn parse_while_from_cond(&mut self, while_tok: Token) -> EyeResult<Expr> {
        debug_assert_eq!(while_tok.ty, TokenType::Keyword(Keyword::While));
        let cond = self.parse_expr()?;
        let body = self.parse_block_or_expr()?;
        Ok(Expr::While { start: while_tok.start, cond, body })
    }
    
    fn parse_path(&mut self) -> EyeResult<IdentPath> {
        let first = self.toks.step_expect([TokenType::Keyword(Keyword::Root), TokenType::Ident])?;
        let (s, e) = (first.start, first.end);
        self.parse_rest_of_path(s, e)
    }

    fn parse_rest_of_path(&mut self, start: u32, mut end: u32) -> EyeResult<IdentPath> {
        while self.toks.step_if(TokenType::Dot).is_some() {
            end = self.toks.step_expect(TokenType::Ident)?.end;
        }
        Ok(IdentPath::new(TSpan::new(start, end)))
    }

    fn parse_type(&mut self) -> EyeResult<UnresolvedType> {
        let type_tok = self.toks.step()?;
        match_or_unexpected!(type_tok,
            self.toks.module,
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
                Ok(UnresolvedType::Primitive(primitive, type_tok.span()))
            },
            TokenType::LParen => {
                let lparen_start = type_tok.start;
                if let Some(rparen) = self.toks.step_if(TokenType::RParen) {
                    return Ok(UnresolvedType::Primitive(Primitive::Unit, TSpan::new(lparen_start, rparen.end)))
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
                Ok(UnresolvedType::Array(Box::new((elem_ty, TSpan::new(type_tok.start, end), count))))
            },
            TokenType::Star => {
                Ok(UnresolvedType::Pointer(Box::new((self.parse_type()?, type_tok.start))))
            },
            TokenType::Bang => {
                Ok(UnresolvedType::Primitive(Primitive::Never, type_tok.span()))  
            },
            TokenType::Underscore => Ok(UnresolvedType::Infer(type_tok.start))
        )
    }

    fn parse_optional_generics(&mut self) -> Result<Option<(TSpan, Vec<TSpan>)>, CompileError> {
        self.toks.step_if(TokenType::LBracket).map(|l| {
            let mut generics = Vec::new();
            let r = self.parse_delimited(TokenType::Comma, TokenType::RBracket, |p| {
                generics.push(p.toks.step_expect(TokenType::Ident)?.span());
                Ok(())
            })?;
            Ok((TSpan::new(l.start, r.end), generics))
        }).transpose()
    }

    fn parse_optional_generic_instance(&mut self) -> EyeResult<Option<(Vec<UnresolvedType>, TSpan)>> {
        self.toks.step_if(TokenType::LBracket).map(|l_bracket| {
            let mut types = Vec::new();
            let r_bracket = self.parse_delimited(TokenType::Comma, TokenType::RBracket, |p| {
                types.push(p.parse_type()?);
                Ok(())
            })?;
            Ok((types, TSpan::new(l_bracket.start, r_bracket.end)))
        }).transpose()
    }
}