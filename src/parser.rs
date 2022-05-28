use std::collections::HashMap;
use crate::{
    ast::*,
    error::{CompileError, EyeResult, Error},
    lexer::{tokens::{Keyword, Token, TokenType, Operator}, Span},
    types::Primitive
};

pub struct Parser<'a> {
    src: &'a str,
    toks: Tokens,
    ast: &'a mut Ast
}

struct Tokens {
    tokens: Vec<Token>,
    index: usize,
    len: usize,
    module: ModuleId
}

impl Tokens {
    fn current(&self) -> Result<&Token, CompileError> {
        if self.index < self.len {
            Ok(&self.tokens[self.index])
        } else {
            let end = self.last_src_pos();
            Err(CompileError {
                err: Error::UnexpectedEndOfFile,
                span: Span::new(end, end, self.module)
            })
        }
    }
    fn previous(&self) -> Option<&Token> {
        (self.index > 0).then(|| &self.tokens[self.index - 1])
    }

    pub fn last_src_pos(&self) -> u32 {
        self.tokens.last().map_or(0, |tok| tok.end)
    }

    fn current_end_pos(&self) -> u32 {
        self.current()
            .map(|tok| tok.end)
            .ok()
            .or_else(|| self.tokens.last().map(|last| last.end))
            .unwrap_or(0)
    }

    pub fn _position(&self) -> usize {
        self.index
    }

    /// steps over the current token and returns it
    pub fn step(&mut self) -> Result<&Token, CompileError> {
        self.index += 1;
        if self.index <= self.len { // <= because we are only getting the previous token
            Ok(&self.tokens[self.index - 1])
        } else {
            let end = self.last_src_pos();
            Err(CompileError {
                err: Error::UnexpectedEndOfFile,
                span: Span::new(end, end, self.module),
            })
        }
    }

    /// steps over the current token and returns it. Token type checks only happen in debug mode.
    /// This should only be used if the type is known.
    pub fn step_assert(&mut self, ty: impl Into<TokenType>) -> &Token {
        let tok = self.step().expect("step_assert failed");
        debug_assert_eq!(tok.ty, ty.into());
        tok
    }

    pub fn step_expect<const N: usize, T: Into<TokenTypes<N>>>(&mut self, expected: T)
    -> Result<&Token, CompileError> {
        let expected = expected.into().0;
        let module = self.module;
        let tok = self.step()?;
        if !expected.iter().any(|expected_tok| *expected_tok == tok.ty) {
            return Err(CompileError {
                err: Error::UnexpectedToken,
                span: Span::new(tok.start, tok.end, module)
            });
        }
        Ok(tok)
    }

    pub fn step_if<const N: usize, T: Into<TokenTypes<N>>>(&mut self, expected: T) -> Option<&Token> {
        if let Some(next) = self.peek() {
            next.is(expected).then(|| self.step().unwrap())
        } else {
            None
        }
    }

    pub fn peek(&self) -> Option<&Token> {
        if self.index < self.tokens.len() {
            Some(&self.tokens[self.index])
        } else {
            None
        }
    }
}

macro_rules! match_or_unexpected {
    ($tok_expr: expr, $module: expr, $($match_arm: pat => $res: expr),*) => {{
        let tok = $tok_expr;
        match tok.ty {
            $($match_arm => $res,)*
            _ => return Err(CompileError {
                err:  Error::UnexpectedToken, // (tok.ty, vec![$(String::from(stringify!($match_arm)), )*]),
                span: Span::new(tok.start, tok.end, $module),
            })
        }
    }};
}

pub struct TokenTypes<const N: usize>(pub [TokenType; N]);
impl From<TokenType> for TokenTypes<1> {
    fn from(x: TokenType) -> Self {
        Self([x])
    }
}
impl<const N: usize> From<[TokenType; N]> for TokenTypes<N> {
    fn from(x: [TokenType; N]) -> Self {
        Self(x)
    }
}

impl<'a> Parser<'a> {
    pub fn new(tokens: Vec<Token>, src: &'a str, ast: &'a mut Ast, module: ModuleId) -> Self {
        let len = tokens.len();
        Self { src, toks: Tokens { tokens, index: 0, len, module }, ast }
    }

    pub fn parse(&mut self) -> Result<Module, CompileError> {
        self.parse_module()
    }

    fn parse_module(&mut self) -> Result<Module, CompileError> {
        let mut definitions = HashMap::new();
        let mut uses = Vec::new();
        
        while self.toks.index < self.toks.len {
            let start = self.toks.current().unwrap().start;
            match self.parse_item()? {
                Item::Definition(name, def) => if let Some(_existing) = definitions.insert(name, def) {
                    return Err(Error::DuplicateDefinition.at(
                        start,
                        self.toks.current().unwrap().end,
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
        definitions.shrink_to_fit();
        uses.shrink_to_fit();
        Ok(Module { definitions, uses })
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
        let start = self.toks.step_expect(TokenType::LBrace)?.start;
        self.parse_block_from_lbrace(start)
    }

    fn parse_block_from_lbrace(&mut self, start: u32) -> EyeResult<ExprRef> {
        let mut defs = HashMap::new();
        let mut items = Vec::new();

        while self.toks.current()?.ty != TokenType::RBrace {
            let start = self.toks.current().unwrap().start;
            match self.parse_item()? {
                Item::Definition(name, def) => if let Some(_existing) = defs.insert(name, def) {
                    let end = self.toks.current().unwrap().end;
                    return Err(Error::DuplicateDefinition.at(start, end, self.toks.module));
                }
                Item::Expr(item) => items.push(item),
            }
        }
        let end = self.toks.step_expect(TokenType::RBrace)?.end;
        let items = self.ast.extra(&items);
        let defs = self.ast.expr_builder.defs(defs);
        
        Ok(self.ast.add_expr(Expr::Block { span: TSpan::new(start, end), items, defs }))
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
                Item::Definition(
                    last.0.to_owned(),
                    Definition::Use(path)
                )
            }
            // function definition
            TokenType::Keyword(Keyword::Fn) => {
                self.toks.step_assert(Keyword::Fn);
                let name_tok = self.toks.step_expect(TokenType::Ident)?;
                let name = name_tok.get_val(self.src).to_owned();
                
                let mut params = Vec::new();
                let mut varargs = false;

                if self.toks.step_if(TokenType::LParen).is_some() { 
                    let mut first = true;
                    if self.toks.step_if(TokenType::RParen).is_none() {
                        'param_loop: loop {
                            if first {
                                first = false;
                            } else {
                                match_or_unexpected!{ self.toks.step()?, self.toks.module,
                                    TokenType::RParen => break 'param_loop,
                                    TokenType::Comma => ()
                                }
                                if self.toks.step_if(TokenType::TripleDot).is_some() {
                                    varargs = true;
                                    self.toks.step_expect(TokenType::RParen)?;
                                    break 'param_loop;
                                }
                                if self.toks.step_if(TokenType::RParen).is_some() {
                                    break 'param_loop
                                }
                            }
                            let name_tok = self.toks.step_expect(TokenType::Ident)?;
                            let name = name_tok.get_val(self.src).to_owned();
                            let (s, e) = (name_tok.start, name_tok.end);
                            let ty = self.parse_type()?;
                            params.push((name, ty, s, e));
                        }
                    }
                }
                let cur_tok = self.toks.peek().ok_or_else(|| CompileError {
                        err: Error::UnexpectedEndOfFile,
                        span: Span::new(self.toks.last_src_pos(), self.toks.last_src_pos(), self.toks.module)
                    })?;
                let (return_type, body) = match cur_tok.ty {
                    TokenType::LBrace => {
                        (
                            UnresolvedType::Primitive(Primitive::Unit, TSpan::new(cur_tok.start, cur_tok.start)),
                            Some(self.parse_block()?)
                        )
                    }
                    TokenType::Colon => {
                        let cur_tok = self.toks.step_assert(TokenType::Colon);
                        (
                            UnresolvedType::Primitive(Primitive::Unit, TSpan::new(cur_tok.start, cur_tok.start)),
                            Some(self.parse_expr()?)
                        )
                    }
                    TokenType::Keyword(Keyword::Extern) => {
                        let cur_tok = self.toks.step_assert(TokenType::Keyword(Keyword::Extern));
                        (
                            UnresolvedType::Primitive(Primitive::Unit, TSpan::new(cur_tok.start, cur_tok.start)),
                            None
                        )
                    }
                    _ => {
                        let return_type = self.parse_type()?;
                        let body = self.toks.step_if(TokenType::Keyword(Keyword::Extern))
                            .is_none()
                            .then(|| self.parse_block_or_expr())
                            .transpose()?;
                        (return_type, body)
                    }
                };
                Item::Definition(name, Definition::Function(Function {
                    params,
                    varargs,
                    return_type,
                    body
                }))
            }
            // either a struct or a variable
            TokenType::Ident => {
                let ident = self.toks.step_expect(TokenType::Ident)?;
                let ident_span = ident.span();
                let name = ident.get_val(self.src);
                match self.toks.peek().map(|t| t.ty) {
                    // Struct definition
                    Some(TokenType::DoubleColon) => {
                        self.toks.step_assert(TokenType::DoubleColon);
                        self.toks.step_expect(TokenType::LBrace)?;
                        let mut members: Vec<(String, UnresolvedType, u32, u32)> = Vec::new();
                        while self.toks.current()?.ty != TokenType::RBrace {
                            let start = self.toks.current().unwrap().start;
                            let member_name = self.toks.step_expect(TokenType::Ident)?.get_val(self.src);
                            let member_type = self.parse_type()?;
                            let end = self.toks.previous().unwrap().end;
                            if self.toks.current()?.ty == TokenType::Comma {
                                self.toks.step()?;
                            }
                            members.push((member_name.to_owned(), member_type, start, end));
                        }
                        self.toks.step_expect(TokenType::RBrace)?;
                        Item::Definition(
                            name.to_owned(),
                            Definition::Struct(StructDefinition { members })
                        )
                    }
                    // Variable declaration with explicit type
                    Some(TokenType::Colon) => {
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
                        let decl_start = self.toks.step_assert(TokenType::Declare).start;
                        let val = self.parse_expr()?;
                        
                        Item::Expr(self.ast.add_expr(Expr::DeclareWithVal {
                            name: ident_span,
                            annotated_ty: UnresolvedType::Infer(decl_start),
                            val
                        }))
                    }
                    _ => {
                        let var = self.ast.add_expr(Expr::Variable(ident_span));
                        let expr = self.parse_expr_starting_with(var)?;
                        Item::Expr(expr)
                    }
                }
            }
            _ => Item::Expr(self.parse_expr()?)
        })
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
                let block = self.parse_block_from_lbrace(start)?;
                return self.parse_factor_postfix(block, true);
            },
            TokenType::LBracket => {
                let mut elems = Vec::new();
                let closing = loop {
                    if let Some(r) = self.toks.step_if(TokenType::RBracket) { break r; }
                    elems.push(self.parse_expr()?);
                    let next = self.toks.step()?;
                    match next.ty {
                        TokenType::RBracket => break next,
                        TokenType::Comma => (),
                        _ => return Err(CompileError::new(
                            Error::UnexpectedToken,
                            next.span().in_mod(self.toks.module)
                        ))
                    }
                };
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
                            let end = loop {
                                if let Some(r) = self.toks.step_if(TokenType::RParen) { break r.end }
                                elems.push(self.parse_expr()?);
                                let after_expr = self.toks.step()?;
                                match_or_unexpected! {after_expr, self.toks.module,
                                    TokenType::RParen => break after_expr.end,
                                    TokenType::Comma => {}
                                }
                            };
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
            TokenType::Keyword(Keyword::While) => self.parse_while_from_cond(start)?,
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
                    let end = match self.toks.step_if(TokenType::RParen) {
                        None => loop {
                            args.push(self.parse_expr()?);
                            let step = self.toks.step()?;
                            match_or_unexpected!(step,
                                self.toks.module,
                                TokenType::Comma => (),
                                TokenType::RParen => break step.end
                            );
                        }
                        Some(rparen) => rparen.end
                    };
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
            self.toks.step().unwrap(); // op
            let op_prec = op.precedence();
            if op_prec < expr_prec { break; }
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
    fn parse_while_from_cond(&mut self, start: u32) -> EyeResult<Expr> {
        let cond = self.parse_expr()?;
        let body = self.parse_block_or_expr()?;
        Ok(Expr::While { start, cond, body })
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
                    self.parse_rest_of_path(s, e)?
                ))
            },
            TokenType::Ident => {
                let (s, e) = (type_tok.start, type_tok.end);
                Ok(UnresolvedType::Unresolved(self.parse_rest_of_path(s, e)?))
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
                let rparen_end = loop {
                    tuple_types.push(self.parse_type()?);
                    let comma_or_rparen = self.toks.step()?;
                    match_or_unexpected! {comma_or_rparen, self.toks.module,
                        TokenType::Comma => {},
                        TokenType::RParen => {
                            println!("RPAREN");
                            break comma_or_rparen.end
                        }
                    }
                };
                Ok(UnresolvedType::Tuple(tuple_types, TSpan::new(lparen_start, rparen_end)))
                
            },
            TokenType::LBracket => {
                let start = type_tok.start;
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
                Ok(UnresolvedType::Array(Box::new((elem_ty, TSpan::new(start, end), count))))
            },
            TokenType::Star => {
                let start = type_tok.start;
                Ok(UnresolvedType::Pointer(Box::new((self.parse_type()?, start))))
            },
            TokenType::Underscore => Ok(UnresolvedType::Infer(type_tok.start))
        )
    }
}