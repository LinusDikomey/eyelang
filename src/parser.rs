use std::collections::HashMap;
use crate::{
    ast::*,
    error::{CompileError, EyeResult, Error},
    lexer::{tokens::{Keyword, Token, TokenType, Operator}, Span},
    types::Primitive
};

pub struct Parser<'a> {
    src: &'a str,
    toks: Tokens
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

    pub fn position(&self) -> usize {
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
    pub fn new(tokens: Vec<Token>, src: &'a str, module: ModuleId) -> Self {
        let len = tokens.len();
        Self { src, toks: Tokens { tokens, index: 0, len, module } }
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
                Item::Block(_) => return Err(CompileError {
                    err: Error::InvalidTopLevelBlockItem,
                    span: Span::new(start, self.toks.current_end_pos(), self.toks.module)
                }),
                Item::Definition(name, def) => if let Some(_existing) = definitions.insert(name, def) {
                    return Err(Error::DuplicateDefinition.at(
                        start,
                        self.toks.current().unwrap().end,
                        self.toks.module
                    ));
                }
            }
        }
        definitions.shrink_to_fit();
        uses.shrink_to_fit();
        Ok(Module { definitions, uses })
    }

    fn parse_block_or_expr(&mut self) -> EyeResult<BlockOrExpr> {
        match_or_unexpected!(
            self.toks.peek()
                .ok_or_else(|| Error::UnexpectedEndOfFile.at(
                    self.toks.last_src_pos(),
                    self.toks.last_src_pos(),
                    self.toks.module
                ))?,
            self.toks.module,
            TokenType::LBrace => self.parse_block().map(BlockOrExpr::Block),
            TokenType::Colon => {
                self.toks.step_expect(TokenType::Colon)?;
                let expr = self.parse_expr()?;
                Ok(BlockOrExpr::Expr(expr))
            }
        )
    }

    fn parse_block(&mut self) -> EyeResult<Block> {
        self.toks.step_expect(TokenType::LBrace)?;
        let mut defs = HashMap::new();
        let mut uses = Vec::new();
        let mut items = Vec::new();

        while self.toks.current()?.ty != TokenType::RBrace {
            let start = self.toks.current().unwrap().start;
            match self.parse_item()? {
                Item::Block(item) => items.push(item),
                Item::Definition(name, def) => if let Some(_existing) = defs.insert(name, def) {
                    let end = self.toks.current().unwrap().end;
                    return Err(Error::DuplicateDefinition.at(start, end, self.toks.module));
                }
            }
        }
        self.toks.step_expect(TokenType::RBrace)?;
        items.shrink_to_fit();
        defs.shrink_to_fit();
        uses.shrink_to_fit();
        Ok( Block { items, defs, uses })
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
                let last = path.segments().2
                    .ok_or(CompileError {
                        err: Error::CantUseRootPath,
                        span: Span::new(use_start, use_end, self.toks.module)
                    })?;
                Item::Definition(last.clone(), Definition::Use(path))
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
                            // trailing comma
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
                let cur_tok = self.toks.peek().ok_or(CompileError {
                        err: Error::UnexpectedEndOfFile,
                        span: Span::new(self.toks.last_src_pos(), self.toks.last_src_pos(), self.toks.module)
                    })?;
                let (return_type, body) = match cur_tok.ty {
                    TokenType::LBrace => {
                        (
                            (UnresolvedType::Primitive(Primitive::Unit), cur_tok.start, cur_tok.end),
                            Some(BlockOrExpr::Block(self.parse_block()?))
                        )
                    }
                    TokenType::Colon => {
                        let cur_tok = self.toks.step_assert(TokenType::Colon);
                        (
                            (UnresolvedType::Primitive(Primitive::Unit), cur_tok.start, cur_tok.end),
                            Some(BlockOrExpr::Expr(self.parse_expr()?)))
                    }
                    TokenType::Keyword(Keyword::Extern) => {
                        let cur_tok = self.toks.step_assert(TokenType::Keyword(Keyword::Extern));
                        (
                            (UnresolvedType::Primitive(Primitive::Unit), cur_tok.start, cur_tok.end),
                            None
                        )
                    }
                    _ => {
                        let r_s = self.toks.position() as u32;
                        let return_type = self.parse_type()?;
                        let r_e = self.toks.position() as u32;
                        let body = self.toks.step_if(TokenType::Keyword(Keyword::Extern))
                            .is_none()
                            .then(|| self.parse_block_or_expr())
                            .transpose()?;
                        ((return_type, r_s, r_e), body)
                    }
                };
                Item::Definition(name, Definition::Function(Function {
                    params,
                    varargs,
                    return_type,
                    body
                }))
            }
            // block
            TokenType::LBrace => Item::Block(BlockItem::Block(self.parse_block()?)),
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
                        let val = self.toks.step_if(TokenType::Equals)
                            .is_some()
                            .then(|| self.parse_expr()).transpose()?;
                        Item::Block(BlockItem::Declare(name.to_owned(), Some(ty), val))
                    }
                    // Variable declaration with inferred type
                    Some(TokenType::Declare) => {
                        self.toks.step_assert(TokenType::Declare);
                        let val = self.parse_expr()?;
                        Item::Block(BlockItem::Declare(name.to_owned(), None, Some(val)))
                    }
                    _ => {
                        let expr = self.parse_expr_starting_with(Expr::Variable(ident_span))?;
                        Item::Block(BlockItem::Expr(expr))
                    }
                }
            }
            _ => Item::Block(BlockItem::Expr(self.parse_expr()?))
        })
    }

    fn parse_expr(&mut self) -> EyeResult<Expr> {
        let lhs = self.parse_factor(true)?;
        self.parse_bin_op_rhs(0, lhs)
    }

    fn parse_expr_starting_with(&mut self, expr: Expr) -> Result<Expr, CompileError> {
        let lhs = self.parse_factor_postfix(expr, true)?;
        self.parse_bin_op_rhs(0, lhs)
    } 

    fn parse_factor(&mut self, include_as: bool) -> Result<Expr, CompileError> {
        let first = self.toks.step()?;
        let start = first.start;
        let expr = match_or_unexpected!(first,
            self.toks.module,
            TokenType::Minus => Expr::UnOp(Box::new((start, UnOp::Neg, self.parse_factor(false)?))),
            TokenType::Bang => Expr::UnOp(Box::new((start, UnOp::Not, self.parse_factor(false)?))),
            TokenType::Ampersand => Expr::UnOp(Box::new((start, UnOp::Ref, self.parse_factor(false)?))),
            TokenType::LParen => {
                if let Some(closing) = self.toks.step_if(TokenType::RParen) {
                    Expr::Unit(TSpan::new(start, closing.end))
                } else {
                    let inner = self.parse_expr()?;
                    let end = self.toks.step_expect(TokenType::RParen)?.end;
                    Expr::Nested(Box::new((TSpan::new(start, end), inner)))
                }
            },
            TokenType::Keyword(Keyword::Ret) => Expr::Return(Box::new((start, self.parse_expr()?))),
            TokenType::IntLiteral => Expr::IntLiteral(first.span()),
            TokenType::FloatLiteral => Expr::FloatLiteral(first.span()),
            TokenType::StringLiteral => Expr::StringLiteral(TSpan::new(first.start, first.end)),
            TokenType::Keyword(Keyword::True) => Expr::BoolLiteral { start, val: true },
            TokenType::Keyword(Keyword::False) => Expr::BoolLiteral { start, val: false },
            TokenType::Ident => Expr::Variable(first.span()),
            TokenType::Keyword(Keyword::If) => Expr::If(Box::new(self.parse_if_from_cond(start)?)),
            TokenType::Keyword(Keyword::While) => Expr::While(Box::new(self.parse_while_from_cond(start)?)),
            TokenType::Keyword(Keyword::Primitive(p)) => {
                let inner = self.parse_factor(false)?;
                Expr::Cast(Box::new((
                    TSpan::new(start, self.toks.current_end_pos()),
                    UnresolvedType::Primitive(p),
                    inner
                )))
            },
            TokenType::Keyword(Keyword::Root) => {
                Expr::Root(start)
            }
        );
        self.parse_factor_postfix(expr, include_as)
    }

    fn parse_factor_postfix(&mut self, mut expr: Expr, include_as: bool) -> EyeResult<Expr> {
        loop {
            expr = match self.toks.peek().map(|t| t.ty) {
                Some(TokenType::LParen) => {
                    // function call
                    self.toks.step_expect(TokenType::LParen)?;
                    let mut args = Vec::new();
                    if self.toks.step_if(TokenType::RParen).is_none() {
                        loop {
                            args.push(self.parse_expr()?);
                            match_or_unexpected!(self.toks.step()?,
                                self.toks.module,
                                TokenType::Comma => (),
                                TokenType::RParen => break
                            );
                        }
                    }
                    let end = self.toks.current_end_pos();
                    Expr::FunctionCall(Box::new((expr, args, end)))
                }
                Some(TokenType::Dot) => {
                    self.toks.step().unwrap();
                    let span = self.toks.step_expect(TokenType::Ident)?.span();
                    Expr::MemberAccess(Box::new((expr, span)))
                }
                Some(TokenType::Caret) => {
                    self.toks.step_assert(TokenType::Caret);
                    Expr::UnOp(Box::new((self.toks.current_end_pos(), UnOp::Deref, expr)))
                }
                Some(TokenType::Keyword(Keyword::As)) if include_as => {
                    self.toks.step_assert(TokenType::Keyword(Keyword::As));
                    let target_ty = self.parse_type()?;
                    Expr::Cast(Box::new((TSpan::new(expr.start(), self.toks.current_end_pos()), target_ty, expr)))
                }
                _ => break Ok(expr)
            };
        }
    }

    fn parse_bin_op_rhs(&mut self, expr_prec: u8, mut lhs: Expr) -> EyeResult<Expr> {
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
            lhs = Expr::BinOp(Box::new((op, lhs, rhs)))
        }
        Ok(lhs)
    }

    /// Starts after the if keyword has already been parsed
    fn parse_if_from_cond(&mut self, start: u32) -> EyeResult<If> {
        let cond = self.parse_expr()?;
        let then = self.parse_block_or_expr()?;
        
        let else_ = if let Some(tok) = self.toks.peek() {
            if tok.ty == TokenType::Keyword(Keyword::Else) {
                let tok = self.toks.step_assert(TokenType::Keyword(Keyword::Else));
                let else_pos = tok.end;
                let next = self.toks.peek()
                    .ok_or_else(|| Error::UnexpectedEndOfFile.at(else_pos, else_pos, self.toks.module))?;
                
                match next.ty {
                    TokenType::LBrace => Some(BlockOrExpr::Block(self.parse_block()?)),
                    _ => Some(BlockOrExpr::Expr(self.parse_expr()?))
                }
            } else { None }
        } else { None };

        let end = self.toks.current_end_pos();

        Ok(If { span: TSpan::new(start, end), cond, then, else_ })
    }

    /// Starts after the while keyword has already been parsed
    fn parse_while_from_cond(&mut self, start: u32) -> EyeResult<While> {
        let cond = self.parse_expr()?;
        let body = self.parse_block_or_expr()?;
        Ok(While { cond, body, span: TSpan::new(start, self.toks.current_end_pos()) })
    }
    
    fn parse_path(&mut self) -> EyeResult<IdentPath> {
        let first = self.toks.step_expect([TokenType::Keyword(Keyword::Root), TokenType::Ident])?;
        let path_start = match first.ty {
            TokenType::Keyword(Keyword::Root) => IdentPath::Root,
            TokenType::Ident => IdentPath::Single(first.get_val(self.src).to_owned()),
            _ => unreachable!()
        };
        self.parse_rest_of_path(path_start)
    }

    fn parse_rest_of_path(&mut self, mut path: IdentPath) -> EyeResult<IdentPath> {
        while self.toks.step_if(TokenType::Dot).is_some() {
            path.push(self.toks.step_expect(TokenType::Ident)?.get_val(self.src).to_owned());
        }
        Ok(path)
    }

    fn parse_type(&mut self) -> EyeResult<UnresolvedType> {
        let type_tok = self.toks.step()?;
        match_or_unexpected!(type_tok,
            self.toks.module,
            TokenType::Keyword(Keyword::Root) => Ok(UnresolvedType::Unresolved(
                self.parse_rest_of_path(IdentPath::Root)?
            )),
            TokenType::Ident => {
                let val = type_tok.get_val(self.src).to_owned();
                Ok(UnresolvedType::Unresolved(self.parse_rest_of_path(IdentPath::Single(val))?))
            },
            TokenType::Keyword(Keyword::Primitive(primitive)) => {
                Ok(UnresolvedType::Primitive(primitive))
            },
            TokenType::LParen => {
                self.toks.step_expect(TokenType::RParen)?;
                Ok(UnresolvedType::Primitive(Primitive::Unit))
            },
            TokenType::Star => {
                Ok(UnresolvedType::Pointer(Box::new(self.parse_type()?)))
            },
            TokenType::Underscore => Ok(UnresolvedType::Infer)
        )
    }
}