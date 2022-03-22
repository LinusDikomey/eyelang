use std::collections::HashMap;
use crate::{
    log,
    ast::*,
    error::{CompileError, EyeResult, Error},
    lexer::{tokens::{FloatLiteral, IntLiteral, Keyword, Token, TokenType, Operator}, Span},
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
            let end = self.tokens.last().unwrap().end;
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
        self.tokens.last().map(|tok| tok.end).unwrap_or(0)
    }

    pub fn position(&self) -> usize {
        self.index
    }

    pub fn set_position(&mut self, pos: usize) {
        self.index = pos;
    }

    /// steps over the current token and returns it
    pub fn step(&mut self) -> Result<&Token, CompileError> {
        self.index += 1;
        if self.index <= self.len { // <= because we are only getting the previous token
            Ok(&self.tokens[self.index - 1])
        } else {
            let end = self.tokens.last().unwrap().end;
            Err(CompileError {
                err: Error::UnexpectedEndOfFile,
                span: Span::new(end, end, self.module),
            })
        }
    }

    /// stpes over the current token and returns it. Token type checks only happen in debug mode.
    /// This should only be used if the type is known.
    pub fn step_assert(&mut self, ty: TokenType) -> &Token {
        let tok = self.step().expect("step_assert failed");
        debug_assert_eq!(tok.ty, ty);
        tok
    }

    pub fn step_expect<const N: usize, T: Into<TokenTypes<N>>>(&mut self, expected: T) -> Result<&Token, CompileError> {
        let expected = expected.into().0;
        let module = self.module;
        let tok = self.step()?;
        if expected.iter().find(|expected_tok| **expected_tok == tok.ty).is_none() {
            return Err(CompileError {
                err: Error::UnexpectedToken, //(tok.ty, expected.into_iter().map(|tok| format!("{tok:?}")).collect()),
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
        
        while self.toks.index < self.toks.len {
            let start = self.toks.current().unwrap().start;
            match self.parse_item(&mut 0)? {
                Item::Block(_) => return Err(CompileError {
                    err: Error::InvalidTopLevelBlockItem,
                    span: Span::new(start, self.toks.current().unwrap().end, self.toks.module)
                }),
                Item::Definition(name, def) => if let Some(_existing) = definitions.insert(name, def) {
                    return Err(Error::DuplicateDefinition.at(start, self.toks.current().unwrap().end, self.toks.module));
                }
            }
        }
        Ok(Module { definitions })
    }

    fn parse_block_or_expr(&mut self, var_index: &mut u32) -> EyeResult<BlockOrExpr> {
        match_or_unexpected!(
            self.toks.peek()
                .ok_or(Error::UnexpectedEndOfFile.at(
                    self.toks.last_src_pos(),
                    self.toks.last_src_pos(),
                    self.toks.module
                ))?,
            self.toks.module,
            TokenType::LBrace => self.parse_block(var_index).map(BlockOrExpr::Block),
            TokenType::Colon => {
                self.toks.step_expect(TokenType::Colon)?;
                let expr = self.parse_expression(var_index)?;
                Ok(BlockOrExpr::Expr(expr))
            }
        )
    }

    fn parse_block(&mut self, var_index: &mut u32) -> EyeResult<Block> {
        self.toks.step_expect(TokenType::LBrace)?;
        let mut defs = HashMap::new();
        let mut items = Vec::new();

        while self.toks.current()?.ty != TokenType::RBrace {
            let start = self.toks.current().unwrap().start;
            match self.parse_item(var_index)? {
                Item::Block(item) => items.push(item),
                Item::Definition(name, def) => if let Some(_existing) = defs.insert(name, def) {
                    let end = self.toks.current().unwrap().end;
                    return Err(Error::DuplicateDefinition.at(start, end, self.toks.module));
                }
            }
        }
        self.toks.step_expect(TokenType::RBrace)?;
        Ok( Block { items, defs })
    }

    fn parse_item(&mut self, var_index: &mut u32) -> Result<Item, CompileError> {
        let pre_item_pos = self.toks.position();

        enum Parsed {
            Item(Item),
            Error(CompileError),
            None
        }

        let block_item = match self.toks.current()?.ty {
            TokenType::LBrace => Parsed::Item(Item::Block(BlockItem::Block(self.parse_block(var_index)?))),
            TokenType::Keyword(Keyword::If) => {
                self.toks.step_assert(TokenType::Keyword(Keyword::If));
                Parsed::Item(Item::Block(BlockItem::Expression(
                    Expression::If(Box::new(self.parse_if_from_cond(var_index)?))
                )))
            }
            TokenType::Ident => {
                let ident = self.toks.step_assert(TokenType::Ident);
                let ident_start = ident.start;
                let name = ident.get_val(self.src);
                match self.toks.step().map(|t| t.ty) {
                    Ok(TokenType::LParen) => match self.parse_params() {
                        Ok((params, varargs)) => {
                            match self.toks.step().map(|t| t.ty) {
                                Ok(TokenType::Arrow) => {
                                    let ret_type_start = self.toks.current().unwrap().start;
                                    let (return_type, ret_type_end, is_extern) = match self.toks.peek().map(|t| t.ty) {
                                        Some(TokenType::LBrace | TokenType::Colon) =>
                                            (UnresolvedType::Primitive(Primitive::Unit), ret_type_start, false),
                                        Some(TokenType::Keyword(Keyword::Extern)) => {
                                            self.toks.step_assert(TokenType::Keyword(Keyword::Extern));
                                            (UnresolvedType::Primitive(Primitive::Unit), ret_type_start, true)
                                        }
                                        _ => {
                                            let ty = self.parse_type()?;
                                            let end = self.toks.previous().unwrap().end;
                                            (ty, end, self.toks.step_if(TokenType::Keyword(Keyword::Extern)).is_some())
                                        }
                                    };
                                    let mut var_count = 1 + params.len() as u32;
                                    let body = (!is_extern).then(|| {
                                        self.parse_block_or_expr(&mut var_count)
                                    }).transpose()?;
                                    Parsed::Item(Item::Definition(name.to_owned(), Definition::Function(Function {
                                        params,
                                        varargs,
                                        body,
                                        return_type: (return_type, ret_type_start, ret_type_end), var_count
                                    })))
                                },
                                Ok(_) => Parsed::None,
                                Err(err) => Parsed::Error(err)
                            }
                        }
                        Err(err) => Parsed::Error(err)
                    },
                    Ok(TokenType::Arrow) => {
                        let ret_type_start = self.toks.current().unwrap().start;
                        let (return_type, ret_type_end, is_extern) = match self.toks.peek().map(|t| t.ty) {
                            Some(TokenType::LBrace | TokenType::Colon)
                                => (UnresolvedType::Primitive(Primitive::Unit), ret_type_start, false),
                            Some(TokenType::Keyword(Keyword::Extern)) => {
                                self.toks.step_assert(TokenType::Keyword(Keyword::Extern));
                                (UnresolvedType::Primitive(Primitive::Unit), ret_type_start, true)
                            }
                            _ => {
                                let ty = self.parse_type()?;
                                let end = self.toks.previous().unwrap().end;
                                (ty, end, self.toks.step_if(TokenType::Keyword(Keyword::Extern)).is_some())
                            }
                        };
                        let mut var_count = 1; // return type, no params
                        let body = (!is_extern).then(|| {
                            self.parse_block_or_expr(&mut var_count)
                        }).transpose()?;
                        Parsed::Item(Item::Definition(name.to_owned(), Definition::Function(Function {
                            params: Vec::new(), varargs: false, body, return_type: (return_type, ret_type_start, ret_type_end), var_count
                        })))
                    },
                    Ok(TokenType::DoubleColon) => {
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
                            members.push((member_name.to_owned(), member_type, start, end))
                        }
                        self.toks.step_expect(TokenType::RBrace)?;
                        log!("Successfully constructed {}", name);
                        Parsed::Item(Item::Definition(
                            name.to_owned(),
                            Definition::Struct(StructDefinition { members })
                        ))
                    },
                    Ok(TokenType::Colon) => {
                        let ty = self.parse_type()?;
                        let val = self.toks.step_if(TokenType::Assign).is_some()
                            .then(|| self.parse_expression(var_index)).transpose()?;
                        let index = *var_index;
                        *var_index += 1;
                        Parsed::Item(Item::Block(BlockItem::Declare(name.to_owned(), index, Some(ty), val)))
                    },
                    Ok(TokenType::Declare) => {
                        let val = self.parse_expression(var_index)?;
                        let index = *var_index;
                        *var_index += 1;
                        Parsed::Item(Item::Block(BlockItem::Declare(name.to_owned(), index, None, Some(val))))
                    }
                    Ok(TokenType::Dot) => {
                        let mut l_value = LValue::Variable(ident_start, name.to_owned());
                        let res =  loop {
                            let member = self.toks.step_expect(TokenType::Ident)?.get_val(self.src).to_owned();
                            l_value = LValue::Member(Box::new(l_value), member);
                            match self.toks.step() {
                                Ok(tok) if tok.ty == TokenType::Dot => {}
                                Ok(tok) if tok.ty == TokenType::Assign => break Ok(()),
                                Err(err) => break Err(err),
                                Ok(other) => break Err(CompileError {
                                    err: Error::UnexpectedToken,
                                    span: Span::new(other.start, other.end, self.toks.module) 
                                })
                            }
                        };
                        if let Err(err) = res {
                            Parsed::Error(err)
                        } else {
                            match self.parse_expression(var_index) {
                                Ok(val) => Parsed::Item(Item::Block(BlockItem::Assign(l_value, val))),
                                Err(err) => Parsed::Error(err)
                            }
                            
                        }
                    }
                    Ok(TokenType::Assign) => {
                        let val = self.parse_expression(var_index)?;
                        Parsed::Item(Item::Block(BlockItem::Assign(LValue::Variable(ident_start, name.to_owned()), val)))
                    }
                    _ => Parsed::None
                }
            },
            _ => Parsed::None
        };
        if let Parsed::Item(item) = block_item {
            Ok(item)
        } else {
            self.toks.set_position(pre_item_pos);
            match self.parse_expression(var_index) {
                Ok(expr) => {
                    Ok(Item::Block(BlockItem::Expression(expr)))
                }
                Err(err) => {
                    match block_item {
                        Parsed::Item(_) => unreachable!(),
                        Parsed::Error(parse_err) => { dbg!((err, parse_err)); Err(parse_err) },
                        Parsed::None => Err(err),
                    }
                }
            }
        }
    }

    fn parse_params(&mut self) -> EyeResult<(Vec<(String, UnresolvedType, u32, u32)>, bool)> {
        let mut params = Vec::new();
        let mut vararg = false;
        match self.toks.peek() {
            Some(tok) if tok.ty == TokenType::RParen => return Ok((params, vararg)),
            _ => ()
        }
        loop {
            if self.toks.step_if(TokenType::TripleDot).is_some() {
                vararg = true;
                self.toks.step_expect(TokenType::RParen)?;
                break;
            }
            let name_tok = self.toks.step_expect(TokenType::Ident)?;
            let start = name_tok.start;
            let name = name_tok.get_val(self.src).to_owned();
            let ty = self.parse_type()?;
            params.push((name, ty, start, self.toks.previous().unwrap().end));
            match_or_unexpected!(self.toks.step()?,
                self.toks.module,
                TokenType::RParen => break,
                TokenType::Comma => ()
            );
        }
        Ok((params, vararg))
    }

    fn parse_expression(&mut self, var_index: &mut u32) -> EyeResult<Expression> {
        let lhs = self.parse_factor(var_index)?;
        self.parse_bin_op_rhs(var_index, 0, lhs)
    }

    fn parse_factor(&mut self, var_index: &mut u32) -> Result<Expression, CompileError> {
        let first = self.toks.step()?;
        let mut expr = match_or_unexpected!(first,
            self.toks.module,
            TokenType::Operator(Operator::Sub) => Expression::UnOp(UnOp::Neg, Box::new(self.parse_factor(var_index)?)),
            TokenType::Bang => Expression::UnOp(UnOp::Not, Box::new(self.parse_factor(var_index)?)),

            TokenType::LParen => {
                if self.toks.step_if(TokenType::RParen).is_some() {
                    Expression::Unit
                } else {
                    let factor = self.parse_expression(var_index)?;
                    self.toks.step_expect(TokenType::RParen)?;
                    factor
                }
            },
            TokenType::Keyword(Keyword::Ret) => Expression::Return(Box::new(self.parse_expression(var_index)?)),
            TokenType::IntLiteral              => Expression::IntLiteral(IntLiteral::from_tok(first, self.src)),
            TokenType::FloatLiteral            => Expression::FloatLiteral(FloatLiteral::from_tok(first, self.src)),
            TokenType::StringLiteral           => Expression::StringLiteral(
                self.src[first.start as usize + 1 ..= first.end as usize - 1]
                    .replace("\\n", "\n")
                    .replace("\\t", "\t")
                    .replace("\\r", "\r")
                    .replace("\\\"", "\r")
            ),
            TokenType::Keyword(Keyword::True)  => Expression::BoolLiteral(true),
            TokenType::Keyword(Keyword::False) => Expression::BoolLiteral(false),
            TokenType::Ident                   => Expression::Variable(first.get_val(self.src).to_owned()),
            TokenType::Keyword(Keyword::If) => Expression::If(Box::new(self.parse_if_from_cond(var_index)?)),
            TokenType::Keyword(Keyword::Primitive(p)) => {
                let inner = self.parse_factor(var_index)?;
                Expression::Cast(p, Box::new(inner))
            },
            TokenType::Keyword(Keyword::Root) => {
                Expression::Root
            }
        );
        loop {
            match self.toks.peek().map(|t| t.ty) {
                Some(TokenType::LParen) => {
                    // function call
                    self.toks.step_expect(TokenType::LParen)?;
                    let mut args = Vec::new();
                    if self.toks.step_if(TokenType::RParen).is_none() {
                        loop {
                            args.push(self.parse_expression(var_index)?);
                            match_or_unexpected!(self.toks.step()?,
                                self.toks.module,
                                TokenType::Comma => (),
                                TokenType::RParen => break
                            )
                        }
                    }
                    expr = Expression::FunctionCall(Box::new(expr), args);
                }
                Some(TokenType::Dot) => {
                    self.toks.step().unwrap();
                    let field = self.toks.step_expect(TokenType::Ident)?.get_val(self.src).to_owned();
                    expr = Expression::MemberAccess(Box::new(expr), field);
                }
                _ => break
            }
        }
        Ok(expr)
    }

    fn parse_bin_op_rhs(&mut self, var_index: &mut u32, expr_prec: u8, mut lhs: Expression) -> EyeResult<Expression> {
        while let Some(TokenType::Operator(op)) = self.toks.peek().map(|t| t.ty) {
            self.toks.step().unwrap(); // op
            let op_prec = op.precedence();
            if op_prec < expr_prec { break; }
            let mut rhs = self.parse_factor(var_index)?;

            // If BinOp binds less tightly with RHS than the operator after RHS, let
            // the pending operator take RHS as its LHS.
            match self.toks.peek().map(|t| t.ty) {
                Some(TokenType::Operator(next_op)) => if op_prec < next_op.precedence() {
                    rhs = self.parse_bin_op_rhs(var_index, op.precedence() + 1, rhs)?;
                },
                _ => ()
            };
            lhs = Expression::BinOp(op, Box::new((lhs, rhs)));
        }
        Ok(lhs)
    }

    /// Starts after the if keyword has already been parsed
    fn parse_if_from_cond(&mut self, var_index: &mut u32) -> EyeResult<If> {
        let cond = self.parse_expression(var_index)?;
        let then = self.parse_block_or_expr(var_index)?;
        
        let else_ = if let Some(tok) = self.toks.peek() {
            if tok.ty == TokenType::Keyword(Keyword::Else) {
                let tok = self.toks.step_assert(TokenType::Keyword(Keyword::Else));
                let else_pos = tok.end;
                let next = self.toks.peek()
                    .ok_or(Error::UnexpectedEndOfFile.at(else_pos, else_pos, self.toks.module))?;
                
                match next.ty {
                    TokenType::LBrace => Some(BlockOrExpr::Block(self.parse_block(var_index)?)),
                    _ => Some(BlockOrExpr::Expr(self.parse_expression(var_index)?))
                }
            } else { None }
        } else { None };

        Ok(If { cond, then, else_ })
    }

    fn parse_type(&mut self) -> EyeResult<UnresolvedType> {
        let type_tok = self.toks.step()?;
        let parse_segments = |toks: &mut Tokens, mut path: IdentPath| -> EyeResult<UnresolvedType> {
            while toks.step_if(TokenType::Dot).is_some() {
                path.push(toks.step_expect(TokenType::Ident)?.get_val(self.src).to_owned());
            }
            Ok(UnresolvedType::Unresolved(path))
        };
        match_or_unexpected!(type_tok,
            self.toks.module,
            TokenType::Keyword(Keyword::Root) => parse_segments(&mut self.toks, IdentPath::Root),
            TokenType::Ident => {
                let val = type_tok.get_val(self.src).to_owned();
                parse_segments(&mut self.toks, IdentPath::Single(val))
            },
            TokenType::Keyword(Keyword::Primitive(primitive)) => {
                Ok(UnresolvedType::Primitive(primitive))
            },
            TokenType::LParen => {
                self.toks.step_expect(TokenType::RParen)?;
                Ok(UnresolvedType::Primitive(Primitive::Unit))
            }
        )
    }
}