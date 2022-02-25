use std::collections::HashMap;
use crate::{log, ast::{self, *}, error::{CompileError, EyeError, EyeResult}, lexer::{tokens::{FloatLiteral, IntLiteral, Keyword, Token, TokenType, Operator}}, types::Primitive};

pub struct Parser {
    tokens: Vec<Token>,
    index: usize,
    len: usize
}


macro_rules! tok_expect {
    ($tok_expr: expr, $expect: expr) => {{
        let tok = $tok_expr;
        if $expect == tok.ty {
            tok
        } else {
            return Err(crate::error::EyeError::CompileError(
                crate::error::CompileError::UnexpectedToken(tok.ty, vec![String::from(stringify!($expect))]),
                tok.start,
                tok.end
            ))
        }  
    }};
}

macro_rules! match_or_unexpected {
    ($tok_expr: expr, $($match_arm: pat => $res: expr),*) => {{
        let tok = $tok_expr;
        match tok.ty {
            $($match_arm => $res,)*
            _ => return Err(crate::error::EyeError::CompileError(
                crate::error::CompileError::UnexpectedToken(tok.ty, vec![$(String::from(stringify!($match_arm)), )*]),
                tok.start,
                tok.end
            ))
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

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        let len = tokens.len();
        Self { tokens, index: 0, len }
    }

    pub fn parse(&mut self) -> Result<Module, EyeError> {
        self.parse_module()
    }

    fn current(&self) -> Result<&Token, EyeError> {
        if self.index < self.len {
            Ok(&self.tokens[self.index])
        } else {
            let end = self.tokens.last().unwrap().end;
            Err(EyeError::CompileError(
                CompileError::UnexpectedEndOfFile,
                end,
                end
            ))
        }
    }

    fn position(&self) -> usize {
        self.index
    }

    fn set_position(&mut self, pos: usize) {
        self.index = pos;
    } 

    /// steps over the current token and returns it
    pub fn step(&mut self) -> Result<&Token, EyeError> {
        self.index += 1;
        if self.index <= self.len { // <= because we are only getting the previous token
            Ok(&self.tokens[self.index - 1])
        } else {
            let end = self.tokens.last().unwrap().end;
            Err(EyeError::CompileError(CompileError::UnexpectedEndOfFile, end, end))
        }
    }

    /// stpes over the current token and returns it. Token type checks only happen in debug mode.
    /// This should only be used if the type is known.
    pub fn step_assert(&mut self, ty: TokenType) -> &Token {
        let tok = self.step().expect("step_assert failed");
        debug_assert_eq!(tok.ty, ty);
        tok
    }

    pub fn step_expect<const N: usize, T: Into<TokenTypes<N>>>(&mut self, expected: T) -> Result<&Token, EyeError> {
        let expected = expected.into().0;
        let tok = self.step()?;
        if expected.iter().find(|expected_tok| **expected_tok == tok.ty).is_none() {
            return Err(EyeError::CompileError(
                CompileError::UnexpectedToken(tok.ty, expected.into_iter().map(|tok| format!("{tok:?}")).collect()),
                tok.start,
                tok.end
            ));
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

    pub fn peek(&mut self) -> Option<&Token> {
        if self.index < self.tokens.len() {
            Some(&self.tokens[self.index])
        } else {
            None
        }
    }

    fn parse_module(&mut self) -> Result<Module, EyeError> {
        let mut definitions = HashMap::new();
        
        while self.index < self.len {
            match self.parse_item()? {
                Item::Block(_) => return Err(EyeError::CompileErrorNoPos(CompileError::InvalidTopLevelBlockItem)),
                Item::Definition(name, def) => if let Some(_existing) = definitions.insert(name, def) {
                    return Err(EyeError::CompileErrorNoPos(CompileError::DuplicateDefinition));
                }
            }
        }
        Ok(Module { definitions })
    }

    fn parse_block_or_expr(&mut self) -> EyeResult<BlockOrExpr> {
        match_or_unexpected!(self.peek().ok_or(EyeError::CompileErrorNoPos(CompileError::UnexpectedEndOfFile))?,
            TokenType::LBrace => self.parse_block().map(BlockOrExpr::Block),
            TokenType::Colon => {
                self.step_expect(TokenType::Colon)?;
                let expr = self.parse_expression()?;
                Ok(BlockOrExpr::Expr(expr))
            }
        )
    }

    fn parse_block(&mut self) -> EyeResult<Block> {
        tok_expect!(self.step()?, TokenType::LBrace);

        let mut defs = HashMap::new();
        let mut items = Vec::new();

        while self.current()?.ty != TokenType::RBrace {
            match self.parse_item()? {
                Item::Block(item) => items.push(item),
                Item::Definition(name, def) => if let Some(_existing) = defs.insert(name, def) {
                    return Err(EyeError::CompileErrorNoPos(CompileError::DuplicateDefinition));
                }
            }
        }

        tok_expect!(self.step().unwrap(), TokenType::RBrace);

        Ok( Block { items, defs })
    }

    fn parse_item(&mut self) -> Result<Item, EyeError> {
        let pre_item_pos = self.position();

        enum Parsed {
            Item(Item),
            Error(EyeError),
            None
        }

        let block_item = match self.current()?.ty {
            TokenType::LBrace => Parsed::Item(Item::Block(BlockItem::Block(self.parse_block()?))),
            TokenType::Keyword(Keyword::If) => {
                self.step_assert(TokenType::Keyword(Keyword::If));
                Parsed::Item(Item::Block(BlockItem::Expression(
                    Expression::If(Box::new(self.parse_if_from_cond()?))
                )))
            }
            TokenType::Ident => {
                let name = self.step_assert(TokenType::Ident).get_val();
                match self.step().map(|t| t.ty) {
                    Ok(TokenType::LParen) => match self.parse_params() {
                        Ok(params) => {
                            match self.step().map(|t| t.ty) {
                                Ok(TokenType::Arrow) => {
                                    let return_type = match self.peek().map(|t| t.ty) {
                                        Some(TokenType::LBrace | TokenType::Colon) => UnresolvedType::Primitive(Primitive::Unit),
                                        _ => self.parse_type()?
                                    };
                                    let body = self.parse_block_or_expr()?;
                                    Parsed::Item(Item::Definition(name, Definition::Function(Function {
                                        params, vararg: None, body, return_type
                                    })))
                                },
                                Ok(_) => Parsed::None,
                                Err(err) => Parsed::Error(err)
                            }
                        }
                        Err(err) => Parsed::Error(err)
                    },
                    Ok(TokenType::Arrow) => {
                        let return_type = match self.peek().map(|t| t.ty) {
                            Some(TokenType::LBrace | TokenType::Colon) => UnresolvedType::Primitive(Primitive::Unit),
                            _ => self.parse_type()?
                        };
                        let body = self.parse_block_or_expr()?;
                        Parsed::Item(Item::Definition(name, Definition::Function(Function {
                            params: Vec::new(), vararg: None, body, return_type
                        })))
                    },
                    Ok(TokenType::DoubleColon) => {
                        self.step_expect(TokenType::LBrace)?;
                        let mut members: Vec<(String, UnresolvedType)> = Vec::new();
                        while self.current()?.ty != TokenType::RBrace {
                            let member_name = tok_expect!(self.step()?, TokenType::Ident).get_val();
                            let member_type = self.parse_type()?;
                            if self.current()?.ty == TokenType::Comma {
                                self.step()?;
                            }
                            members.push((member_name, member_type))
                        }
                        tok_expect!(self.step()?, TokenType::RBrace);
                        log!("Successfully constructed {}", name);
                        Parsed::Item(Item::Definition(name, Definition::Struct(StructDefinition { members })))
                    },
                    Ok(TokenType::Colon) => {
                        let ty = self.parse_type()?;
                        let val = self.step_if(TokenType::Assign).is_some()
                            .then(|| self.parse_expression()).transpose()?;
                        Parsed::Item(Item::Block(BlockItem::Declare(name, Some(ty), val)))
                    },
                    Ok(TokenType::Declare) => {
                        let val = self.parse_expression()?;
                        Parsed::Item(Item::Block(BlockItem::Declare(name, None, Some(val))))
                    }
                    Ok(TokenType::Dot) => {
                        let mut l_value = LValue::Variable(name);
                        loop {
                            let member = tok_expect!(self.step()?, TokenType::Ident).val.clone();
                            l_value = LValue::Member(Box::new(l_value), member);
                            match_or_unexpected!{self.step()?,
                                TokenType::Dot => {},
                                TokenType::Assign => break
                            }
                        }
                        let val = self.parse_expression()?;
                        Parsed::Item(Item::Block(BlockItem::Assign(l_value, val)))
                    }
                    Ok(TokenType::Assign) => {
                        let val = self.parse_expression()?;
                        Parsed::Item(Item::Block(BlockItem::Assign(LValue::Variable(name), val)))
                    }
                    _ => Parsed::None
                }
            },
            _ => Parsed::None
        };
        if let Parsed::Item(item) = block_item {
            Ok(item)
        } else {
            self.set_position(pre_item_pos);
            match self.parse_expression() {
                Ok(expr) => {
                    Ok(Item::Block(BlockItem::Expression(expr)))
                }
                Err(err) => {
                    match block_item {
                        Parsed::Item(_) => unreachable!(),
                        Parsed::Error(err) => Err(err),
                        Parsed::None => Err(err),
                    }
                }
            }
        }
    }

    fn parse_params(&mut self) -> EyeResult<Vec<(String, UnresolvedType)>> {
        let mut params = Vec::new();
        match self.peek() {
            Some(tok) if tok.ty == TokenType::RParen => return Ok(params),
            _ => ()
        }
        loop {
            let name = tok_expect!(self.step()?, TokenType::Ident).val.clone();
            let ty = self.parse_type()?;
            params.push((name, ty));
            match_or_unexpected!(self.step()?,
                TokenType::RParen => break,
                TokenType::Comma => ()
            );
        }
        Ok(params)
    }

    fn parse_expression(&mut self) -> EyeResult<Expression> {
        let lhs = self.parse_factor()?;
        self.parse_bin_op_rhs(0, lhs)
    }

    fn parse_factor(&mut self) -> Result<Expression, EyeError> {
        let first = self.step()?;
        let mut expr = match_or_unexpected!(first,
            TokenType::Operator(Operator::Sub) => {
                Expression::Negate(Box::new(self.parse_factor()?))
            },
            TokenType::LParen => {
                let factor = self.parse_expression()?;
                tok_expect!(self.step()?, TokenType::RParen);
                factor
            },
            TokenType::Keyword(Keyword::Ret) => Expression::Return(Box::new(self.parse_expression()?)),
            TokenType::IntLiteral              => Expression::IntLiteral(IntLiteral::from_tok(first)?),
            TokenType::FloatLiteral            => Expression::FloatLiteral(FloatLiteral::from_tok(first)?),
            TokenType::StringLiteral           => Expression::StringLiteral(first.get_val()),
            TokenType::Keyword(Keyword::True)  => Expression::BoolLiteral(true),
            TokenType::Keyword(Keyword::False) => Expression::BoolLiteral(false),
            TokenType::Ident                   => Expression::Variable(first.get_val()),
            TokenType::Keyword(Keyword::If) => Expression::If(Box::new(self.parse_if_from_cond()?)),
            TokenType::Keyword(Keyword::Primitive(p)) => {
                let inner = self.parse_expression()?;
                Expression::Cast(p, Box::new(inner))
            }
        );
        loop {
            match self.peek().map(|t| t.ty) {
                Some(TokenType::LParen) => {
                    // function call
                    tok_expect!(self.step()?, TokenType::LParen);
                    let mut args = Vec::new();
                    loop {
                        match self.peek().map(|t| t.ty) {
                            Some(TokenType::RParen) => { self.step().unwrap(); break },
                            _ => ()
                        }
                        args.push(self.parse_expression()?);
                        match_or_unexpected!(self.step()?,
                            TokenType::Comma => (),
                            TokenType::RParen => break
                        )
                    }
                    expr = Expression::FunctionCall(Box::new(expr), args);
                }
                Some(TokenType::Dot) => {
                    self.step().unwrap();
                    let field = tok_expect!(self.step()?, TokenType::Ident).val.clone();
                    expr = Expression::MemberAccess(Box::new(expr), field);
                }
                _ => break
            }
        }
        Ok(expr)
    }

    fn parse_bin_op_rhs(&mut self, expr_prec: u8, mut lhs: Expression) -> EyeResult<Expression> {
        while let Some(TokenType::Operator(op)) = self.peek().map(|t| t.ty) {
            self.step().unwrap(); // op
            let op_prec = op.precedence();
            if op_prec < expr_prec { break; }
            let mut rhs = self.parse_factor()?;

            // If BinOp binds less tightly with RHS than the operator after RHS, let
            // the pending operator take RHS as its LHS.
            match self.peek().map(|t| t.ty) {
                Some(TokenType::Operator(next_op)) => if op_prec < next_op.precedence() {
                    rhs = self.parse_bin_op_rhs(op.precedence() + 1, rhs)?;
                },
                _ => ()
            };
            lhs = Expression::BinOp(op, Box::new((lhs, rhs)));
        }
        Ok(lhs)
    }

    /// Starts after the if keyword has already been parsed
    fn parse_if_from_cond(&mut self) -> EyeResult<ast::If> {
        let cond = self.parse_expression()?;
        let then = self.parse_block_or_expr()?;
        
        let else_ = if let Some(tok) = self.peek() {
            if tok.ty == TokenType::Keyword(Keyword::Else) {
                let tok = self.step_assert(TokenType::Keyword(Keyword::Else));
                let else_pos = tok.end;
                let next = self.peek().ok_or(EyeError::CompileError(
                    CompileError::UnexpectedEndOfFile,
                    else_pos,
                    else_pos
                ))?;
                
                match next.ty {
                    TokenType::LBrace => Some(BlockOrExpr::Block(self.parse_block()?)),
                    _ => Some(BlockOrExpr::Expr(self.parse_expression()?))
                }
            } else { None }
        } else { None };

        Ok(ast::If { cond, then, else_ })
    }

    fn parse_type(&mut self) -> EyeResult<UnresolvedType> {
        let type_tok = self.step()?;
        Ok(match_or_unexpected!(type_tok,
            TokenType::Ident => {
                UnresolvedType::Unresolved(type_tok.get_val())
            },
            TokenType::Keyword(Keyword::Primitive(primitive)) => {
                UnresolvedType::Primitive(primitive)
            },
            TokenType::LParen => {
                tok_expect!(self.step()?, TokenType::RParen);
                UnresolvedType::Primitive(Primitive::Unit)
            }
        ))
    }
}