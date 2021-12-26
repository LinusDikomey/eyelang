use std::collections::HashMap;

use crate::{log, ast::*, error::{CompileError, EyeError, EyeResult}, lexer::{tokens::{FloatLiteral, IntLiteral, Keyword, Token, TokenType}}, types::Primitive};

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

    pub fn peek(&mut self) -> Option<&Token> {
        if self.index < self.tokens.len() {
            Some(&self.tokens[self.index])
        } else {
            None
        }
    }

    fn parse_module(&mut self) -> Result<Module, EyeError> {
        let mut functions = HashMap::new();
        let mut types = HashMap::new();

        while self.index < self.len {
            match self.parse_item()? {
                Item::Block(_) => return Err(EyeError::CompileErrorNoPos(CompileError::InvalidTopLevelBlockItem)),
                Item::Definition(Definition::Function(name, func)) => {
                    if functions.insert(name, func).is_some() {
                        return Err(EyeError::CompileErrorNoPos(CompileError::DuplicateFunctionDefinition));
                    }
                }
                Item::Definition(Definition::Struct(name, struc)) => {
                    if types.insert(name, UnresolvedTypeDefinition::Struct(struc)).is_some() {
                        return Err(EyeError::CompileErrorNoPos(CompileError::DuplicateTypeDefinition));
                    }
                },
            }
            /*match_or_unexpected!(self.current()?, 
                TokenType::Keyword(Keyword::Struct) => {
                    let (name, struc) = self.parse_struct()?; 
                    types.insert(name, UnresolvedTypeDefinition::Struct(struc));
                },
                TokenType::Ident => {
                    let (name, func) = self.parse_function()?;
                    if functions.insert(name, func).is_some() {
                        return Err(EyeError::CompileErrorNoPos(CompileError::DuplicateFunctionDefinition));
                    }
                }
            );*/
        }
        Ok(Module { functions, types })
    }

    /*fn parse_function(&mut self) -> Result<(String, Function), EyeError> {
        let name = tok_expect!(self.step()?, TokenType::Ident).get_val();
        log!("Parsing function with name {}", name);

        let args: Vec<(String, UnresolvedType)> = Vec::new();


        //TODO: optionally parse args here

        tok_expect!(self.step()?, TokenType::DoubleColon);

        let mut return_type = UnresolvedType::Primitive(Primitive::Void);
        
        let brace_or_ret = self.current()?;

        match_or_unexpected!{brace_or_ret,
            TokenType::LBrace => (),
            TokenType::Ident => {
                return_type = UnresolvedType::Unresolved(brace_or_ret.get_val());
                self.step().unwrap();
            },
            TokenType::Keyword(Keyword::Primitive(primitive)) => {
                return_type = UnresolvedType::Primitive(primitive);
                self.step().unwrap();
            }
        };

        let body = self.parse_block()?;

        Ok((name, Function { args, return_type, body }))
    }*/

    fn parse_block(&mut self) -> Result<Block, EyeError> {
        tok_expect!(self.step()?, TokenType::LBrace);

        let mut defs = Vec::new();
        let mut items = Vec::new();

        while self.current()?.ty != TokenType::RBrace {
            match self.parse_item()? {
                Item::Block(item) => items.push(item),
                Item::Definition(def) => defs.push(def)
            }
        }

        tok_expect!(self.step().unwrap(), TokenType::RBrace);

        Ok( Block { items, defs })
    }

    fn parse_item(&mut self) -> Result<Item, EyeError> {
        let pre_item_pos = self.position();
        let block_item = match self.current()?.ty {
            TokenType::LBrace => Some(Item::Block(BlockItem::Block(self.parse_block()?))),
            TokenType::Ident => {
                let name = tok_expect!(self.step()?, TokenType::Ident).get_val();
                match self.step().map(|t| t.ty) {
                    Ok(TokenType::LParen) => match self.parse_params() {
                        Ok(params) => {
                            match self.step().map(|t| t.ty) {
                                Ok(TokenType::Arrow) => {
                                    let return_type = match self.peek().map(|t| t.ty) {
                                        Some(TokenType::LBrace) => UnresolvedType::Primitive(Primitive::Void),
                                        _ => self.parse_type()?
                                    };
                                    let body = self.parse_block()?;
                                    Some(Item::Definition(Definition::Function(name, Function {
                                        params,  body, return_type
                                    })))
                                },
                                _ => None
                            }
                        },
                        Err(_) => None
                    },
                    Ok(TokenType::Arrow) => {
                        let return_type = match self.peek().map(|t| t.ty) {
                            Some(TokenType::LBrace) => UnresolvedType::Primitive(Primitive::Void),
                            _ => self.parse_type()?
                        };
                        let body = self.parse_block()?;
                        Some(Item::Definition(Definition::Function(name, Function {
                            params: Vec::new(),  body, return_type
                        })))
                    },
                    Ok(TokenType::DoubleColon) => {
                        tok_expect!(self.step()?, TokenType::LBrace);
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
                        Some(Item::Definition(Definition::Struct(name,
                            StructDefinition { members }
                        )))
                    },
                    Ok(TokenType::Colon) => {
                        let ty = self.parse_type()?;
                        let val = match_or_unexpected!{self.step()?, 
                            TokenType::Assign => Some(self.parse_expression()?),
                            TokenType::Semicolon => None
                        };
                        tok_expect!(self.step()?, TokenType::Semicolon);
                        Some(Item::Block(BlockItem::Declare(name, Some(ty), val)))
                    },
                    Ok(TokenType::Declare) => {
                        let val = self.parse_expression()?;
                        tok_expect!(self.step()?, TokenType::Semicolon);
                        Some(Item::Block(BlockItem::Declare(name, None, Some(val))))
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
                        tok_expect!(self.step()?, TokenType::Semicolon);
                        Some(Item::Block(BlockItem::Assign(l_value, val)))
                    }
                    Ok(TokenType::Assign) => {
                        let val = self.parse_expression()?;
                        tok_expect!(self.step()?, TokenType::Semicolon);
                        Some(Item::Block(BlockItem::Assign(LValue::Variable(name), val)))
                    }
                    _ => None
                }
            },
            _ => None
        };
        if let Some(item) = block_item {
            Ok(item)
        } else {
            self.set_position(pre_item_pos);
            let expr = BlockItem::Expression(self.parse_expression()?);
            tok_expect!(self.step()?, TokenType::Semicolon);
            Ok(Item::Block(expr))
        }
    }

    fn parse_params(&mut self) -> EyeResult<Vec<(String, UnresolvedType)>> {
        let mut params = Vec::new();
        loop {
            match self.peek() {
                Some(tok) if tok.ty == TokenType::RParen => break,
                _ => ()
            }
            let name = tok_expect!(self.step()?, TokenType::Ident).val.clone();
            tok_expect!(self.step()?, TokenType::Colon);
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
            TokenType::LParen => {
                let factor = self.parse_expression()?;
                tok_expect!(self.step()?, TokenType::RParen);
                factor
            },
            TokenType::Keyword(Keyword::Yeet) => {
                let return_val = if self.current()?.ty == TokenType::Semicolon {
                    None
                } else {
                    Some(Box::new(self.parse_expression()?))
                };
                Expression::Return(return_val)
            },
            TokenType::IntLiteral              => Expression::IntLiteral(IntLiteral::from_tok(first)?),
            TokenType::FloatLiteral            => Expression::FloatLiteral(FloatLiteral::from_tok(first)?),
            TokenType::StringLiteral           => Expression::StringLiteral(first.get_val()),
            TokenType::Keyword(Keyword::True)  => Expression::BoolLiteral(true),
            TokenType::Keyword(Keyword::False) => Expression::BoolLiteral(false),
            TokenType::Ident                   => Expression::Variable(first.get_val()),
            TokenType::Keyword(Keyword::If) => {
                let cond = self.parse_expression()?;
                let then_block = self.parse_block()?;
                let else_block = if self.current()?.ty == TokenType::Keyword(Keyword::Else) {
                    self.step()?;
                    Some(self.parse_block()?,)
                } else {
                    None
                };
                Expression::If(Box::new(cond), then_block, else_block)
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

    fn parse_type(&mut self) -> Result<UnresolvedType, EyeError> {
        let type_tok = self.step()?;
        Ok(match_or_unexpected!(type_tok,
            TokenType::Ident => {
                UnresolvedType::Unresolved(type_tok.get_val())
            },
            TokenType::Keyword(Keyword::Primitive(primitive)) => {
                UnresolvedType::Primitive(primitive)
            }
        ))
    }
}