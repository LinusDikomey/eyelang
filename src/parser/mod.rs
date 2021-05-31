use std::{primitive, thread::current};

use crate::{ast::*, error::{CompileError, EyeError}, lexer::tokens::{FloatLiteral, IntLiteral, Keyword, Operator, Token, TokenType}, types::Primitive};



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

    fn peek(&self) -> Result<&Token, EyeError> {
        self.peek_count(1)
    }

    fn peek_count(&self, count: usize) -> Result<&Token, EyeError> {
        let index = self.index + count;
        if index < self.len {
            Ok(&self.tokens[self.index + count])
        } else {
            let end = self.tokens.last().unwrap().end;
            Err(EyeError::CompileError(
                CompileError::UnexpectedEndOfFile,
                end,
                end
            ))
        }
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

    fn parse_module(&mut self) -> Result<Module, EyeError> {
        let mut functions = Vec::new();
        let mut structs = Vec::new();

        while self.index < self.len {
            match_or_unexpected!(self.current()?, 
                TokenType::Keyword(Keyword::Struct) => structs.push(self.parse_struct()?),
                TokenType::Ident => functions.push(self.parse_function()?)
            );
        }
        Ok(Module { functions, structs})
    }

    fn parse_struct(&mut self) -> Result<Struct, EyeError> {
        tok_expect!(self.step()?, TokenType::Keyword(Keyword::Struct));
        let name = tok_expect!(self.step()?, TokenType::Ident).get_val();
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
        println!("Successfully conSTRUCTed {}", name);
        Ok(Struct{name, members})
    }

    fn parse_function(&mut self) -> Result<Function, EyeError> {
        let name = tok_expect!(self.step()?, TokenType::Ident).get_val();
        println!("Parsing function with name {}", name);

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

        Ok(Function { name, args, return_type, body })
    }

    fn parse_block(&mut self) -> Result<Block, EyeError> {
        tok_expect!(self.step()?, TokenType::LBrace);

        let mut items = Vec::new();

        while self.current()?.ty != TokenType::RBrace {
            items.push(self.parse_block_item()?)
        }

        tok_expect!(self.step().unwrap(), TokenType::RBrace);

        Ok( Block { items })
    }

    fn parse_block_item(&mut self) -> Result<BlockItem, EyeError> {

        let block_item = match self.current()?.ty {
            TokenType::LBrace => Some(BlockItem::Block(self.parse_block()?)),
            TokenType::Ident => {
                let name = tok_expect!(self.step()?, TokenType::Ident).get_val();
                let (ty, val): (Option<UnresolvedType>, Option<Expression>) = match_or_unexpected!(self.step()?,
                    TokenType::Colon => {
                        let ty = self.parse_type()?;
                        (
                            Some(ty),
                            match_or_unexpected!{self.step()?, 
                                TokenType::Operator(Operator::Assign) => {
                                    let expr = self.parse_expression()?;
                                    Some(expr)
                                },
                                TokenType::Semicolon => None
                            }
                        )
                    },
                    TokenType::Operator(Operator::Declare) => {
                        let expr = self.parse_expression()?;
                        (None, Some(expr))
                    }
                );
                tok_expect!(self.step()?, TokenType::Semicolon);

                Some(BlockItem::Declare(name, ty, val))
            },
            _ => None
        };
        if let Some(item) = block_item {
            Ok(item)
        } else {
            let expr = BlockItem::Expression(self.parse_expression()?);
            tok_expect!(self.step()?, TokenType::Semicolon);
            Ok(expr)
        }
    }

    fn parse_expression(&mut self) -> Result<Expression, EyeError> {
        println!("Parsing expression...");
        let first = self.step()?;
        Ok(match_or_unexpected!(first,
            TokenType::Keyword(Keyword::Ret)   => Expression::Return(Box::new(self.parse_expression()?)),
            TokenType::IntLiteral              => Expression::IntLiteral(IntLiteral::from_tok(first)?),
            TokenType::FloatLiteral            => Expression::FloatLiteral(FloatLiteral::from_tok(first)?),
            TokenType::StringLiteral           => Expression::StringLiteral(first.get_val()),
            TokenType::Keyword(Keyword::True)  => Expression::BoolLiteral(true),
            TokenType::Keyword(Keyword::False) => Expression::BoolLiteral(false),
            TokenType::Ident                   => Expression::Variable(first.get_val())
        ))
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