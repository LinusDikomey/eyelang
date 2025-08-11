pub mod ast;
mod parse;
pub mod token;
mod tokenize;

use dmap::DHashMap;

use id::ModuleId;

use crate::{
    error::{CompileError, Errors},
    parser::tokenize::Tokenizer,
};

use self::{ast::Definition, token::TokenType};

pub fn parse(
    source: Box<str>,
    errors: &mut Errors,
    module: ModuleId,
    definitions: DHashMap<String, Definition>,
) -> ast::Ast {
    let mut ast_builder = ast::AstBuilder::new();
    let mut parser = Parser {
        ast: &mut ast_builder,
        toks: Tokenizer::new(&source, module, errors),
    };

    let scope = parser.parse_module(definitions);
    ast_builder.finish_with_top_level_scope(source, scope)
}

type ParseResult<T> = Result<T, CompileError>;

struct Parser<'a> {
    ast: &'a mut ast::AstBuilder,
    toks: tokenize::Tokenizer<'a>,
}

/// Represents the necessity of delimiters in delimited lists
#[derive(Debug)]
pub enum Delimit {
    /// Require a delimiter between elements
    Yes,
    /// Don't expect a delimiter
    No,
    /// The delimiter may be omitted
    Optional,
    /// delimiter may be omitted if the next entry starts on a new line
    OptionalIfNewLine,
}
impl From<()> for Delimit {
    fn from((): ()) -> Self {
        Self::Yes
    }
}

#[derive(Debug, Clone)]
pub enum ExpectedTokens {
    Specific(TokenType),
    AnyOf(Box<[TokenType]>),
    Expr,
    Type,
    Item,
    EndOfMultilineComment,
    EndOfStringLiteral,
}
impl std::fmt::Display for ExpectedTokens {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            &Self::Specific(tok) => {
                write!(f, "{tok}")
            }
            Self::AnyOf(toks) => {
                for (i, tok) in toks.iter().enumerate() {
                    match i {
                        0 => {}
                        i if i != 0 || i == toks.len() - 1 => {
                            write!(f, " or ")?;
                        }
                        _ => write!(f, ", ")?,
                    }
                    write!(f, "{tok}")?;
                }
                Ok(())
            }
            Self::Expr => write!(f, "an expression"),
            Self::Type => write!(f, "a type"),
            Self::Item => write!(f, "an item"),
            Self::EndOfMultilineComment => write!(f, "end of comment"),
            Self::EndOfStringLiteral => write!(f, "end of string literal"),
        }
    }
}

#[derive(Clone, Copy)]
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

impl<const N: usize> From<TokenTypes<N>> for ExpectedTokens {
    fn from(t: TokenTypes<N>) -> Self {
        match t.0.as_slice() {
            [t] => Self::Specific(*t),
            other => Self::AnyOf(other.into()),
        }
    }
}
impl From<TokenType> for ExpectedTokens {
    fn from(value: TokenType) -> Self {
        Self::Specific(value)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        error::Errors,
        parser::ast::{Ast, Definition, Expr},
    };

    fn test_parse(s: &str) -> Ast {
        let mut errors = Errors::new();
        errors.enable_crash_on_error();
        super::parse(s.into(), &mut errors, id::ModuleId(0), dmap::new())
    }

    #[test]
    fn parse_function() {
        let ast = test_parse("f :: fn { x := 3 }");
        let scope = &ast[ast.top_level_scope_id()];
        assert_eq!(scope.definitions.len(), 1);
        let Definition::Expr(f_def) = scope.definitions["f"] else {
            panic!("expected definition f");
        };
        let Expr::Function { id } = ast[ast[f_def].0] else {
            panic!("expected function definition");
        };
        let body = ast[id].body.unwrap();
        let Expr::Block { scope, items } = ast[body] else {
            panic!("expected body");
        };
        assert_eq!(items.count, 1);
        assert_eq!(ast[scope].definitions.len(), 0);
    }
}
