pub mod ast;
mod parse;
mod tokenize;

use dmap::DHashMap;

use id::ModuleId;

use error::{CompileError, Error, Errors};
use span::Span;
use token::{ExpectedTokens, Token};
use tokenize::Tokenizer;

use self::ast::Definition;

fn unexpected(token: Token, module: ModuleId, expected: ExpectedTokens) -> CompileError {
    CompileError {
        err: Error::UnexpectedToken {
            expected,
            found: token.ty,
        },
        span: Span::new(token.start, token.end, module),
    }
}

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

#[cfg(test)]
mod tests {
    use crate::ast::{Ast, Definition, Expr};
    use error::Errors;

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
