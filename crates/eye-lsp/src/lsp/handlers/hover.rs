use compiler::{compiler::BodyOrTypes, typing::LocalTypeId};
use error::span::TSpan;
use parser::ast::Ast;

use crate::{
    lsp::{
        Lsp,
        find_in_ast::{FoundType, ScopeContext},
    },
    types::{
        Range,
        request::{Hover, HoverContents, HoverParams, MarkedString},
    },
};

impl Lsp {
    pub fn hover(&mut self, hover: HoverParams) -> Hover {
        let Some((module, _offset, found)) = self.find_document_position(&hover.position) else {
            return Hover::default();
        };
        let ast = self.compiler.get_module_ast(module);
        let hover = |contents| Hover {
            contents,
            range: Some(Range::from_span(found.span, ast.src())),
        };
        match found.ty {
            FoundType::None => Hover::default(),
            FoundType::Error => hover("syntax error".into()),
            FoundType::Ident | FoundType::Literal | FoundType::EnumLiteral => {
                let context = self.find_context_for_scope(module, found.scope);
                match context {
                    ScopeContext::TopLevel => Hover::default(),
                    ScopeContext::Function(function_id) => {
                        let ast = self.compiler.get_module_ast(module);
                        let mut hooks = HoverHooks {
                            span: found.span,
                            ast,
                            ty: None,
                        };
                        let checked = compiler::check::function(
                            &self.compiler,
                            module,
                            function_id,
                            &mut hooks,
                        );
                        let BodyOrTypes::Body(hir) = checked.body_or_types else {
                            return Hover::default();
                        };
                        let signature = self.compiler.get_signature(module, function_id);
                        let ty = match hooks.ty {
                            Some(ty) => self
                                .compiler
                                .types
                                .display(hir[ty], &signature.generics)
                                .to_string(),
                            None => "<unknown type>".to_owned(),
                        };
                        let val = &ast.src()[found.span.range()];
                        Hover {
                            contents: HoverContents::MarkedString(MarkedString::Code {
                                language: "eye".into(),
                                value: format!("{val}: {ty}"),
                            }),
                            range: Some(Range::from_span(found.span, ast.src())),
                        }
                    }
                }
            }
            // FoundType::Literal => todo!(),
            // FoundType::EnumLiteral => todo!(),
            FoundType::Primitive(_) => hover(HoverContents::MarkedStrings(vec![
                MarkedString::String("primitive type ".to_owned()),
                MarkedString::Code {
                    language: "eye".into(),
                    value: ast.src()[found.span.range()].to_owned(),
                },
            ])),
            // FoundType::Path(_) => todo!(),
            // FoundType::TypePlaceholder => todo!(),
            // FoundType::Underscore => todo!(),
            // FoundType::RootModule => todo!(),
            // FoundType::Member => todo!(),
            // FoundType::ParameterName => todo!(),
            FoundType::Keyword => hover(HoverContents::MarkedStrings(vec![
                MarkedString::String("Keyword ".into()),
                MarkedString::Code {
                    language: "eye".into(),
                    value: ast.src()[found.span.range()].to_owned(),
                },
            ])),
            // FoundType::Generic => todo!(),
            _ => hover(format!("TODO: implement hover type {found:?}").into()),
        }
    }
}

struct HoverHooks<'a> {
    span: TSpan,
    ast: &'a Ast,
    ty: Option<LocalTypeId>,
}
impl<'a> compiler::check::Hooks for HoverHooks<'a> {
    fn on_check_expr(
        &mut self,
        expr: parser::ast::ExprId,
        _scope: &mut compiler::compiler::LocalScope,
        ty: compiler::typing::LocalTypeId,
        _return_ty: compiler::typing::LocalTypeId,
        _noreturn: &mut bool,
    ) {
        if self.ast[expr].span(self.ast) != self.span {
            return;
        }
        self.ty = Some(ty);
    }

    fn on_checked_lvalue(
        &mut self,
        expr: parser::ast::ExprId,
        _scope: &mut compiler::compiler::LocalScope,
        ty: LocalTypeId,
    ) {
        if self.ast[expr].span(self.ast) != self.span {
            return;
        }
        self.ty = Some(ty);
    }

    fn on_check_pattern(&mut self, expr: parser::ast::ExprId, ty: LocalTypeId) {
        if self.ast[expr].span(self.ast) != self.span {
            return;
        }
        self.ty = Some(ty);
    }
}
