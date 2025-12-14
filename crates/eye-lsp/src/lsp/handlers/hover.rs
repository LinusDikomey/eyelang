use std::fmt::Write;

use compiler::{
    Compiler, Def,
    compiler::{BodyOrTypes, LocalItem, LocalScope, VarId},
    hir::HIRBuilder,
    typing::LocalTypeId,
};
use error::span::TSpan;
use parser::ast::{Ast, ExprId};

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
        let context = self.find_context_for_scope(module, found.scope);
        let ast = self.compiler.get_module_ast(module);
        let hover = |contents| Hover {
            contents,
            range: Some(Range::from_span(found.span, ast.src())),
        };
        match found.ty {
            FoundType::None => Hover::default(),
            FoundType::Error => hover("syntax error".into()),
            FoundType::Ident | FoundType::Literal | FoundType::EnumLiteral => {
                let is_ident = matches!(found.ty, FoundType::Ident);
                match context {
                    ScopeContext::TopLevel => Hover::default(),
                    ScopeContext::Function(function_id) => {
                        let ast = self.compiler.get_module_ast(module);
                        let mut hooks = HoverHooks {
                            span: found.span,
                            ast,
                            local_item: None,
                            ty: None,
                            compiler: &self.compiler,
                            is_ident,
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
                        let hover_var = |var: VarId| {
                            let ty = hir.vars[var.idx()].ty();
                            let val = &ast.src()[found.span.range()];
                            let ty = self
                                .compiler
                                .types
                                .display(hir[ty], &signature.generics)
                                .to_string();
                            let mut text = format!("```eye\n{val}: {ty}\n```");
                            if let compiler::hir::Var::Capture { outer, .. } = hir.vars[var.idx()] {
                                write!(text, "\n---\nCapture of #{}", outer.0).unwrap();
                            }
                            Hover {
                                contents: text.into(),
                                range: Some(Range::from_span(found.span, ast.src())),
                            }
                        };
                        let val = &ast.src()[found.span.range()];
                        let Some(item) = hooks.local_item else {
                            let Some(ty) = hooks.ty else {
                                return hover("expr not found".into());
                            };
                            let ty = self.compiler.types.display(hir[ty], &signature.generics);
                            return hover(format!("{val} : {ty}").into());
                        };
                        match item {
                            LocalItem::Var(var_id) => hover_var(var_id),
                            LocalItem::Invalid | LocalItem::Def(Def::Invalid) => {
                                hover("<invalid value>".into())
                            }
                            LocalItem::Def(Def::Function(function_module, function)) => {
                                let signature =
                                    self.compiler.get_signature(function_module, function);
                                let mut text = format!("```eye\n{val} :: fn");
                                if signature.generics.count() > 0 {
                                    text.push('[');
                                    for i in 0..signature.generics.count() {
                                        if i != 0 {
                                            text.push_str(", ");
                                        }
                                        // TODO: not displaying bounds here for now, should be
                                        // displayed here or in where clause when it is supported
                                        text.push_str(signature.generics.get_name(i));
                                    }
                                    text.push(']');
                                }
                                if signature.params.len() + signature.named_params.len() > 0 {
                                    let mut first = true;
                                    let mut param_delimiter = |text: &mut String| {
                                        if first {
                                            first = false;
                                        } else {
                                            text.push_str(", ");
                                        }
                                    };
                                    text.push('(');
                                    for (name, ty) in &signature.params {
                                        param_delimiter(&mut text);
                                        write!(
                                            text,
                                            "{name} {}",
                                            self.compiler.types.display(*ty, &signature.generics),
                                        )
                                        .unwrap();
                                    }
                                    for (name, ty, _default) in &signature.named_params {
                                        param_delimiter(&mut text);
                                        write!(
                                            text,
                                            "{name} {} = <TODO: display default>",
                                            self.compiler.types.display(*ty, &signature.generics)
                                        )
                                        .unwrap();
                                    }
                                    text.push(')');
                                }
                                hover(text.into())
                            }
                            // TODO: handle each case separately and produce proper hover text
                            LocalItem::Def(def) => hover(format!("Definition {def:?}").into()),
                        }
                    }
                }
            }
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
    compiler: &'a Compiler,
    local_item: Option<LocalItem>,
    ty: Option<LocalTypeId>,
    is_ident: bool,
}
impl<'a> HoverHooks<'a> {
    fn handle_hovered_expr(
        &mut self,
        _expr: ExprId,
        hir: &mut HIRBuilder,
        scope: &mut LocalScope,
        ty: LocalTypeId,
        is_pattern: bool,
    ) {
        let name = &self.ast.src()[self.span.range()];
        self.ty = Some(ty);
        if self.is_ident && !is_pattern {
            // TODO: this should probably not emit errors
            let item = scope.resolve(name, self.span, self.compiler, hir);
            self.local_item = Some(item);
        }
    }
}
impl<'a> compiler::check::Hooks for HoverHooks<'a> {
    fn on_check_expr(
        &mut self,
        expr: parser::ast::ExprId,
        hir: &mut HIRBuilder,
        scope: &mut compiler::compiler::LocalScope,
        ty: compiler::typing::LocalTypeId,
        _return_ty: compiler::typing::LocalTypeId,
        _noreturn: &mut bool,
    ) {
        if self.ast[expr].span(self.ast) != self.span {
            return;
        }
        self.handle_hovered_expr(expr, hir, scope, ty, false);
    }

    fn on_checked_lvalue(
        &mut self,
        expr: parser::ast::ExprId,
        hir: &mut HIRBuilder,
        scope: &mut compiler::compiler::LocalScope,
        ty: LocalTypeId,
    ) {
        if self.ast[expr].span(self.ast) != self.span {
            return;
        }
        self.handle_hovered_expr(expr, hir, scope, ty, false);
    }

    fn on_check_pattern(
        &mut self,
        expr: ExprId,
        hir: &mut HIRBuilder,
        scope: &mut LocalScope,
        ty: LocalTypeId,
    ) {
        if self.ast[expr].span(self.ast) != self.span {
            return;
        }
        self.handle_hovered_expr(expr, hir, scope, ty, true);
    }
}
