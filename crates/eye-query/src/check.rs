use types::Primitive;

use crate::{Compiler, parser::{ast::{Ast, ExprId, Expr}, token::IntLiteral}, compiler::{LocalScope, Ident, LocalItem, Def, Vars}, type_table::{TypeTable, TypeInfo, LocalTypeId}, eval::ConstValue, hir::{HIR, self, HIRBuilder, Node}};

impl Compiler {
    pub fn typecheck_expr(
        &mut self,
        ast: &Ast,
        expr: ExprId,
        scope: &mut LocalScope,
        hir: &mut HIRBuilder,
        expected: LocalTypeId,
        return_ty: LocalTypeId,
    ) -> Node {
        match &ast[expr] {
            Expr::IntLiteral(span) => {
                let lit = IntLiteral::parse(&ast.src()[span.range()]);
                let info = lit.ty.map_or(
                    TypeInfo::Integer,
                    |int| TypeInfo::Primitive(int.into()),
                );
                hir.types.specify(expected, info);
                Node::IntLiteral { val: lit.val, ty: expected }
            }
            &Expr::Variable { span, id: _ } => {
                let name = &ast[span];
                match scope.resolve(name, span, self) {
                    LocalItem::Var(var) => {
                        let ty = hir.get_var(var);
                        hir.types.unify(expected, ty);
                        Node::Variable(var)
                    }
                    LocalItem::Def(def) => match def {
                        Def::Function(_, _) => todo!("function items"),
                        Def::Type(_) => todo!("type type?"),
                        Def::ConstValue(const_val) => {
                            match &self.const_values[const_val.idx()] {
                                ConstValue::Undefined => todo!("should this invalidate the type?"),
                                ConstValue::Unit => {
                                    hir.types.specify(expected, TypeInfo::Primitive(Primitive::Unit));
                                }
                                ConstValue::Number(_) => hir.types.specify(expected, TypeInfo::Primitive(Primitive::I32)),
                            }
                            Node::Const(const_val)
                        }
                        Def::Module(_) => panic!("value expected but found module"),
                        Def::Global(_, _) => todo!("globals"),
                        Def::Invalid => {
                            hir.types.specify(expected, TypeInfo::Invalid);
                            Node::Invalid
                        }
                    }
                    LocalItem::Invalid => {
                        hir.types.specify(expected, TypeInfo::Invalid);
                        Node::Invalid
                    }
                }
            }
            Expr::ReturnUnit { .. } => {
                hir.types.specify(return_ty, TypeInfo::Primitive(Primitive::Unit));
                Node::Return(hir.add(Node::Unit))
            }
            &Expr::Return { val, .. } => {
                let val = self.typecheck_expr(ast, val, scope, hir, return_ty, return_ty);
                Node::Return(hir.add(val))
            }
            Expr::Function { id: _ } => todo!("function items (+ closures)"),
            Expr::Type { id: _ } => todo!("type type?"),
            &Expr::Block { scope: static_scope, items } => {
                let mut scope = LocalScope {
                    parent: Some(scope),
                    variables: dmap::new(),
                    module: scope.module,
                    static_scope,
                };
                // PERF: should preallocate in nodes list and put them in directly
                let items = items
                    .into_iter()
                    .map(|item| {
                        let unknown = hir.types.add_unknown();
                        self.typecheck_expr(ast, item, &mut scope, hir, unknown, return_ty)
                    })
                    .collect::<Vec<_>>();
                Node::Block(hir.add_nodes(items))
            }
            expr => todo!("typecheck {expr:?}")
        }
    }
}
