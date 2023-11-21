use crate::{Expr, Compiler, Def, Ast, ResolvedTypeDef, parser::ast::ExprId};

pub enum ConstValue {
    Unit,
    Number(u64),
}
impl ConstValue {
    pub fn dump(&self) {
        match self {
            Self::Unit => print!("()"),
            Self::Number(n) => print!("{n}")
        }
    }
}

pub fn def_expr(
    expr: ExprId,
    ast: Ast,
    scope: id::ScopeId,
    compiler: &mut Compiler,
) -> Def {
    match &ast[expr] {
        &Expr::Number(n) => Def::ConstValue(compiler.add_const_value(ConstValue::Number(n))),
        Expr::Ident(name) => {
            // PERF: cloning name
            compiler.resolve_definition(scope, &name.clone()).expect("unresolved name")
        }
        Expr::Return(None) => Def::ConstValue(compiler.add_const_value(ConstValue::Unit)),
        &Expr::Return(Some(expr)) => def_expr(expr, ast, scope, compiler),
        &Expr::Function(id) => Def::Function(id),
        &Expr::Type(id) => Def::Type(id),
        Expr::Block { .. } => todo!("eval expr block for definition"),
    }
}

pub fn type_def(compiler: &mut Compiler, ty: id::TypeDefId) -> ResolvedTypeDef {
    match &compiler.type_defs[ty.idx()].ast {
        TypeDefAst::Struct { def, enclosing_scope } => {
            let enclosing_scope = *enclosing_scope;
            // PERF: cloning fields
            let fields = def.fields
                    .clone()
                    .iter()
                    .map(|(name, ty)| (name.clone(), compiler.resolve_type(ty, enclosing_scope)))
                    .collect();
            ResolvedTypeDef::Struct(crate::ResolvedStructDef {
                fields,
            })
        }
    }
}
