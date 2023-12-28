use id::ModuleId;

use crate::{Compiler, Def, parser::{ast::{ExprId, ScopeId, Expr}, token::IntLiteral}};

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
    compiler: &mut Compiler,
    module: ModuleId,
    scope: ScopeId,
    expr: ExprId,
) -> Def {
    let (ast, symbols) = compiler.get_module_ast_and_symbols(module);
    let ast = ast.clone();
    match &ast[expr] {
        Expr::IntLiteral(span) => {
            let lit = IntLiteral::parse(&ast[*span]);
            let Ok(val) = lit.val.try_into() else { todo!("handle large constants") };
            Def::ConstValue(compiler.add_const_value(ConstValue::Number(val)))
        }
        Expr::Variable { span, id: _ } => {
            let name = &ast[*span];
            compiler.resolve_in_scope(module, scope, name, span.in_mod(module))
        }
        Expr::ReturnUnit { .. } => Def::ConstValue(compiler.add_const_value(ConstValue::Unit)),
        &Expr::Return { val, .. } => def_expr(compiler, module, scope, val),
        &Expr::Function { id } => Def::Function(module, id),
        &Expr::Type { id } => {
            if let Some(id) = symbols.types[id.idx()] {
                Def::Type(id)
            } else {
                let id = compiler.add_type_def(module, id);
                compiler.get_module_ast_and_symbols(module).1.types[id.idx()] = Some(id);
                Def::Type(id)
            }
        }
        expr => todo!("eval expr {expr:?}")
    }
}

/*
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
*/
