use id::ModuleId;
use types::Type;

use crate::{
    parser::{
        ast::{Ast, Expr, ExprId, ScopeId},
        token::{FloatLiteral, IntLiteral},
    },
    Compiler, Def,
};

#[derive(Debug, Clone)]
pub enum ConstValue {
    /// represents an undefined value, for example when a global is not initialized
    Undefined,
    Unit,
    Int(u64),
    Float(f64),
}
impl ConstValue {
    pub fn dump(&self) {
        match self {
            Self::Undefined => print!("undefined"),
            Self::Unit => print!("()"),
            Self::Int(n) => print!("{n}"),
            Self::Float(n) => print!("{n}"),
        }
    }
}

pub fn def_expr(
    compiler: &mut Compiler,
    module: ModuleId,
    scope: ScopeId,
    ast: &Ast,
    expr: ExprId,
) -> Def {
    match &ast[expr] {
        &Expr::IntLiteral(span) => {
            let lit = IntLiteral::parse(&ast[span]);
            let Ok(val) = lit.val.try_into() else {
                todo!("handle large constants")
            };
            Def::ConstValue(compiler.add_const_value(ConstValue::Int(val)))
        }
        &Expr::FloatLiteral(span) => {
            let lit = FloatLiteral::parse(&ast[span]);
            Def::ConstValue(compiler.add_const_value(ConstValue::Float(lit.val)))
        }
        Expr::Ident { span } => {
            let name = &ast[*span];
            compiler.resolve_in_scope(module, scope, name, span.in_mod(module))
        }
        Expr::ReturnUnit { .. } => Def::ConstValue(compiler.add_const_value(ConstValue::Unit)),
        &Expr::Return { val, .. } => def_expr(compiler, module, scope, ast, val),
        &Expr::Function { id } => Def::Function(module, id),
        &Expr::Type { id } => {
            let symbols = &mut compiler.get_module_ast_and_symbols(module).symbols;
            let id = if let Some(id) = symbols.types[id.idx()] {
                id
            } else {
                let assigned_id = compiler.add_type_def(module, id);
                compiler.get_module_ast_and_symbols(module).symbols.types[id.idx()] =
                    Some(assigned_id);
                assigned_id
            };
            // TODO: check/pass generics somehow
            Def::Type(Type::DefId { id, generics: None })
        }
        &Expr::Primitive { primitive, .. } => Def::Type(Type::Primitive(primitive)),
        expr => {
            /*
            let mut ir_types = ir::IrTypes::new();
            let mut ir = ir::builder::IrBuilder::new(&mut ir_types);
            let mut to_generate = Vec::new();
            crate::irgen::lower_function(compiler, &mut to_generate, src, name, checked, generics)
            */
            todo!("generate and evaluate ir for {expr:?}")
        }
    }
}
