use id::ModuleId;
use types::{Primitive, Type};

use crate::{
    error::Error,
    parser::{
        ast::{Ast, Expr, ExprId, ScopeId},
        token::{FloatLiteral, IntLiteral},
    },
    type_table::{TypeInfo, TypeTable},
    Compiler, Def,
};

#[derive(Debug, Clone)]
pub enum ConstValue {
    /// represents an undefined value, for example when a global is not initialized
    Undefined,
    Unit,
    Bool(bool),
    Int(u64),
    Float(f64),
}
impl ConstValue {
    pub fn dump(&self) {
        match self {
            Self::Undefined => print!("undefined"),
            Self::Unit => print!("()"),
            Self::Bool(b) => print!("{b}"),
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
    name: &str,
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
        &Expr::Return { val, .. } => def_expr(compiler, module, scope, ast, val, name),
        &Expr::Function { id } => Def::Function(module, id),
        &Expr::Type { id } => {
            let symbols = &mut compiler.get_module_ast_and_symbols(module).symbols;
            let id = if let Some(id) = symbols.types[id.idx()] {
                id
            } else {
                let assigned_id = compiler.add_type_def(module, id, name.into());
                compiler.get_module_ast_and_symbols(module).symbols.types[id.idx()] =
                    Some(assigned_id);
                assigned_id
            };
            // TODO: check/pass generics somehow
            Def::Type(Type::DefId { id, generics: None })
        }
        &Expr::Primitive { primitive, .. } => Def::Type(Type::Primitive(primitive)),
        _ => {
            let mut types = TypeTable::new();
            let expected = types.add_unknown();
            let (hir, types) =
                crate::check::check(compiler, ast, module, types, scope, [], expr, expected);
            let mut to_generate = Vec::new();
            let mut ir_types = ir::IrTypes::new();
            let builder = ir::builder::IrBuilder::new(&mut ir_types);
            let mut vars = vec![(ir::Ref::UNDEF, ir::TypeRef::NONE); hir.vars.len()];
            let ir = crate::irgen::lower_hir(
                builder,
                &hir,
                &types,
                compiler,
                &mut to_generate,
                &[],
                ir::TypeRefs::EMPTY,
                &mut vars,
            );
            use ir::Val;
            match ir::eval(&ir, &ir_types, &[]) {
                Ok(val) => {
                    let const_val = match val {
                        Val::Invalid => panic!("internal error during evaluation occured"),
                        Val::Unit => ConstValue::Unit,
                        Val::Int(n)
                            if matches!(types[expected], TypeInfo::Primitive(Primitive::Bool)) =>
                        {
                            debug_assert!(n < 2);
                            ConstValue::Bool(n != 0)
                        }
                        Val::Int(n) => ConstValue::Int(n),
                        Val::F32(n) => ConstValue::Float(n as f64),
                        Val::F64(n) => ConstValue::Float(n),
                        Val::StackPointer(_) => {
                            compiler.errors.emit_err(
                                Error::EvalReturnedStackPointer
                                    .at_span(ast[expr].span(ast).in_mod(module)),
                            );
                            return Def::Invalid;
                        }
                    };
                    Def::ConstValue(compiler.add_const_value(const_val))
                }
                Err(err) => {
                    compiler.errors.emit_err(
                        Error::EvalFailed(err).at_span(ast[expr].span(ast).in_mod(module)),
                    );
                    Def::Invalid
                }
            }
        }
    }
}
