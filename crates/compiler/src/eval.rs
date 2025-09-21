use std::{num::NonZeroU64, rc::Rc};

use error::Error;
use ir::eval::Val;
use parser::ast::{
    Ast, Expr, ExprId, FloatLiteral, IntLiteral, ModuleId, Primitive, ScopeId, UnresolvedType,
};

use crate::{
    Compiler, Def, TypeOld,
    compiler::{Generics, ModuleSpan, ResolvedPrimitive},
    hir::HIRBuilder,
    irgen,
    typing::TypeTable,
};

id::id!(ConstValueId);

#[derive(Debug, Clone)]
pub enum ConstValue {
    /// represents an undefined value, for example when a global is not initialized
    Undefined,
    Unit,
    Int(u64),
    Float(f64),
    Aggregate(Box<[ConstValue]>),
}
impl ConstValue {
    pub fn dump(&self) {
        match self {
            Self::Undefined => print!("undefined"),
            Self::Unit => print!("()"),
            Self::Int(n) => {
                print!("{n}");
            }
            Self::Float(n) => {
                print!("{n}");
            }
            Self::Aggregate(elems) => {
                print!("(");
                for (i, elem) in elems.iter().enumerate() {
                    if i != 0 {
                        print!(", ");
                    }
                    elem.dump();
                }
            }
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
    ty: &UnresolvedType,
) -> Def {
    let mismatched_type = |compiler: &mut Compiler, found| {
        let mut expected = String::new();
        ty.to_string(&mut expected, ast.src());
        compiler.errors.emit(
            module,
            Error::MismatchedType { expected, found }.at_span(ast[expr].span(ast)),
        );
    };
    // TODO: support untyped number constants again
    match &ast[expr] {
        &Expr::IntLiteral { span, .. } => {
            let lit = IntLiteral::parse(&ast[span]);
            let Ok(val) = lit.val.try_into() else {
                todo!("handle large constants")
            };
            let val = ConstValue::Int(val);

            match compiler.unresolved_primitive(ty, module, scope) {
                ResolvedPrimitive::Primitive(p) if p.is_int() => {
                    Def::ConstValue(compiler.add_const_value(val, TypeOld::Primitive(p)))
                }
                ResolvedPrimitive::Infer => {
                    Def::ConstValue(compiler.add_const_value(val, TypeOld::Primitive(Primitive::I32)))
                }
                ResolvedPrimitive::Invalid => Def::Invalid,
                _ => {
                    mismatched_type(compiler, "an integer".to_owned());
                    Def::Invalid
                }
            }
        }
        &Expr::FloatLiteral { span, .. } => {
            let lit = FloatLiteral::parse(&ast[span]);
            let val = ConstValue::Float(lit.val);
            match compiler.unresolved_primitive(ty, module, scope) {
                ResolvedPrimitive::Primitive(p) if p.is_float() => {
                    Def::ConstValue(compiler.add_const_value(val, TypeOld::Primitive(p)))
                }
                ResolvedPrimitive::Infer => {
                    Def::ConstValue(compiler.add_const_value(val, TypeOld::Primitive(Primitive::F32)))
                }
                ResolvedPrimitive::Invalid => Def::Invalid,
                _ => {
                    mismatched_type(compiler, "a float".to_owned());
                    Def::Invalid
                }
            }
        }
        &Expr::Ident { span, .. } => {
            let name = &ast[span];
            let def = compiler.resolve_in_scope(module, scope, name, ModuleSpan { module, span });
            match def.check_with_type(module, scope, compiler, ty) {
                Ok(def) => def,
                Err(found) => {
                    if let Some(found) = found {
                        mismatched_type(compiler, found.to_owned());
                    }
                    Def::Invalid
                }
            }
        }
        Expr::ReturnUnit { .. } => {
            let ty = compiler.resolve_type(ty, module, scope);
            if !matches!(&ty, TypeOld::Tuple(elems) if elems.is_empty()) {
                mismatched_type(compiler, TypeOld::Tuple(Box::new([])).to_string());
                return Def::Invalid;
            }
            Def::ConstValue(compiler.add_const_value(ConstValue::Unit, ty))
        }
        &Expr::Return { val, .. } => def_expr(compiler, module, scope, ast, val, name, ty),
        &Expr::Function { id } => {
            if compiler
                .check_signature_with_type((module, id), ty, scope, module)
                .is_ok()
            {
                Def::Function(module, id)
            } else {
                Def::Invalid
            }
        }
        &Expr::Type { id } => {
            let Ok(matches) =
                compiler.unresolved_matches_primitive(ty, Primitive::Type, module, scope)
            else {
                return Def::Invalid;
            };
            if !matches {
                mismatched_type(compiler, Primitive::Type.to_string());
                return Def::Invalid;
            }
            let symbols = &mut compiler.get_parsed_module(module).symbols;
            let (id, generic_count) = if let Some(id) = symbols.types[id.idx()] {
                (id, compiler.get_resolved_type_generic_count(id))
            } else {
                let generic_count = ast[id].generic_count();
                let assigned_id = compiler.add_type_def(module, id, name.into(), generic_count);
                compiler.get_parsed_module(module).symbols.types[id.idx()] = Some(assigned_id);
                (assigned_id, generic_count)
            };
            if generic_count == 0 {
                Def::Type(TypeOld::DefId {
                    id,
                    generics: Box::new([]),
                })
            } else {
                Def::GenericType(id)
            }
        }
        &Expr::Trait { id } => {
            if !matches!(ty, UnresolvedType::Infer(_)) {
                mismatched_type(compiler, "a trait".to_owned());
                return Def::Invalid;
            }
            Def::Trait(module, id)
        }
        &Expr::Primitive { primitive, .. } => {
            let Ok(matches) =
                compiler.unresolved_matches_primitive(ty, Primitive::Type, module, scope)
            else {
                return Def::Invalid;
            };
            if !matches {
                mismatched_type(compiler, Primitive::Type.to_string());
                return Def::Invalid;
            }
            Def::Type(TypeOld::Primitive(primitive))
        }
        _ => {
            tracing::debug!(target: "eval", "Running evaluator for definition of {name}:");
            match value_expr(compiler, module, scope, ast, expr, ty) {
                Ok((val, ty)) => Def::ConstValue(compiler.add_const_value(val, ty)),
                Err(err) => {
                    compiler
                        .errors
                        .emit(module, Error::EvalFailed(err).at_span(ast[expr].span(ast)));
                    Def::Invalid
                }
            }
        }
    }
}

pub fn value_expr(
    compiler: &mut Compiler,
    module: ModuleId,
    scope: ScopeId,
    ast: &Ast,
    expr: ExprId,
    ty: &UnresolvedType,
) -> Result<(ConstValue, TypeOld), ir::eval::Error> {
    let mut types = TypeTable::new();
    let expected = types.info_from_unresolved(ty, compiler, module, scope);
    let expected = types.add(expected);
    let hir = HIRBuilder::new(types);
    let (hir, types) = crate::check::check(
        compiler,
        ast,
        module,
        &Generics::EMPTY,
        scope,
        hir,
        [],
        expr,
        expected,
        crate::compiler::LocalScopeParent::None,
    );
    let ty = types.to_resolved(types[expected], &[]);
    if let crate::hir::Node::Invalid = hir[hir.root_id()] {
        return Ok((ConstValue::Undefined, ty));
    }

    let mut to_generate = Vec::new();
    let mut builder = ir::builder::Builder::new(&mut *compiler);
    builder.create_and_begin_block([]);
    let Some(return_ty) = crate::irgen::types::get_from_info(
        builder.env,
        &types,
        &mut builder.types,
        types[expected],
        crate::irgen::types::Generics::Empty,
    ) else {
        return Ok((ConstValue::Undefined, ty));
    };
    let return_ty = builder.types.add(return_ty);
    let (ir, ir_types) = crate::irgen::lower_hir(
        builder,
        &hir,
        &types,
        &mut to_generate,
        &[],
        ir::Refs::EMPTY,
        return_ty,
    );
    while let Some(f) = to_generate.pop() {
        let checked = Rc::clone(compiler.get_hir(f.module, f.ast_function_id));

        if let Some(body) = &checked.body {
            let return_type = compiler.ir[f.ir_id].return_type().unwrap();
            let (builder, params) = ir::builder::Builder::begin_function(&mut *compiler, f.ir_id);
            let res = irgen::lower_hir(
                builder,
                body,
                &checked.types,
                &mut to_generate,
                &f.generics,
                params,
                return_type,
            );
            compiler.ir.attach_body(f.ir_id, res);
        }
    }
    let mut env = LazyEvalEnv { compiler };
    ir::eval::eval(&ir, &ir_types, &[], &mut env).map(|val| (to_const_val(val), ty))
}

fn to_const_val(val: Val) -> ConstValue {
    match val {
        Val::Invalid => ConstValue::Undefined,
        Val::Unit => ConstValue::Unit,
        Val::Int(n) => ConstValue::Int(n),
        Val::F32(n) => ConstValue::Float(n as f64),
        Val::F64(n) => ConstValue::Float(n),
        Val::Ptr(_) => todo!("handle constants with compile-time pointers"),
        Val::Array(elems) | Val::Tuple(elems) => {
            ConstValue::Aggregate(elems.into_iter().map(to_const_val).collect())
        }
    }
}

struct LazyEvalEnv<'a> {
    compiler: &'a mut Compiler,
}
impl ir::eval::EvalEnvironment for LazyEvalEnv<'_> {
    fn env(&self) -> &ir::Environment {
        &self.compiler.ir
    }

    fn env_mut(&mut self) -> &mut ir::Environment {
        &mut self.compiler.ir
    }

    fn debug(&self) -> bool {
        #[cfg(debug_assertions)]
        {
            tracing::enabled!(target: "foo", tracing::Level::DEBUG)
        }
        #[cfg(not(debug_assertions))]
        {
            false
        }
    }

    fn call_extern(
        &mut self,
        id: ir::FunctionId,
        args: &[Val],
        mem: &mut ir::eval::Mem,
    ) -> Result<Val, Box<str>> {
        let func = &self.compiler.ir[id];
        Ok(match &*func.name {
            "malloc" => {
                let &[Val::Int(size)] = args else {
                    return Err("invalid signature for malloc".into());
                };
                let ptr = mem
                    .malloc(ir::Layout {
                        size,
                        align: NonZeroU64::new(16).unwrap(),
                    })
                    .map_err(|_| "out of compile-time memory")?;
                Val::Ptr(ptr)
            }
            name => {
                return Err(
                    format!("Can't evaluate extern function {name} at compile-time").into(),
                );
            }
        })
    }
}
