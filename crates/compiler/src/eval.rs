use std::{num::NonZeroU64, rc::Rc};

use id::ModuleId;
use ir::eval::Val;
use types::{FloatType, IntType, Primitive, Type, UnresolvedType};

use crate::{
    compiler::{Generics, ResolvedPrimitive},
    error::Error,
    hir::HIRBuilder,
    irgen,
    parser::{
        ast::{Ast, Expr, ExprId, ScopeId},
        token::{FloatLiteral, IntLiteral},
    },
    types::{TypeInfo, TypeTable},
    Compiler, Def,
};

#[derive(Debug, Clone)]
pub enum ConstValue {
    /// represents an undefined value, for example when a global is not initialized
    Undefined,
    Unit,
    Bool(bool),
    Int(u64, Option<IntType>),
    Float(f64, Option<FloatType>),
    Tuple(Box<[ConstValue]>),
    Typed(id::TypeId, Box<[ConstValue]>),
}
impl ConstValue {
    pub fn dump(&self) {
        match self {
            Self::Undefined => print!("undefined"),
            Self::Unit => print!("()"),
            Self::Bool(b) => print!("{b}"),
            Self::Int(n, ty) => {
                print!("{n}");
                if let Some(ty) = ty {
                    print!(": {ty}");
                }
            }
            Self::Float(n, ty) => {
                print!("{n}");
                if let Some(ty) = ty {
                    print!(": {ty}");
                }
            }
            Self::Tuple(elems) => {
                print!("(");
                for (i, elem) in elems.iter().enumerate() {
                    if i != 0 {
                        print!(", ");
                    }
                    elem.dump();
                }
            }
            Self::Typed(id, elems) => {
                print!("{id:?}(");
                for (i, elem) in elems.iter().enumerate() {
                    if i != 0 {
                        print!(", ");
                    }
                    elem.dump();
                }
            }
        }
    }

    /// returns a potentially changed ConstValue or Err with either an expected type or None in
    /// the case that something was invalid
    pub fn check_with_type(
        &self,
        module: ModuleId,
        scope: ScopeId,
        compiler: &mut Compiler,
        ty: &UnresolvedType,
    ) -> Result<Option<ConstValue>, Option<&'static str>> {
        match self {
            Self::Undefined => Ok(None),
            Self::Unit => {
                if compiler
                    .unresolved_matches_primitive(ty, Primitive::Unit, module, scope)
                    .map_err(|_| None)?
                {
                    Ok(None)
                } else {
                    Err(Some(Primitive::Unit.into()))
                }
            }
            Self::Bool(_) => {
                if compiler
                    .unresolved_matches_primitive(ty, Primitive::Bool, module, scope)
                    .map_err(|_| None)?
                {
                    Ok(None)
                } else {
                    Err(Some(Primitive::Bool.into()))
                }
            }
            &Self::Int(val, current_ty) => match compiler.unresolved_primitive(ty, module, scope) {
                ResolvedPrimitive::Infer => Ok(None),
                ResolvedPrimitive::Primitive(p) => {
                    if let Some(current) = current_ty {
                        if Primitive::from(current) == p {
                            Ok(None)
                        } else {
                            Err(Some(Primitive::from(current).into()))
                        }
                    } else if let Some(int_ty) = p.as_int() {
                        Ok(Some(ConstValue::Int(val, Some(int_ty))))
                    } else {
                        Err(Some("<integer>"))
                    }
                }
                ResolvedPrimitive::Invalid => Err(None),
                ResolvedPrimitive::Other => Err(Some("<integer>")),
            },
            &Self::Float(val, current_ty) => {
                match compiler.unresolved_primitive(ty, module, scope) {
                    ResolvedPrimitive::Infer => Ok(None),
                    ResolvedPrimitive::Primitive(p) => {
                        if let Some(current) = current_ty {
                            if Primitive::from(current) == p {
                                Ok(None)
                            } else {
                                Err(Some(Primitive::from(current).into()))
                            }
                        } else if let Some(float_ty) = p.as_float() {
                            Ok(Some(ConstValue::Float(val, Some(float_ty))))
                        } else {
                            Err(Some("<float>"))
                        }
                    }
                    ResolvedPrimitive::Other => Err(Some("<float>")),
                    ResolvedPrimitive::Invalid => Err(None),
                }
            }
            Self::Tuple(_) => todo!(),
            Self::Typed(_, _) => todo!(),
        }
    }

    pub fn ty(&self) -> Type {
        match self {
            ConstValue::Undefined => Type::Invalid,
            ConstValue::Unit => Type::Primitive(Primitive::Unit),
            ConstValue::Bool(_) => Type::Primitive(Primitive::Bool),
            ConstValue::Int(_, ty) => Type::Primitive(ty.map_or(Primitive::I32, Primitive::from)),
            ConstValue::Float(_, ty) => Type::Primitive(ty.map_or(Primitive::F32, Primitive::from)),
            ConstValue::Tuple(elems) => Type::Tuple(elems.iter().map(Self::ty).collect()),
            ConstValue::Typed(_, _) => todo!("generics from values with default types?"),
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
        compiler.errors.emit_err(
            Error::MismatchedType { expected, found }.at_span(ast[expr].span(ast).in_mod(module)),
        );
    };
    match &ast[expr] {
        &Expr::IntLiteral(span) => {
            let lit = IntLiteral::parse(&ast[span]);
            let Ok(val) = lit.val.try_into() else {
                todo!("handle large constants")
            };
            let val = ConstValue::Int(val, None);
            match val.check_with_type(module, scope, compiler, ty) {
                Ok(None) => Def::ConstValue(compiler.add_const_value(val)),
                Ok(Some(val)) => Def::ConstValue(compiler.add_const_value(val)),
                Err(found) => {
                    if let Some(found) = found {
                        mismatched_type(compiler, found.to_owned());
                    }
                    Def::Invalid
                }
            }
        }
        &Expr::FloatLiteral(span) => {
            let lit = FloatLiteral::parse(&ast[span]);
            let val = ConstValue::Float(lit.val, None);
            match val.check_with_type(module, scope, compiler, ty) {
                Ok(None) => Def::ConstValue(compiler.add_const_value(val)),
                Ok(Some(val)) => Def::ConstValue(compiler.add_const_value(val)),
                Err(found) => {
                    if let Some(found) = found {
                        mismatched_type(compiler, found.to_owned());
                    }
                    Def::Invalid
                }
            }
        }
        Expr::Ident { span } => {
            let name = &ast[*span];
            let def = compiler.resolve_in_scope(module, scope, name, span.in_mod(module));
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
            let Ok(matches) =
                compiler.unresolved_matches_primitive(ty, Primitive::Unit, module, scope)
            else {
                return Def::Invalid;
            };
            if !matches {
                mismatched_type(compiler, Primitive::Unit.to_string());
                return Def::Invalid;
            }
            Def::ConstValue(compiler.add_const_value(ConstValue::Unit))
        }
        &Expr::Return { val, .. } => def_expr(compiler, module, scope, ast, val, name, ty),
        &Expr::Function { id } => {
            if compiler
                .check_signature_with_type(
                    (module, id),
                    ty,
                    scope,
                    module,
                    ast[expr].span(ast).in_mod(module),
                )
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
                Def::Type(Type::DefId {
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
            Def::Type(Type::Primitive(primitive))
        }
        _ => match value_expr(compiler, module, scope, ast, expr, ty) {
            Ok(val) => Def::ConstValue(compiler.add_const_value(val)),
            Err(err) => {
                compiler
                    .errors
                    .emit_err(Error::EvalFailed(err).at_span(ast[expr].span(ast).in_mod(module)));
                Def::Invalid
            }
        },
    }
}

pub fn value_expr(
    compiler: &mut Compiler,
    module: ModuleId,
    scope: ScopeId,
    ast: &Ast,
    expr: ExprId,
    ty: &UnresolvedType,
) -> Result<ConstValue, ir::eval::Error> {
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
        return Ok(ConstValue::Undefined);
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
    ir::eval::eval(&ir, &ir_types, &[], &mut env)
        .map(|val| to_const_val(val, types[expected], &types))
}

fn to_const_val(val: Val, ty: TypeInfo, types: &TypeTable) -> ConstValue {
    match val {
        Val::Invalid => ConstValue::Undefined,
        Val::Unit => ConstValue::Unit,
        Val::Int(n) if matches!(ty, TypeInfo::Primitive(Primitive::Bool)) => {
            debug_assert!(n < 2);
            ConstValue::Bool(n != 0)
        }
        Val::Int(n) => {
            let TypeInfo::Primitive(p) = ty else {
                unreachable!()
            };
            let int_ty = p.as_int().unwrap();
            ConstValue::Int(n, Some(int_ty))
        }
        Val::F32(n) => ConstValue::Float(n as f64, Some(FloatType::F32)),
        Val::F64(n) => ConstValue::Float(n, Some(FloatType::F64)),
        Val::Ptr(_) => todo!("handle constants with compile-time pointers"),
        Val::Array(_) => todo!("constant arrays"),
        Val::Tuple(elems) => match ty {
            TypeInfo::Tuple(elem_types) => {
                assert_eq!(elems.len(), elem_types.count as usize);
                let elems = IntoIterator::into_iter(elems)
                    .zip(elem_types.iter())
                    .map(|(elem, ty)| to_const_val(elem, types[ty], types))
                    .collect();
                ConstValue::Tuple(elems)
            }
            TypeInfo::TypeDef(_, _) => todo!("const value from typed Val"),
            _ => ConstValue::Undefined,
        },
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
                return Err(format!("Can't evaluate extern function {name} at compile-time").into())
            }
        })
    }
}
