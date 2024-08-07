pub mod const_value;
mod entry_point;
pub mod types;

pub use entry_point::entry_point;

use ::types::{Primitive, Type};
use id::ModuleId;
use ir::builder::{BinOp, Terminator};
use ir::{builder::IrBuilder, IrType, Ref};
use ir::{BlockIndex, RefVal};

use crate::compiler::{builtins, FunctionToGenerate};
use crate::eval::ConstValue;
use crate::hir::{CastType, LValue, LValueId, Node, Pattern, PatternId};
use crate::irgen::types::get_primitive;
use crate::parser::ast;
use crate::types::{LocalTypeId, LocalTypeIds, OrdinalType};
use crate::Compiler;
use crate::{
    compiler::CheckedFunction,
    hir::{NodeId, HIR},
    types::{TypeInfo, TypeTable},
};

pub fn lower_function(
    compiler: &mut Compiler,
    to_generate: &mut Vec<FunctionToGenerate>,
    name: String,
    checked: &CheckedFunction,
    generics: &[Type],
) -> ir::Function {
    let mut types = ir::IrTypes::new();
    // TODO: figure out what to do when params/return_type are Invalid or never types. We can no
    // longer generate a valid signature
    let param_types = types::get_multiple_infos(
        compiler,
        &checked.types,
        &mut types,
        checked.params,
        types::Generics::function_instance(generics),
    )
    .unwrap_or_else(|| types.add_multiple((0..checked.params.count).map(|_| IrType::Unit)));

    let return_type = checked.types[checked.return_type];
    let return_type = types::get_from_info(
        compiler,
        &checked.types,
        &mut types,
        return_type,
        types::Generics::function_instance(generics),
    )
    .unwrap_or(IrType::Unit);

    let ir = checked.body.as_ref().map(|hir| {
        let (mut builder, params) = ir::builder::IrBuilder::new(&mut types, param_types);
        let mut vars = vec![(Ref::UNDEF, ir::TypeRef::NONE); hir.vars.len()];

        for (i, (r, ty)) in params.iter().zip(param_types.iter()).enumerate() {
            vars[i] = (builder.build_decl(ty), ty);
            builder.build_store(vars[i].0, Ref::index(r));
        }

        lower_hir(
            builder,
            hir,
            &checked.types,
            compiler,
            to_generate,
            generics,
            &mut vars,
        )
    });
    ir::Function {
        name,
        types,
        params: param_types,
        return_type,
        varargs: checked.varargs,
        ir,
    }
}

type Result<T> = std::result::Result<T, NoReturn>;
struct NoReturn;

macro_rules! crash_point {
    ($ctx: expr) => {{
        build_crash_point($ctx);
        return Err(NoReturn);
    }};
}

pub fn lower_hir(
    builder: ir::builder::IrBuilder,
    hir: &HIR,
    hir_types: &TypeTable,
    compiler: &mut Compiler,
    to_generate: &mut Vec<FunctionToGenerate>,
    generics: &[Type],
    vars: &mut [(Ref, ir::TypeRef)],
) -> ir::FunctionIr {
    let mut ctx = Ctx {
        compiler,
        to_generate,
        hir,
        types: hir_types,
        generics,
        generic_types: generics,
        builder,
        vars,
    };
    let val = lower(&mut ctx, hir.root_id());
    if let Ok(val) = val {
        ctx.builder.terminate_block(Terminator::Ret(val));
    }
    ctx.builder.finish()
}

struct Ctx<'a> {
    compiler: &'a mut Compiler,
    to_generate: &'a mut Vec<FunctionToGenerate>,
    hir: &'a HIR,
    types: &'a TypeTable,
    generics: &'a [Type],
    generic_types: &'a [Type],
    builder: IrBuilder<'a>,
    vars: &'a mut [(Ref, ir::TypeRef)],
}
impl<'a> Ctx<'a> {
    fn get_ir_id(
        &mut self,
        module: ModuleId,
        id: ast::FunctionId,
        generics: Vec<Type>,
    ) -> Option<ir::FunctionId> {
        // check that none of the types is invalid, we never wan't to generate an instance for an
        // invalid type. The caller should build a crash point in that case.
        for ty in &generics {
            if matches!(ty, Type::Invalid) {
                return None;
            }
        }
        let checked = self.compiler.get_hir(module, id);
        debug_assert_eq!(
            checked.generic_count as usize,
            generics.len(),
            "trying to instantiate a function with an invalid generic count"
        );
        let instances = &mut self.compiler.modules[module.idx()]
            .ast
            .as_mut()
            .unwrap()
            .instances;

        let potential_id = ir::FunctionId(self.compiler.ir_module.funcs.len() as _);

        Some(match instances.get_or_insert(id, &generics, potential_id) {
            Some(id) => id,
            None => {
                // FIXME: just adding a dummy function right now, stupid solution and might cause issues
                self.compiler.ir_module.funcs.push(ir::Function {
                    name: String::new(),
                    types: ir::IrTypes::new(),
                    params: ir::TypeRefs::EMPTY,
                    return_type: ir::IrType::Unit,
                    varargs: false,
                    ir: None,
                });
                self.to_generate.push(FunctionToGenerate {
                    ir_id: potential_id,
                    module,
                    ast_function_id: id,
                    generics,
                });
                potential_id
            }
        })
    }

    fn get_ir_global(&mut self, module: ModuleId, id: ast::GlobalId) -> Option<ir::GlobalId> {
        let parsed = self.compiler.get_parsed_module(module);
        if let Some(global) = parsed.instances.globals[id.idx()] {
            Some(global)
        } else {
            let parsed = self.compiler.get_parsed_module(module);
            let name = String::from(&*parsed.ast[id].name);
            let (ty, value) = self.compiler.get_checked_global(module, id);
            let ty = ty.clone();
            let value = const_value::translate(value);
            let mut types = ir::IrTypes::new();
            let ty = types::get(&mut self.compiler, &mut types, &ty, types::Generics::Empty)?;
            let global_id = ir::GlobalId(self.compiler.ir_module.globals.len() as _);
            self.compiler.ir_module.globals.push(ir::Global {
                name,
                types,
                ty,
                value,
            });
            self.compiler.get_parsed_module(module).instances.globals[id.idx()] = Some(global_id);
            Some(global_id)
        }
    }

    fn get_type(&mut self, ty: TypeInfo) -> Result<IrType> {
        types::get_from_info(
            self.compiler,
            self.types,
            self.builder.types,
            ty,
            types::Generics::function_instance(self.generics),
        )
        .ok_or_else(|| {
            build_crash_point(self);
            NoReturn
        })
    }

    fn get_multiple_types(&mut self, ids: LocalTypeIds) -> Result<ir::TypeRefs> {
        types::get_multiple_infos(
            self.compiler,
            self.types,
            self.builder.types,
            ids,
            types::Generics::function_instance(self.generics),
        )
        .ok_or_else(|| {
            build_crash_point(self);
            NoReturn
        })
    }
}

fn lower(ctx: &mut Ctx, node: NodeId) -> Result<Ref> {
    Ok(match lower_expr(ctx, node)? {
        ValueOrPlace::Value(r) => r,
        ValueOrPlace::Place { ptr, value_ty } => ctx.builder.build_load(ptr, value_ty),
    })
}

enum ValueOrPlace {
    Value(Ref),
    Place { ptr: Ref, value_ty: ir::TypeRef },
}

fn lower_expr(ctx: &mut Ctx, node: NodeId) -> Result<ValueOrPlace> {
    let value = match &ctx.hir[node] {
        Node::Invalid => crash_point!(ctx),
        Node::Block(items) => {
            for item in items.iter() {
                lower(ctx, item)?;
            }
            Ref::UNIT
        }
        Node::Unit => Ref::UNIT,
        &Node::IntLiteral { val, ty } => {
            let TypeInfo::Primitive(p) = ctx.types[ty] else {
                crash_point!(ctx)
            };
            debug_assert!(p.is_int());
            let ty = types::get_primitive(p);
            if let Ok(small) = val.try_into() {
                ctx.builder.build_int(small, ty)
            } else {
                ctx.builder.build_large_int(val, ty)
            }
        }
        &Node::FloatLiteral { val, ty } => {
            let TypeInfo::Primitive(p) = ctx.types[ty] else {
                crash_point!(ctx)
            };
            debug_assert!(p.is_float());
            let ty = types::get_primitive(p);
            ctx.builder.build_float(val, ty)
        }
        Node::BoolLiteral(true) => Ref::val(RefVal::True),
        Node::BoolLiteral(false) => Ref::val(RefVal::False),
        &Node::ArrayLiteral { elems, array_ty } => {
            let TypeInfo::Array { element, count: _ } = ctx.types[array_ty] else {
                panic!("non-array literal type");
            };
            let elem_ir_ty = ctx.get_type(ctx.types[element])?;
            let elem_ir_ty = ctx.builder.types.add(elem_ir_ty);
            let array_ir_ty = ctx
                .builder
                .types
                .add(IrType::Array(elem_ir_ty, elems.count));
            let array_var = ctx.builder.build_decl(array_ir_ty);
            for (elem, i) in elems.iter().zip(0..) {
                let val = lower(ctx, elem)?;
                let index = ctx.builder.build_int(i, IrType::U64);
                let member_ptr = ctx.builder.build_array_index(array_var, index, elem_ir_ty);
                ctx.builder.build_store(member_ptr, val);
            }
            return Ok(ValueOrPlace::Place {
                ptr: array_var,
                value_ty: array_ir_ty,
            });
        }
        &Node::TupleLiteral { elems, elem_types } => {
            debug_assert_eq!(elems.count, elem_types.count);
            let elem_types = ctx.get_multiple_types(elem_types)?;
            let tuple_ty = ctx.builder.types.add(IrType::Tuple(elem_types));
            let var = ctx.builder.build_decl(tuple_ty);
            for (elem, i) in elems.iter().zip(0..) {
                let elem_ptr = ctx.builder.build_member_ptr(var, i, elem_types);
                let val = lower(ctx, elem)?;
                ctx.builder.build_store(elem_ptr, val);
            }
            // maybe do this differently, could do it like llvm: insertvalue
            ctx.builder.build_load(var, tuple_ty)
        }
        &Node::EnumLiteral {
            elems,
            elem_types,
            enum_ty,
        } => {
            debug_assert_eq!(elems.count, elem_types.count);
            let enum_ty = ctx.get_type(ctx.types[enum_ty])?;
            let elem_types = ctx.get_multiple_types(elem_types)?;
            let var = ctx.builder.build_decl(enum_ty);
            for (elem, i) in elems.iter().zip(0..) {
                let elem_ptr = ctx.builder.build_member_ptr(var, i, elem_types);
                let val = lower(ctx, elem)?;
                ctx.builder.build_store(elem_ptr, val);
            }
            // maybe do this differently, could do it like llvm: insertvalue
            ctx.builder.build_load(var, enum_ty)
        }
        Node::StringLiteral(str) => {
            let (ptr, value_ty) = lower_string_literal(&mut ctx.builder, str);
            return Ok(ValueOrPlace::Place { ptr, value_ty });
        }
        &Node::InferredEnumOrdinal(variant) => {
            let variant = &ctx.types[variant];
            let ty = ctx.types[variant.args.iter().next().unwrap()];
            match ty {
                TypeInfo::Primitive(Primitive::Unit) => Ref::UNIT,
                _ => {
                    let ty = ctx.get_type(ty)?;
                    ctx.builder.build_int(variant.ordinal as u64, ty)
                }
            }
        }

        Node::Declare { pattern: _ } => todo!("lower declarations without values"),
        &Node::DeclareWithVal { pattern, val } => {
            let val = lower(ctx, val)?;
            lower_pattern(ctx, pattern, val, BlockIndex::MISSING)?;
            Ref::UNIT
        }
        Node::Variable(id) => {
            return Ok(ValueOrPlace::Place {
                ptr: ctx.vars[id.idx()].0,
                value_ty: ctx.vars[id.idx()].1,
            });
        }
        &Node::Global(module, id, ty) => {
            let Some(id) = ctx.get_ir_global(module, id) else {
                crash_point!(ctx)
            };
            let global = ctx.builder.build_global(id, IrType::Ptr);
            let ty = ctx.get_type(ctx.types[ty])?;
            let ty = ctx.builder.types.add(ty);
            return Ok(ValueOrPlace::Place {
                ptr: global,
                value_ty: ty,
            });
        }
        &Node::Assign(lval, val, assign_ty, ty) => {
            let lval = lower_lval(ctx, lval)?;
            let val = lower(ctx, val)?;
            // this will be none when the LValue is Ignore, don't perform a store in
            // that case
            use crate::parser::token::AssignType;
            let Some(lval) = lval else {
                // TODO: is ignoring the value fine for arithmetic assignment operations like
                // plus-equals?
                return Ok(ValueOrPlace::Value(Ref::UNIT));
            };
            use crate::hir::Arithmetic;
            let arithmetic = match assign_ty {
                AssignType::Assign => {
                    ctx.builder.build_store(lval, val);
                    return Ok(ValueOrPlace::Value(Ref::UNIT));
                }
                AssignType::AddAssign => Arithmetic::Add,
                AssignType::SubAssign => Arithmetic::Sub,
                AssignType::MulAssign => Arithmetic::Mul,
                AssignType::DivAssign => Arithmetic::Div,
                AssignType::ModAssign => Arithmetic::Mod,
            };

            let ty = ctx.types[ty];
            let ir_ty = ctx.get_type(ty)?;
            let loaded = ctx.builder.build_load(lval, ir_ty);
            let result = build_arithmetic(ctx, loaded, val, arithmetic, ty);
            ctx.builder.build_store(lval, result);
            Ref::UNIT
        }

        &Node::Const { id, ty } => {
            let const_val = &ctx.compiler.const_values[id.idx()];
            match const_val {
                ConstValue::Unit => Ref::UNIT,
                ConstValue::Bool(true) => Ref::val(RefVal::True),
                ConstValue::Bool(false) => Ref::val(RefVal::False),
                &ConstValue::Int(num, _) => {
                    let ty = ctx.types[ty];
                    match ty {
                        TypeInfo::Primitive(p) => {
                            debug_assert!(p.is_int());
                            ctx.builder.build_int(num, get_primitive(p))
                        }
                        TypeInfo::Invalid => crash_point!(ctx),
                        _ => unreachable!(),
                    }
                }
                &ConstValue::Float(num, _) => {
                    let ty = ctx.types[ty];
                    match ty {
                        TypeInfo::Primitive(p) => {
                            debug_assert!(p.is_float());
                            ctx.builder.build_float(num, get_primitive(p))
                        }
                        TypeInfo::Invalid => crash_point!(ctx),
                        _ => unreachable!(),
                    }
                }
                ConstValue::Undefined => crash_point!(ctx),
            }
        }

        &Node::Negate(value, ty) => {
            let value = lower(ctx, value)?;
            let ty = ctx.get_type(ctx.types[ty])?;
            ctx.builder.build_neg(value, ty)
        }
        &Node::Not(value) => {
            let value = lower(ctx, value)?;
            ctx.builder.build_not(value, IrType::U1)
        }
        &Node::AddressOf { inner, value_ty } => {
            let value = lower_expr(ctx, inner)?;
            match value {
                ValueOrPlace::Value(v) => {
                    let ty = ctx.get_type(ctx.types[value_ty])?;
                    let ptr = ctx.builder.build_decl(ty);
                    ctx.builder.build_store(ptr, v);
                    ptr
                }
                ValueOrPlace::Place { ptr, value_ty: _ } => ptr,
            }
        }
        &Node::Deref { value, deref_ty } => {
            let value = lower(ctx, value)?;
            let ty = ctx.get_type(ctx.types[deref_ty])?;
            let value_ty = ctx.builder.types.add(ty);
            //let ptr = ctx.builder.build_load(value, ty);
            return Ok(ValueOrPlace::Place {
                ptr: value,
                value_ty,
            });
        }

        &Node::Cast(id) => {
            let cast = &ctx.hir[id];
            let val = lower(ctx, cast.val)?;
            // TODO: separate into multiple more specific cast instructions in ir
            match &cast.cast_ty {
                CastType::Invalid => crash_point!(ctx),
                CastType::Noop => val,
                &CastType::Int { from: _, to } => {
                    let to_ty = types::get_primitive(to.into());
                    ctx.builder.build_cast_int(val, to_ty)
                }
                &CastType::Float { from: _, to } => {
                    let to_ty = types::get_primitive(to.into());
                    ctx.builder.build_cast_float(val, to_ty)
                }
                &CastType::FloatToInt { from: _, to } => {
                    let to_ty = types::get_primitive(to.into());
                    ctx.builder.build_cast_float_to_int(val, to_ty)
                }
                &CastType::IntToFloat { from: _, to } => {
                    let to_ty = types::get_primitive(to.into());
                    ctx.builder.build_cast_int_to_float(val, to_ty)
                }
                CastType::IntToPtr { from: _ } => ctx.builder.build_int_to_ptr(val),
                &CastType::PtrToInt { to } => ctx
                    .builder
                    .build_ptr_to_int(val, types::get_primitive(to.into())),
                CastType::EnumToInt { .. } => todo!("cast enums to integers, might be removed"),
            }
        }
        &Node::Comparison {
            l,
            r,
            cmp,
            compared,
        } => {
            let l = lower(ctx, l)?;
            let r = lower(ctx, r)?;
            use crate::hir::Comparison;
            let mut is_equality = false;
            let op = match cmp {
                Comparison::Eq => {
                    is_equality = true;
                    BinOp::Eq
                }
                Comparison::NE => {
                    is_equality = true;
                    BinOp::NE
                }
                Comparison::LT => BinOp::LT,
                Comparison::GT => BinOp::GT,
                Comparison::LE => BinOp::LE,
                Comparison::GE => BinOp::GE,
                Comparison::And => BinOp::And,
                Comparison::Or => BinOp::Or,
            };
            if is_equality {
                match ctx.types[compared] {
                    TypeInfo::Invalid => crash_point!(ctx),
                    TypeInfo::TypeDef(id, generics) => {
                        let str_ty = builtins::get_str(ctx.compiler);
                        if id == str_ty {
                            debug_assert!(generics.count == 0);
                            let string_eq = builtins::get_str_eq(ctx.compiler);
                            let Some(string_eq) =
                                ctx.get_ir_id(string_eq.0, string_eq.1, Vec::new())
                            else {
                                crash_point!(ctx);
                            };
                            let eq = ctx.builder.build_call(string_eq, [l, r], IrType::U1);
                            return Ok(ValueOrPlace::Value(if cmp == Comparison::NE {
                                ctx.builder.build_not(eq, IrType::U1)
                            } else {
                                eq
                            }));
                        } else {
                            panic!("invalid type for comparison, will change with traits");
                        }
                    }
                    // let all other types fall through, they might be invalid but that will be
                    // dealt with by traits in the future
                    _ => {}
                }
            }
            ctx.builder.build_bin_op(op, l, r, IrType::U1)
        }
        &Node::Arithmetic(l, r, op, ty) => {
            let l = lower(ctx, l)?;
            let r = lower(ctx, r)?;
            build_arithmetic(ctx, l, r, op, ctx.types[ty])
        }

        &Node::Element {
            tuple_value,
            index,
            elem_types,
        } => {
            let value = lower_expr(ctx, tuple_value)?;
            let value = match value {
                ValueOrPlace::Value(val) => {
                    let elem_ty = ctx.get_type(ctx.types[elem_types.nth(index).unwrap()])?;
                    let value = ctx.builder.build_member_value(val, index, elem_ty);
                    ValueOrPlace::Value(value)
                }
                ValueOrPlace::Place { ptr, value_ty: _ } => {
                    let elem_types = ctx.get_multiple_types(elem_types)?;
                    let member_ptr = ctx.builder.build_member_ptr(ptr, index, elem_types);
                    ValueOrPlace::Place {
                        ptr: member_ptr,
                        value_ty: elem_types.nth(index),
                    }
                }
            };
            return Ok(value);
        }
        &Node::ArrayIndex {
            array,
            index,
            elem_ty,
        } => {
            let array = match lower_expr(ctx, array)? {
                ValueOrPlace::Value(_) => todo!("array indexing without place"),
                ValueOrPlace::Place { ptr, .. } => ptr,
            };
            let index = lower(ctx, index)?;
            let elem_ir_ty = ctx.get_type(ctx.types[elem_ty])?;
            let elem_ir_ty = ctx.builder.types.add(elem_ir_ty);
            return Ok(ValueOrPlace::Place {
                ptr: ctx.builder.build_array_index(array, index, elem_ir_ty),
                value_ty: elem_ir_ty,
            });
        }

        &Node::Return(val) => {
            let val = lower(ctx, val)?;
            ctx.builder.terminate_block(Terminator::Ret(val));
            return Err(NoReturn);
        }
        &Node::IfElse {
            cond,
            then,
            else_,
            resulting_ty,
        } => {
            let cond = lower(ctx, cond)?;
            let then_block = ctx.builder.create_block();
            let else_block = ctx.builder.create_block();
            ctx.builder.terminate_block(Terminator::Branch {
                cond,
                on_true: (then_block, &[]),
                on_false: (else_block, &[]),
            });
            ctx.builder.begin_block(then_block);
            lower_if_else_branches(ctx, then, else_, else_block, resulting_ty)?
        }
        &Node::IfPatElse {
            pat,
            val,
            then,
            else_,
            resulting_ty,
        } => {
            let val = lower(ctx, val)?;
            let else_block = ctx.builder.create_block();
            lower_pattern(ctx, pat, val, else_block)?;
            lower_if_else_branches(ctx, then, else_, else_block, resulting_ty)?
        }
        &Node::Match {
            value,
            branch_index,
            pattern_index,
            branch_count,
            resulting_ty,
        } => {
            let value = lower(ctx, value)?;
            let mut after_block = None;
            let mut next_block;
            let mut result_value = None;
            if branch_count == 0 {
                // matching on an empty enum or something so we need to terminate the block
                ctx.builder.terminate_block(Terminator::Ret(Ref::UNDEF));
                return Err(NoReturn);
            }
            for i in 0..branch_count {
                let is_last = i + 1 == branch_count;
                let pattern = PatternId(pattern_index + i);
                let branch = NodeId(branch_index + i);
                next_block = if is_last {
                    BlockIndex::MISSING
                } else {
                    ctx.builder.create_block()
                };
                let pattern_noreturn = lower_pattern(ctx, pattern, value, next_block).is_err();
                if pattern_noreturn {
                    // if any other than the first pattern is noreturn, the match itself might
                    // still return because a pattern before might have matched
                    if i == 0 {
                        return Err(NoReturn);
                    }
                    break;
                }
                let val = lower(ctx, branch);
                if let Ok(val) = val {
                    let after = *after_block.get_or_insert_with(|| ctx.builder.create_block());
                    ctx.builder.terminate_block(Terminator::Goto(after, &[val]));
                }
                if is_last {
                    // after could still be none if all branches are noreturn, we don't have to
                    // create an after block at all in this case
                    if let Some(after) = after_block {
                        let ty = ctx.get_type(ctx.types[resulting_ty])?;
                        let types = ctx.builder.types.add_multiple([ty]);
                        let args = ctx.builder.begin_block_with_args(after, types);
                        result_value = Some(args.nth(0));
                    }
                } else {
                    ctx.builder.begin_block(next_block);
                }
            }
            result_value.ok_or(NoReturn)?
        }
        &Node::While { cond, body } => {
            let cond_block = ctx.builder.create_block();
            ctx.builder
                .terminate_block(Terminator::Goto(cond_block, &[]));
            ctx.builder.begin_block(cond_block);
            let cond = lower(ctx, cond)?;
            let body_block = ctx.builder.create_block();
            let after_block = ctx.builder.create_block();
            ctx.builder.terminate_block(Terminator::Branch {
                cond,
                on_true: (body_block, &[]),
                on_false: (after_block, &[]),
            });
            ctx.builder.begin_block(body_block);
            if lower(ctx, body).is_ok() {
                ctx.builder
                    .terminate_block(Terminator::Goto(cond_block, &[]));
            }
            ctx.builder.begin_block(after_block);
            Ref::UNIT
        }
        &Node::WhilePat { pat, val, body } => {
            let loop_start = ctx.builder.create_block();
            let after = ctx.builder.create_block();
            ctx.builder
                .terminate_block(Terminator::Goto(loop_start, &[]));
            ctx.builder.begin_block(loop_start);
            let val = lower(ctx, val)?;
            lower_pattern(ctx, pat, val, after)?;
            if lower(ctx, body).is_ok() {
                ctx.builder
                    .terminate_block(Terminator::Goto(loop_start, &[]));
            }
            ctx.builder.begin_block(after);
            Ref::UNIT
        }
        &Node::Call {
            function,
            generics: call_generics,
            args,
            return_ty,
            noreturn,
        } => {
            let call_generics = call_generics
                .iter()
                .map(|generic| ctx.types.to_resolved(ctx.types[generic], ctx.generic_types))
                .collect();
            let Some(func) = ctx.get_ir_id(function.0, function.1, call_generics) else {
                crash_point!(ctx)
            };
            let mut arg_refs = Vec::with_capacity(args.iter().count());
            for arg in args.iter() {
                let arg = lower(ctx, arg)?;
                arg_refs.push(arg);
            }
            let return_ty = ctx.get_type(ctx.types[return_ty])?;
            let res = ctx.builder.build_call(func, arg_refs, return_ty);
            if noreturn {
                ctx.builder.terminate_block(Terminator::Ret(Ref::UNDEF));
                return Err(NoReturn);
            }
            res
        }
        &Node::TraitCall {
            trait_id,
            trait_generics,
            method_index,
            self_ty,
            args,
            return_ty,
            noreturn,
        } => {
            // PERF: could implement get_checked_trait_impl_from_final_types again to avoid
            // the to_resolved_calls and heap allocation for generics.
            // Only do this when tests exist to ensure TraitCall instantiation works
            let self_ty = ctx.types.to_resolved(ctx.types[self_ty], ctx.generics);
            let trait_generics: Box<[Type]> = trait_generics
                .iter()
                .map(|ty| ctx.types.to_resolved(ctx.types[ty], ctx.generics))
                .collect();
            let Some((impl_, impl_generics)) =
                ctx.compiler
                    .get_checked_trait_impl(trait_id, &self_ty, &trait_generics)
            else {
                crash_point!(ctx)
            };
            let function = (impl_.impl_module, impl_.functions[method_index as usize]);
            // TODO: handle impl/method generics
            let Some(func) = ctx.get_ir_id(function.0, function.1, impl_generics) else {
                crash_point!(ctx)
            };
            let return_ty = ctx.get_type(ctx.types[return_ty])?;
            let mut arg_refs = Vec::with_capacity(args.iter().count());
            for arg in args.iter() {
                let arg = lower(ctx, arg)?;
                arg_refs.push(arg);
            }
            let res = ctx.builder.build_call(func, arg_refs, return_ty);
            if noreturn {
                ctx.builder.terminate_block(Terminator::Ret(Ref::UNDEF));
                return Err(NoReturn);
            }
            res
        }
        &Node::TypeProperty(ty, property) => {
            let layout = ir::type_layout(ctx.get_type(ctx.types[ty])?, &ctx.builder.types);
            use crate::hir::TypeProperty;
            let value = match property {
                TypeProperty::Size => layout.size,
                TypeProperty::Align => layout.align.get(),
                TypeProperty::Stride => layout.stride(),
            };
            ctx.builder.build_int(value, IrType::U64)
        }
    };
    Ok(ValueOrPlace::Value(value))
}

fn lower_lval(ctx: &mut Ctx, lval: LValueId) -> Result<Option<Ref>> {
    Ok(Some(match ctx.hir[lval] {
        LValue::Invalid => crash_point!(ctx),
        LValue::Variable(id) => ctx.vars[id.idx()].0,
        LValue::Ignore => return Ok(None),
        LValue::Global(module, id) => {
            let Some(id) = ctx.get_ir_global(module, id) else {
                crash_point!(ctx)
            };
            ctx.builder.build_global(id, IrType::Ptr)
        }
        LValue::Deref(pointer) => lower(ctx, pointer)?,
        LValue::Member {
            ptr,
            index,
            elem_types,
        } => {
            let ptr = lower(ctx, ptr)?;
            let types = ctx.get_multiple_types(elem_types)?;
            ctx.builder.build_member_ptr(ptr, index, types)
        }
        LValue::ArrayIndex {
            array_ptr,
            index,
            element_type,
        } => {
            let ptr = lower(ctx, array_ptr)?;
            let idx = lower(ctx, index)?;
            let ty = ctx.get_type(ctx.types[element_type])?;
            let ty = ctx.builder.types.add(ty);
            ctx.builder.build_array_index(ptr, idx, ty)
        }
    }))
}

/// Lower a pattern, jumping to the on_mismatch block if the pattern doesn't match.
/// When on_mismatch is set to BlockIndex::MISSING, all patterns are assumed to always match
fn lower_pattern(
    ctx: &mut Ctx,
    pattern: PatternId,
    value: Ref,
    on_mismatch: BlockIndex,
) -> Result<()> {
    let branch_bool = |ctx: &mut Ctx, cond: Ref| {
        if on_mismatch == BlockIndex::MISSING {
            return;
        }
        let on_match = ctx.builder.create_block();
        ctx.builder.terminate_block(Terminator::Branch {
            cond,
            on_true: (on_match, &[]),
            on_false: (on_mismatch, &[]),
        });
        ctx.builder.begin_block(on_match);
    };
    match &ctx.hir[pattern] {
        Pattern::Invalid => crash_point!(ctx),
        Pattern::Variable(id) => {
            let var_ty = ctx.types[ctx.hir.vars[id.idx()]];
            let ty = ctx.get_type(var_ty)?;
            let ty = ctx.builder.types.add(ty);
            let var = ctx.builder.build_decl(ty);
            ctx.vars[id.idx()] = (var, ty);
            ctx.builder.build_store(var, value);
        }
        Pattern::Ignore => {}
        Pattern::Tuple(_) => todo!(),
        &Pattern::Int(sign, val, ty) => {
            let TypeInfo::Primitive(p) = ctx.types[ty] else {
                panic!("integer type expected")
            };
            let ty = types::get_primitive(p);
            debug_assert!(p.is_int());
            let pattern_value = int_pat(&mut ctx.builder, sign, val, ty);
            let cond = ctx
                .builder
                .build_bin_op(BinOp::Eq, value, pattern_value, ty);
            branch_bool(ctx, cond);
        }
        &Pattern::Bool(b) => {
            if on_mismatch == BlockIndex::MISSING {
                return Ok(());
            }
            let on_match = ctx.builder.create_block();
            let (on_true, on_false) = if b {
                (on_match, on_mismatch)
            } else {
                (on_mismatch, on_match)
            };
            ctx.builder.terminate_block(Terminator::Branch {
                cond: value,
                on_true: (on_true, &[]),
                on_false: (on_false, &[]),
            });
        }
        Pattern::String(s) => {
            let str_eq = builtins::get_str_eq(ctx.compiler);
            // can unwrap here because we don't pass invalid generics
            let str_eq = ctx.get_ir_id(str_eq.0, str_eq.1, Vec::new()).unwrap();
            let (expected, str_ty) = lower_string_literal(&mut ctx.builder, s);
            let expected = ctx.builder.build_load(expected, str_ty);
            let matches = ctx
                .builder
                .build_call(str_eq, [value, expected], IrType::U1);
            branch_bool(ctx, matches);
        }
        &Pattern::Range {
            min_max: (min, max),
            ty,
            min_max_signs: (min_sign, max_sign),
            inclusive,
        } => {
            let TypeInfo::Primitive(p) = ctx.types[ty] else {
                panic!("integer type expected")
            };
            let ty = types::get_primitive(p);
            let min = int_pat(&mut ctx.builder, min_sign, min, ty);
            let max = int_pat(&mut ctx.builder, max_sign, max, ty);
            let left = ctx
                .builder
                .build_bin_op(ir::builder::BinOp::GE, value, min, ty);
            branch_bool(ctx, left);
            let right_op = if inclusive {
                ir::builder::BinOp::LE
            } else {
                ir::builder::BinOp::LT
            };
            let right = ctx.builder.build_bin_op(right_op, value, max, ty);
            branch_bool(ctx, right);
        }
        &Pattern::EnumVariant {
            ordinal,
            types,
            args,
        } => {
            let ir_types = ctx.get_multiple_types(LocalTypeIds {
                idx: types,
                count: args.count + 1,
            })?;
            let tuple_ty = IrType::Tuple(ir_types);
            // HACK: right now the value is always stored when checking with an enum variant. In
            // Rust, all patterns get passed a pointer to check their value, which would probably
            // be better. Pointer is needed right now to compare ordinal and variants
            // (implicitly casting the types on load)
            let var = ctx.builder.build_decl(tuple_ty);
            ctx.builder.build_store(var, value);
            let ordinal_ty = LocalTypeId(types);
            let arg_types = LocalTypeIds {
                idx: types + 1,
                count: args.count,
            };
            match ctx.types[ordinal_ty] {
                TypeInfo::Invalid => crash_point!(ctx),
                TypeInfo::Primitive(Primitive::Unit) => {}
                TypeInfo::Primitive(p) => {
                    let int_ty = p.as_int().unwrap();
                    let ordinal_ty = get_primitive(int_ty.into());
                    let actual_ordinal = ctx.builder.build_load(var, ordinal_ty);
                    let ordinal_value = match ordinal {
                        OrdinalType::Known(val) => val,
                        OrdinalType::Inferred(variant) => ctx.types[variant].ordinal,
                    };
                    let expected = ctx.builder.build_int(ordinal_value as u64, ordinal_ty);
                    let ordinal_matches =
                        ctx.builder
                            .build_bin_op(BinOp::Eq, actual_ordinal, expected, IrType::U1);
                    branch_bool(ctx, ordinal_matches);
                }
                other => unreachable!("invalid ordinal type {other:?}"),
            }
            if args.count == 0 {
                return Ok(());
            }
            for ((arg, i), ty) in args.iter().zip(1..).zip(arg_types.iter()) {
                let ty = ctx.get_type(ctx.types[ty])?;
                let arg_ptr = ctx.builder.build_member_ptr(var, i, ir_types);
                let arg_value = ctx.builder.build_load(arg_ptr, ty);
                lower_pattern(ctx, arg, arg_value, on_mismatch)?;
            }
        }
    }
    Ok(())
}

fn int_pat(builder: &mut IrBuilder, sign: bool, val: u128, ty: IrType) -> Ref {
    let mut pattern_value = if let Ok(small) = val.try_into() {
        builder.build_int(small, ty)
    } else {
        builder.build_large_int(val, ty)
    };
    if sign {
        pattern_value = builder.build_neg(pattern_value, ty);
    }
    pattern_value
}

fn lower_string_literal(builder: &mut IrBuilder, s: &str) -> (Ref, ir::TypeRef) {
    // TODO: cache string ir type to prevent generating it multiple times
    let elems = builder.types.add_multiple([IrType::Ptr, IrType::U64]);
    let str_ty = builder.types.add(IrType::Tuple(elems));
    let str_var = builder.build_decl(str_ty);
    let str_ptr = builder.build_string(s.as_bytes(), true);
    builder.build_store(str_var, str_ptr);
    let str_len_var = builder.build_member_ptr(str_var, 1, elems);
    let str_len = builder.build_int(s.len() as u64, IrType::U64);
    builder.build_store(str_len_var, str_len);
    (str_var, str_ty)
}

fn build_crash_point(ctx: &mut Ctx) {
    let msg = "program reached a compile error at runtime";
    let (ptr, str_ty) = lower_string_literal(&mut ctx.builder, msg);
    let msg = ctx.builder.build_load(ptr, str_ty);
    let panic_function = ctx.compiler.get_builtin_panic();
    ctx.builder.build_call(panic_function, [msg], IrType::Unit);
    ctx.builder.terminate_block(Terminator::Ret(Ref::UNDEF));
}

fn build_arithmetic(
    ctx: &mut Ctx,
    l: Ref,
    r: Ref,
    op: crate::hir::Arithmetic,
    ty: TypeInfo,
) -> Ref {
    use crate::hir::Arithmetic;
    let op = match op {
        Arithmetic::Add => BinOp::Add,
        Arithmetic::Sub => BinOp::Sub,
        Arithmetic::Mul => BinOp::Mul,
        Arithmetic::Div => BinOp::Div,
        Arithmetic::Mod => BinOp::Mod,
    };
    let TypeInfo::Primitive(p) = ty else {
        panic!(
            "Invalid type {:?} for arithmetic op. Will be handled properly with traits",
            ty
        );
    };
    assert!(
        p.is_int() || p.is_float(),
        "Invalid primitive type {p} for arithmetic op. Will be handled properly with traits"
    );
    ctx.builder.build_bin_op(op, l, r, types::get_primitive(p))
}

fn lower_if_else_branches(
    ctx: &mut Ctx,
    then: NodeId,
    else_: NodeId,
    else_block: ir::BlockIndex,
    resulting_ty: LocalTypeId,
) -> Result<Ref> {
    // after_block is a closure that creates the block lazily and returns it
    let else_is_trival = matches!(ctx.hir[else_], Node::Unit);
    let mut after_block = {
        let mut after_block = else_is_trival.then_some(else_block);
        move |ctx: &mut Ctx| {
            after_block.unwrap_or_else(|| {
                let block = ctx.builder.create_block();
                after_block = Some(block);
                block
            })
        }
    };
    let mut check_branch = |ctx: &mut Ctx, value: NodeId| -> Option<ir::BlockIndex> {
        lower(ctx, value).ok().map(|val| {
            let block = ctx.builder.current_block();
            let after_block = after_block(ctx);
            ctx.builder
                .terminate_block(Terminator::Goto(after_block, &[val]));
            block
        })
    };
    let then_val = check_branch(ctx, then);
    ctx.builder.begin_block(else_block);
    if else_is_trival {
        return Ok(Ref::UNIT);
    }
    let else_val = check_branch(ctx, else_);
    match (then_val, else_val) {
        (None, None) => Err(NoReturn),
        _ => {
            let after_block = after_block(ctx);
            let ty = ctx.get_type(ctx.types[resulting_ty])?;
            let types = ctx.builder.types.add_multiple([ty]);
            let args = ctx.builder.begin_block_with_args(after_block, types);
            Ok(args.nth(0))
        }
    }
}
