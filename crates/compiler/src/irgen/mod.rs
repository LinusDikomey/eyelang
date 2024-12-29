pub mod const_value;
mod entry_point;
mod intrinsics;
pub mod types;

pub use entry_point::entry_point;

use ::types::{Primitive, Type};
use id::ModuleId;
use ir2::builder::Builder;
use ir2::{BlockId, BlockTarget, Ref};

use crate::compiler::{builtins, Dialects, FunctionToGenerate};
use crate::eval::ConstValue;
use crate::hir::{CastType, LValue, LValueId, Node, Pattern, PatternId};
use crate::irgen::types::get_primitive;
use crate::parser::ast;
use crate::types::{LocalTypeId, LocalTypeIds, OrdinalType};
use crate::Compiler;
use crate::{
    compiler::CheckedFunction,
    hir::{Hir, NodeId},
    types::{TypeInfo, TypeTable},
};

pub fn lower_function(
    compiler: &mut Compiler,
    to_generate: &mut Vec<FunctionToGenerate>,
    name: String,
    checked: &CheckedFunction,
    generics: &[Type],
) -> ir2::Function {
    let mut types = ir2::Types::new();
    // TODO: figure out what to do when params/return_type are Invalid or never types. We can no
    // longer generate a valid signature
    let param_types = types::get_multiple_infos(
        compiler,
        &checked.types,
        &mut types,
        checked.params,
        types::Generics::function_instance(generics),
    )
    .unwrap_or_else(|| {
        types.add_multiple(
            (0..checked.params.count).map(|_| ir2::Type::Primitive(ir2::Primitive::Unit.id())),
        )
    });

    let return_type = checked.types[checked.return_type];
    let return_type = types::get_from_info(
        compiler,
        &checked.types,
        &mut types,
        return_type,
        types::Generics::function_instance(generics),
    )
    .unwrap_or(Primitive::Unit.into());

    let function = if let Some(hir) = &checked.body {
        let builder = ir2::builder::Builder::with_types(compiler, name, types);
        let (_, params) = builder.create_and_begin_block(param_types.iter());
        lower_hir(
            builder,
            hir,
            &checked.types,
            to_generate,
            generics,
            params,
            return_type,
        )
    } else {
        ir2::Function::declare(name, types, param_types.iter(), return_type)
    };
    function.varargs = checked.varargs;
    function
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
    mut builder: ir2::builder::Builder<&mut Compiler>,
    hir: &Hir,
    hir_types: &TypeTable,
    to_generate: &mut Vec<FunctionToGenerate>,
    generics: &[Type],
    params: ir2::Refs,
    return_ty: ir2::TypeId,
) -> ir2::Function {
    let ptr = builder.types.add(ir2::dialect::Primitive::Ptr);
    let vars = hir
        .vars
        .iter()
        .map(|&var_ty| {
            match types::get_from_info(
                builder.env,
                hir_types,
                &mut builder.types,
                hir_types[var_ty],
                types::Generics::function_instance(generics),
            ) {
                Some(ty) => {
                    let ty = builder.types.add(ty);
                    let var = builder.append(builder.env.dialects.mem.Decl(ty, ptr));
                    Ok((var, ty))
                }
                None => {
                    build_crash_point_inner(&mut builder);
                    Err(NoReturn)
                }
            }
        })
        .collect();
    let mut vars: Vec<_> = match vars {
        Ok(vars) => vars,
        Err(NoReturn) => return builder.finish(return_ty),
    };
    debug_assert_eq!(params.count(), hir.params.len() as _);
    let unit_ty = builder.types.add(ir2::Primitive::Unit);
    for (param, &var) in params.iter().zip(&hir.params) {
        builder.append(
            builder
                .env
                .dialects
                .mem
                .Store(vars[var.idx()].0, param, unit_ty),
        );
    }
    let ptr_ty = builder.types.add(ir2::Primitive::Ptr);
    let i1_ty = builder.types.add(ir2::Primitive::I1);
    let mut ctx = Ctx {
        to_generate,
        hir,
        types: hir_types,
        generics,
        generic_types: generics,
        builder,
        vars: &mut vars,
        control_flow_stack: Vec::new(),
        return_ty,
        unit_ty,
        ptr_ty,
        i1_ty,
    };

    let val = lower(&mut ctx, hir.root_id());
    if let Ok(val) = val {
        let unit = ctx.builder.types.add(ir2::Primitive::Unit);
        ctx.builder
            .append(ctx.builder.env.dialects.cf.Ret(val, unit));
    }
    ctx.builder.finish(return_ty)
}

struct Ctx<'a> {
    to_generate: &'a mut Vec<FunctionToGenerate>,
    hir: &'a Hir,
    types: &'a TypeTable,
    generics: &'a [Type],
    generic_types: &'a [Type],
    builder: ir2::builder::Builder<&'a mut Compiler>,
    vars: &'a [(Ref, ir2::TypeId)],
    control_flow_stack: Vec<ControlFlowEntry>,
    return_ty: ir2::TypeId,
    // TODO: improve ergonomics of types, especially primitives in ir, primitives should not have
    // to be added, also for PERF reasons
    unit_ty: ir2::TypeId,
    ptr_ty: ir2::TypeId,
    i1_ty: ir2::TypeId,
}
impl Ctx<'_> {
    fn get_ir_id(
        &mut self,
        module: ModuleId,
        id: ast::FunctionId,
        generics: Vec<Type>,
    ) -> Option<ir2::FunctionId> {
        // check that none of the types is invalid, we never wan't to generate an instance for an
        // invalid type. The caller should build a crash point in that case.
        for ty in &generics {
            if matches!(ty, Type::Invalid) {
                return None;
            }
        }
        let checked = self.builder.env.get_hir(module, id);
        debug_assert_eq!(
            checked.generic_count as usize,
            generics.len(),
            "trying to instantiate a function with an invalid generic count"
        );
        let instances = &mut self.builder.env.modules[module.idx()]
            .ast
            .as_mut()
            .unwrap()
            .instances;

        Some(instances.get_or_insert(id, &generics, |generics| {
            // FIXME: just adding a dummy function right now, stupid solution and might cause issues
            let ir_id = self.builder.env.ir.add_function(
                self.builder.env.ir_module,
                ir2::Function::empty(String::new()),
            );
            self.to_generate.push(FunctionToGenerate {
                ir_id,
                module,
                ast_function_id: id,
                generics,
            });
            ir_id
        }))
    }

    fn get_ir_global(&mut self, module: ModuleId, id: ast::GlobalId) -> Option<ir2::GlobalId> {
        let parsed = self.builder.env.get_parsed_module(module);
        if let Some(global) = parsed.instances.globals[id.idx()] {
            Some(global)
        } else {
            let parsed = self.builder.env.get_parsed_module(module);
            let name = String::from(&*parsed.ast[id].name);
            let (ty, value) = self.builder.env.get_checked_global(module, id);
            let ty = ty.clone();
            // TODO: translate globals or store as bytes in the first place
            //let value = const_value::translate(value);
            let global_id = self.builder.env.ir.add_global(
                self.builder.env.ir_module,
                name,
                1,
                Box::new([1, 2, 3, 4]),
            );
            self.builder.env.get_parsed_module(module).instances.globals[id.idx()] =
                Some(global_id);
            Some(global_id)
        }
    }

    fn get_type(&mut self, ty: TypeInfo) -> Result<ir2::Type> {
        types::get_from_info(
            self.builder.env,
            self.types,
            &mut self.builder.types,
            ty,
            types::Generics::function_instance(self.generics),
        )
        .ok_or_else(|| {
            build_crash_point(self);
            NoReturn
        })
    }

    fn get_multiple_types(&mut self, ids: LocalTypeIds) -> Result<ir2::TypeIds> {
        types::get_multiple_infos(
            self.builder.env,
            self.types,
            &mut self.builder.types,
            ids,
            types::Generics::function_instance(self.generics),
        )
        .ok_or_else(|| {
            build_crash_point(self);
            NoReturn
        })
    }
}

#[derive(Debug, Clone, Copy)]
struct ControlFlowEntry {
    loop_begin: BlockId,
    loop_after: BlockId,
}

fn lower(ctx: &mut Ctx, node: NodeId) -> Result<Ref> {
    Ok(match lower_expr(ctx, node)? {
        ValueOrPlace::Value(r) => r,
        ValueOrPlace::Place { ptr, value_ty } => ctx
            .builder
            .append(ctx.builder.env.dialects.mem.Load(ptr, value_ty)),
    })
}

enum ValueOrPlace {
    Value(Ref),
    Place { ptr: Ref, value_ty: ir2::TypeId },
}

fn lower_expr(ctx: &mut Ctx, node: NodeId) -> Result<ValueOrPlace> {
    let Dialects {
        arith,
        tuple,
        mem,
        cf,
    } = ctx.builder.env.dialects;
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
                ctx.builder.append(arith.Int(small, ty))
            } else {
                todo!("large ints")
                //ctx.builder.build_large_int(val, ty)
            }
        }
        &Node::FloatLiteral { val, ty } => {
            let TypeInfo::Primitive(p) = ctx.types[ty] else {
                crash_point!(ctx)
            };
            debug_assert!(p.is_float());
            let ty = types::get_primitive(p);
            ctx.builder.append(arith.Float(val, ty))
        }
        Node::BoolLiteral(true) => Ref::TRUE,
        Node::BoolLiteral(false) => Ref::FALSE,
        &Node::ArrayLiteral { elems, array_ty } => {
            let TypeInfo::Array { element, count: _ } = ctx.types[array_ty] else {
                panic!("non-array literal type");
            };
            let elem_ir_ty = ctx.get_type(ctx.types[element])?;
            let elem_ir_ty = ctx.builder.types.add(elem_ir_ty);
            let array_ir_ty = ctx
                .builder
                .types
                .add(ir2::Type::Array(elem_ir_ty, elems.count));
            let array_var = ctx.builder.append(mem.Decl(array_ir_ty, ctx.ptr_ty));
            for (elem, i) in elems.iter().zip(0..) {
                let val = lower(ctx, elem)?;
                let u64_ty = ctx.builder.types.add(ir2::Primitive::U64);
                let index = ctx.builder.append(arith.Int(i, u64_ty));
                let member_ptr = ctx
                    .builder
                    .append(mem.ArrayIndex(array_var, index, elem_ir_ty));
                ctx.builder.append(mem.Store(member_ptr, val, ctx.unit_ty));
            }
            return Ok(ValueOrPlace::Place {
                ptr: array_var,
                value_ty: array_ir_ty,
            });
        }
        &Node::TupleLiteral { elems, elem_types } => {
            debug_assert_eq!(elems.count, elem_types.count);
            if elems.count == 0 {
                return Ok(ValueOrPlace::Value(Ref::UNIT));
            }
            let elem_types = ctx.get_multiple_types(elem_types)?;
            let tuple_ty = ctx.builder.types.add(ir2::Type::Tuple(elem_types));
            let mut tuple_val = ctx.builder.append_undef(tuple_ty);
            for (elem, i) in elems.iter().zip(0..) {
                let val = lower(ctx, elem)?;
                tuple_val = ctx
                    .builder
                    .append(tuple.InsertMember(tuple_val, i, val, tuple_ty));
            }
            tuple_val
        }
        &Node::EnumLiteral {
            elems,
            elem_types,
            enum_ty,
        } => {
            debug_assert_eq!(elems.count, elem_types.count);
            let enum_ty = ctx.builder.types.add(ctx.get_type(ctx.types[enum_ty])?);
            let elem_types = ctx.get_multiple_types(elem_types)?;
            let elem_tuple = ctx.builder.types.add(ir2::Type::Tuple(elem_types));
            let var = ctx.builder.append(mem.Decl(enum_ty, ctx.ptr_ty));
            for (elem, i) in elems.iter().zip(0..) {
                let elem_ptr = ctx
                    .builder
                    .append(mem.MemberPtr(var, elem_tuple, i, ctx.ptr_ty));
                let val = lower(ctx, elem)?;
                ctx.builder.append(mem.Store(elem_ptr, val, ctx.unit_ty));
            }
            // maybe do this differently, could do it like llvm: insertvalue
            ctx.builder.append(mem.Load(var, enum_ty))
        }
        Node::StringLiteral(str) => {
            let (s, _value_ty) = lower_string_literal(&mut ctx.builder, str);
            s
        }
        &Node::InferredEnumOrdinal(variant) => {
            let variant = &ctx.types[variant];
            let ty = ctx.types[variant.args.iter().next().unwrap()];
            match ty {
                TypeInfo::Primitive(Primitive::Unit) => Ref::UNIT,
                _ => {
                    let ty = ctx.builder.types.add(ctx.get_type(ty)?);
                    ctx.builder.append(arith.Int(variant.ordinal as u64, ty))
                }
            }
        }

        Node::Declare { pattern: _ } => todo!("lower declarations without values"),
        &Node::DeclareWithVal { pattern, val } => {
            let val = lower(ctx, val)?;
            // ENTRY is passed but should never be used because Declare should have infallible
            // patterns
            lower_pattern(ctx, pattern, val, BlockId::ENTRY)?;
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
            let global = ctx.builder.append(mem.Global(id, ctx.ptr_ty));
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
            use crate::hir::Arithmetic;
            use crate::parser::token::AssignType;

            let arithmetic = match assign_ty {
                AssignType::Assign => {
                    ctx.builder.append(mem.Store(lval, val, ctx.unit_ty));
                    return Ok(ValueOrPlace::Value(Ref::UNIT));
                }
                AssignType::AddAssign => Arithmetic::Add,
                AssignType::SubAssign => Arithmetic::Sub,
                AssignType::MulAssign => Arithmetic::Mul,
                AssignType::DivAssign => Arithmetic::Div,
                AssignType::ModAssign => Arithmetic::Mod,
            };

            let ty = ctx.types[ty];
            let ir_ty = ctx.builder.types.add(ctx.get_type(ty)?);
            let loaded = ctx.builder.append(mem.Load(lval, ir_ty));
            let result = build_arithmetic(ctx, loaded, val, arithmetic, ty);
            ctx.builder.append(mem.Store(lval, result, ctx.unit_ty));
            Ref::UNIT
        }

        &Node::Const { id, ty } => {
            let const_val = &ctx.builder.env.const_values[id.idx()];
            match const_val {
                ConstValue::Unit => Ref::UNIT,
                ConstValue::Bool(true) => Ref::TRUE,
                ConstValue::Bool(false) => Ref::FALSE,
                &ConstValue::Int(num, _) => {
                    let ty = ctx.types[ty];
                    match ty {
                        TypeInfo::Primitive(p) => {
                            debug_assert!(p.is_int());
                            ctx.builder.append(arith.Int(num, get_primitive(p)))
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
                            ctx.builder.append(arith.Float(num, get_primitive(p)))
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
            let ty = ctx.builder.types.add(ty);
            ctx.builder.append(arith.Neg(value, ty))
        }
        &Node::Not(value) => {
            let value = lower(ctx, value)?;
            ctx.builder.append(arith.Neg(value, ctx.i1_ty))
        }
        &Node::AddressOf { value, value_ty: _ } => lower_lval(ctx, value)?,
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
        &Node::Promote { value, variable } => {
            let val = lower(ctx, value)?;
            let var = ctx.vars[variable.idx()].0;
            ctx.builder.append(mem.Store(var, val, ctx.unit_ty));
            var
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
                    ctx.builder.append(arith.CastInt(val, to_ty))
                }
                &CastType::Float { from: _, to } => {
                    let to_ty = types::get_primitive(to.into());
                    ctx.builder.append(arith.CastFloat(val, to_ty))
                }
                &CastType::FloatToInt { from: _, to } => {
                    let to_ty = types::get_primitive(to.into());
                    ctx.builder.append(arith.CastFloatToInt(val, to_ty))
                }
                &CastType::IntToFloat { from: _, to } => {
                    let to_ty = types::get_primitive(to.into());
                    ctx.builder.append(arith.CastIntToFloat(val, to_ty))
                }
                CastType::IntToPtr { from: _ } => ctx.builder.append(mem.IntToPtr(val, ctx.ptr_ty)),
                &CastType::PtrToInt { to } => {
                    let ty = ctx.builder.types.add(types::get_primitive(to.into()));
                    ctx.builder.append(mem.PtrToInt(val, ty))
                }
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
        &Node::Logic { l, r, logic } => {
            let l = lower(ctx, l)?;
            let rhs = ctx.builder.create_block();
            let res = ctx.builder.create_block();
            match logic {
                crate::hir::Logic::And => ctx.builder.append(cf.Branch(
                    l,
                    BlockTarget(rhs, &[]),
                    BlockTarget(res, &[Ref::FALSE]),
                    ctx.unit_ty,
                )),
                crate::hir::Logic::Or => ctx.builder.append(cf.Branch(
                    l,
                    BlockTarget(res, &[Ref::TRUE]),
                    BlockTarget(rhs, &[]),
                    ctx.unit_ty,
                )),
            };
            ctx.builder.begin_block(rhs, []);
            if let Ok(r) = lower(ctx, r) {
                ctx.builder
                    .append(cf.Goto(BlockTarget(res, &[r]), ctx.unit_ty));
            }
            let args = ctx.builder.begin_block(res, [ctx.i1_ty]);
            args.nth(0)
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
                    let elem_ty = ctx.builder.types.add(elem_ty);
                    let value = ctx
                        .builder
                        .append(tuple.MemberValue(val, index.into(), elem_ty));
                    ValueOrPlace::Value(value)
                }
                ValueOrPlace::Place { ptr, value_ty: _ } => {
                    let elem_types = ctx.get_multiple_types(elem_types)?;
                    let elem_tuple = ctx.builder.types.add(ir2::Type::Tuple(elem_types));
                    let member_ptr = ctx
                        .builder
                        .append(mem.MemberPtr(ptr, elem_tuple, index, ctx.ptr_ty));
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
                ptr: ctx.builder.append(mem.ArrayIndex(array, index, elem_ir_ty)),
                value_ty: elem_ir_ty,
            });
        }

        &Node::Return(val) => {
            let val = lower(ctx, val)?;
            ctx.builder.append(cf.Ret(val, ctx.unit_ty));
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
            ctx.builder.append(cf.Branch(
                cond,
                BlockTarget(then_block, &[]),
                BlockTarget(else_block, &[]),
                ctx.unit_ty,
            ));
            ctx.builder.begin_block(then_block, []);
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
                // matching on an uninhabited type so we need to terminate the block
                let undef = ctx.builder.append_undef(ctx.return_ty);
                ctx.builder.append(cf.Ret(undef, ctx.unit_ty));
                return Err(NoReturn);
            }
            for i in 0..branch_count {
                let is_last = i + 1 == branch_count;
                let pattern = PatternId(pattern_index + i);
                let branch = NodeId(branch_index + i);
                next_block = if is_last {
                    BlockId::ENTRY // should never be used
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
                    ctx.builder
                        .append(cf.Goto(BlockTarget(after, &[val]), ctx.unit_ty));
                }
                if is_last {
                    // after could still be none if all branches are noreturn, we don't have to
                    // create an after block at all in this case
                    if let Some(after) = after_block {
                        let ty = ctx.get_type(ctx.types[resulting_ty])?;
                        let ty = ctx.builder.types.add(ty);
                        let args = ctx.builder.begin_block(after, [ty]);
                        result_value = Some(args.nth(0));
                    }
                } else {
                    ctx.builder.begin_block(next_block, []);
                }
            }
            result_value.ok_or(NoReturn)?
        }
        &Node::While { cond, body } => {
            let cond_block = ctx.builder.create_block();
            ctx.builder
                .append(cf.Goto(BlockTarget(cond_block, &[]), ctx.unit_ty));
            ctx.builder.begin_block(cond_block, []);
            let cond = lower(ctx, cond)?;
            let body_block = ctx.builder.create_block();
            let after_block = ctx.builder.create_block();
            ctx.control_flow_stack.push(ControlFlowEntry {
                loop_begin: cond_block,
                loop_after: after_block,
            });
            ctx.builder.append(cf.Branch(
                cond,
                BlockTarget(body_block, &[]),
                BlockTarget(after_block, &[]),
                ctx.unit_ty,
            ));
            ctx.builder.begin_block(body_block, []);
            if lower(ctx, body).is_ok() {
                ctx.builder
                    .append(cf.Goto(BlockTarget(cond_block, &[]), ctx.unit_ty));
            }
            ctx.builder.begin_block(after_block, []);
            Ref::UNIT
        }
        &Node::WhilePat { pat, val, body } => {
            let loop_start = ctx.builder.create_block();
            let after = ctx.builder.create_block();
            ctx.builder
                .append(cf.Goto(BlockTarget(loop_start, &[]), ctx.unit_ty));
            ctx.builder.begin_block(loop_start, []);
            let val = lower(ctx, val)?;
            lower_pattern(ctx, pat, val, after)?;
            if lower(ctx, body).is_ok() {
                ctx.builder
                    .append(cf.Goto(BlockTarget(loop_start, &[]), ctx.unit_ty));
            }
            ctx.builder.begin_block(after, []);
            Ref::UNIT
        }
        &Node::Call {
            function,
            args,
            arg_types,
            return_ty,
            noreturn,
        } => {
            // PERF: we probably need to collect here but reusing the Vec might be better
            // if possible (difficult because calls can be inside the argument list etc.)
            let arg_refs = args
                .iter()
                .map(|arg| lower(ctx, arg))
                .collect::<Result<Vec<_>>>()?;
            let return_info = ctx.types[return_ty];
            let return_ty = ctx.get_type(return_info)?;
            let res = if let Node::FunctionItem(module, id, call_generics) = ctx.hir[function] {
                if (module, id) == builtins::get_intrinsic(ctx.builder.env) {
                    let Node::StringLiteral(intrinsic) = &ctx.hir[args.iter().next().unwrap()]
                    else {
                        panic!("expected string literal passed to intrinsic call");
                    };
                    let return_ty = ctx.builder.types.add(return_ty);
                    return intrinsics::call_intrinsic(ctx, intrinsic, &arg_refs[1..], return_ty);
                }
                let call_generics = call_generics
                    .iter()
                    .map(|generic| ctx.types.to_resolved(ctx.types[generic], ctx.generic_types))
                    .collect();
                let Some(func) = ctx.get_ir_id(module, id, call_generics) else {
                    crash_point!(ctx)
                };
                ctx.builder.append((func, arg_refs, return_ty))
            } else {
                debug_assert_eq!(args.count, arg_types.count);
                let func = lower(ctx, function)?;
                let arg_types = ctx.get_multiple_types(arg_types)?;
                ctx.builder
                    .build_call_ptr(func, arg_refs, arg_types, return_ty)
            };
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
            let layout = ir::type_layout(ctx.get_type(ctx.types[ty])?, ctx.builder.types);
            use crate::hir::TypeProperty;
            let value = match property {
                TypeProperty::Size => layout.size,
                TypeProperty::Align => layout.align.get(),
                TypeProperty::Stride => layout.stride(),
            };
            ctx.builder.build_int(value, IrType::U64)
        }
        &Node::FunctionItem(module, id, generics) => {
            let generics = generics
                .iter()
                .map(|generic| ctx.types.to_resolved(ctx.types[generic], ctx.generic_types))
                .collect();
            let Some(id) = ctx.get_ir_id(module, id, generics) else {
                crash_point!(ctx)
            };
            ctx.builder.build_function_ptr(id)
        }
        &Node::Capture(i) => {
            let (captures, captures_ty) = ctx.vars[ctx.hir.params[0].idx()];
            let IrType::Tuple(capture_types) = ctx.builder.types[captures_ty] else {
                unreachable!()
            };
            return Ok(ValueOrPlace::Place {
                ptr: ctx.builder.build_member_ptr(captures, i.0, capture_types),
                value_ty: capture_types.nth(i.0),
            });
        }
        &Node::Break(n) | &Node::Continue(n) => {
            let entry = ctx.control_flow_stack
                [ctx.control_flow_stack.len() - usize::try_from(n).unwrap() - 1];
            let target = if matches!(ctx.hir[node], Node::Break(_)) {
                entry.loop_after
            } else {
                entry.loop_begin
            };
            ctx.builder.terminate_block(Terminator::Goto(target, &[]));
            return Err(NoReturn);
        }
    };
    Ok(ValueOrPlace::Value(value))
}

fn lower_lval(ctx: &mut Ctx, lval: LValueId) -> Result<Ref> {
    Ok(match ctx.hir[lval] {
        LValue::Invalid => crash_point!(ctx),
        LValue::Variable(id) => ctx.vars[id.idx()].0,
        LValue::Global(module, id) => {
            let Some(id) = ctx.get_ir_global(module, id) else {
                crash_point!(ctx)
            };
            ctx.builder.build_global(id, IrType::Ptr)
        }
        LValue::Deref(pointer) => lower(ctx, pointer)?,
        LValue::Member {
            tuple,
            index,
            elem_types,
        } => {
            let ptr = lower_lval(ctx, tuple)?;
            let types = ctx.get_multiple_types(elem_types)?;
            ctx.builder.build_member_ptr(ptr, index, types)
        }
        LValue::ArrayIndex {
            array,
            index,
            elem_ty: element_type,
        } => {
            let ptr = lower_lval(ctx, array)?;
            let idx = lower(ctx, index)?;
            let ty = ctx.get_type(ctx.types[element_type])?;
            let ty = ctx.builder.types.add(ty);
            ctx.builder.build_array_index(ptr, idx, ty)
        }
    })
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
        ctx.builder.begin_block(on_match, []);
    };
    match &ctx.hir[pattern] {
        Pattern::Invalid => crash_point!(ctx),
        Pattern::Variable(id) => {
            ctx.builder.build_store(ctx.vars[id.idx()].0, value);
        }
        Pattern::Ignore => {}
        &Pattern::Tuple {
            member_count,
            patterns,
            types,
        } => {
            for i in 0..member_count {
                let member_pat = PatternId(patterns + i);
                let member_ty = ctx.get_type(ctx.types[LocalTypeId(types + i)])?;
                let member_value = ctx.builder.build_member_value(value, i, member_ty);
                lower_pattern(ctx, member_pat, member_value, on_mismatch)?;
            }
        }
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
            ctx.builder.begin_block(on_match, []);
        }
        Pattern::String(s) => {
            let str_eq = builtins::get_str_eq(ctx.compiler);
            // can unwrap here because we don't pass invalid generics
            let str_eq = ctx.get_ir_id(str_eq.0, str_eq.1, Vec::new()).unwrap();
            let (expected, _str_ty) = lower_string_literal(&mut ctx.builder, s);
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
    let str_ptr = builder.build_string(s.as_bytes(), true);
    let tuple = builder.build_insert_member(Ref::UNDEF, 0, str_ptr, str_ty);
    let str_len = builder.build_int(s.len() as u64, IrType::U64);
    let tuple = builder.build_insert_member(tuple, 1, str_len, str_ty);
    (tuple, str_ty)
}

fn build_crash_point(ctx: &mut Ctx) {
    build_crash_point_inner(&mut ctx.builder);
}

fn build_crash_point_inner(builder: &mut Builder<&mut Compiler>) {
    let msg = "program reached a compile error at runtime";
    let (msg, _str_ty) = lower_string_literal(builder, msg);
    let panic_function = builder.env.get_builtin_panic();
    let unit = builder.types.add(ir2::Primitive::Unit);
    builder.append((panic_function, (msg), unit));

    builder.append(builder.env.dialects.mem.Ret());
    builder.terminate_block(Terminator::Ret(Ref::UNDEF));
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
    ctx.builder.begin_block(else_block, []);
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
