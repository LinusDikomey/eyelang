mod entry_point;
mod types;

pub use entry_point::entry_point;

use id::ModuleId;
use ir::{RefVal, TypeRefs};
use ir::builder::{Terminator, BinOp};
use ir::{IrType, Ref, builder::IrBuilder};
use ::types::Type;

use crate::Compiler;
use crate::compiler::FunctionToGenerate;
use crate::eval::ConstValue;
use crate::hir::{Node, PatternId, Pattern, CastType, LValueId, LValue};
use crate::irgen::types::get_primitive;
use crate::parser::ast;
use crate::type_table::LocalTypeId;
use crate::{
    compiler::CheckedFunction,
    type_table::{TypeTable, TypeInfo},
    hir::{NodeId, HIR},
};

pub fn lower_function(
    compiler: &mut Compiler,
    to_generate: &mut Vec<FunctionToGenerate>,
    _src: &str,
    name: String,
    checked: &CheckedFunction,
    generics: &[Type],
) -> ir::Function {
    let mut types = ir::IrTypes::new();
    let generics = types::get_multiple(compiler, &mut types, generics, TypeRefs::EMPTY);
    let params = types::get_multiple_infos(compiler, &checked.types, &mut types, checked.params, generics);
    let return_type = checked.types[checked.return_type];
    let return_type = types::get_from_info(compiler, &checked.types, &mut types, return_type, generics);

    let ir = checked.body.as_ref().map(|hir| {
        let mut builder = ir::builder::IrBuilder::new(&mut types);
        let mut vars = vec![Ref::UNDEF; hir.vars.len()];

        for (i, ty) in params.iter().enumerate() {
            vars[i] = builder.build_decl(ty);
            let param_val = builder.build_param(i as u32, ty);
            builder.build_store(vars[i], param_val);
        }

        let mut noreturn = false;

        let mut ctx = Ctx {
            compiler,
            to_generate,
            hir,
            types: &checked.types,
            generics,
            builder,
            vars: &mut vars,
        };
        let val = lower(&mut ctx, hir.root_id(), &mut noreturn);
        if !noreturn {
            ctx.builder.terminate_block(Terminator::Ret(val));
        }
        ctx.builder.finish()
    });
    ir::Function {
        name,
        types,
        params,
        return_type,
        varargs: checked.varargs,
        ir,
    }
}

struct Ctx<'a> {
    compiler: &'a mut Compiler,
    to_generate: &'a mut Vec<FunctionToGenerate>,
    hir: &'a HIR,
    types: &'a TypeTable,
    generics: TypeRefs,
    builder: IrBuilder<'a>,
    vars: &'a mut [Ref],
}
impl<'a> Ctx<'a> {

    fn get_ir_id(&mut self, module: ModuleId, id: ast::FunctionId, generics: Vec<Type>) -> ir::FunctionId {
        self.compiler.get_hir(module, id);
        let instances = &mut self.compiler.modules[module.idx()]
            .ast.as_mut().unwrap().2;

        let potential_id = ir::FunctionId(self.compiler.ir_module.funcs.len() as _);

        match instances.get_or_insert(id, &generics, potential_id) {
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
        }
    }

    fn get_type(&mut self, ty: TypeInfo) -> IrType {
        types::get_from_info(self.compiler, self.types, self.builder.types, ty, self.generics)
    }
}

fn lower(
    ctx: &mut Ctx,
    node: NodeId,
    noreturn: &mut bool,
) -> Ref {
    match lower_expr(ctx, node, noreturn) {
        ValueOrPlace::Value(r) => r,
        ValueOrPlace::Place { ptr, value_ty } => {
            if *noreturn { return Ref::UNDEF }
            let ty = ctx.get_type(ctx.types[value_ty]);
            ctx.builder.build_load(ptr, ty)
        }
    }
}

enum ValueOrPlace {
    Value(Ref),
    Place {
        ptr: Ref,
        value_ty: LocalTypeId,
    },
}

fn lower_expr(
    ctx: &mut Ctx,
    node: NodeId,
    noreturn: &mut bool,
) -> ValueOrPlace {
    debug_assert!(!*noreturn, "lowering new expression with noreturn already active should not happen");
    let value = match &ctx.hir[node] {
        Node::Invalid => build_crash_point(ctx, noreturn),

        &Node::CheckPattern(pat, value) => {
            let value = lower(ctx, value, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            lower_pattern(ctx, pat, value, noreturn)
        }

        Node::Block(items) => {
            for item in items.iter() {
                lower(ctx, item, noreturn);
                if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            }
            Ref::UNIT
        }

        Node::Unit => Ref::UNIT,
        &Node::IntLiteral { val, ty } => {
            let TypeInfo::Primitive(p) = ctx.types[ty] else {
                build_crash_point(ctx, noreturn);
                return ValueOrPlace::Value(Ref::UNDEF);
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
                build_crash_point(ctx, noreturn);
                return ValueOrPlace::Value(Ref::UNDEF);
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
            let elem_ir_ty = ctx.get_type(ctx.types[element]);
            let elem_ir_ty = ctx.builder.types.add(elem_ir_ty);
            let array_ir_ty = ctx.builder.types.add(IrType::Array(elem_ir_ty, elems.count));
            let array_var = ctx.builder.build_decl(array_ir_ty);
            for (elem, i) in elems.iter().zip(0..) {
                let val = lower(ctx, elem, noreturn);
                if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
                let index = ctx.builder.build_int(i, IrType::U64);
                let member_ptr = ctx.builder.build_array_index(array_var, index, elem_ir_ty);
                ctx.builder.build_store(member_ptr, val);
            }
            return ValueOrPlace::Place {
                ptr: array_var,
                value_ty: array_ty,
            }
        }
        &Node::TupleLiteral { elems, elem_types } => {
            debug_assert_eq!(elems.count, elem_types.count);
            let tuple_ty = ctx.get_type(TypeInfo::Tuple(elem_types));
            let IrType::Tuple(elem_types) = tuple_ty else { unreachable!() };
            let var = ctx.builder.build_decl(tuple_ty);
            for (elem, i) in elems.iter().zip(0..) {
                let elem_ptr = ctx.builder.build_member_ptr(var, i, elem_types);
                let val = lower(ctx, elem, noreturn);
                if *noreturn {
                    return ValueOrPlace::Value(Ref::UNDEF);
                }
                ctx.builder.build_store(elem_ptr, val);
            }
            // maybe do this differently, could do it like llvm: insertvalue
            ctx.builder.build_load(var, tuple_ty)
        }
        Node::StringLiteral(_) => todo!(),

        Node::Declare { pattern: _ } => todo!("lower declarations without values"),
        &Node::DeclareWithVal { pattern, val } => {
            let val = lower(ctx, val, noreturn);
            if !*noreturn {
                lower_pattern(ctx, pattern, val, noreturn);
            }
            Ref::UNIT
        }
        Node::Variable(id) => return ValueOrPlace::Place {
            ptr: ctx.vars[id.idx()],
            value_ty: ctx.hir.vars[id.idx()],
        },
        &Node::Assign(lval, val) => {
            let lval = lower_lval(ctx, lval, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            let val = lower(ctx, val, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            ctx.builder.build_store(lval, val);
            Ref::UNIT
        }

        &Node::Const { id, ty } => {
            let const_val = &ctx.compiler.const_values[id.idx()];
            match const_val {
                ConstValue::Unit => Ref::UNIT,
                &ConstValue::Number(num) => {
                    let ty = ctx.types[ty];
                    match ty {
                        TypeInfo::Primitive(p) => {
                            debug_assert!(p.is_int());
                            ctx.builder.build_int(num, get_primitive(p))
                        }
                        TypeInfo::Invalid => {
                            build_crash_point(ctx, noreturn)
                        }
                        _ => unreachable!(),
                    }
                }
                ConstValue::Undefined => build_crash_point(ctx, noreturn),
            }
        }

        &Node::Negate(value, ty) => {
            let value = lower(ctx, value, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            let ty = ctx.get_type(ctx.types[ty]);
            ctx.builder.build_neg(value, ty)
        }
        &Node::Not(value) => {
            let value = lower(ctx, value, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            ctx.builder.build_neg(value, IrType::U1)
        }
        &Node::AddressOf { inner, value_ty } => {
            let value = lower_expr(ctx, inner, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) };
            match value {
                ValueOrPlace::Value(v) => {
                    let ty = ctx.get_type(ctx.types[value_ty]);
                    let ptr = ctx.builder.build_decl(ty);
                    ctx.builder.build_store(ptr, v);
                    ptr
                }
                ValueOrPlace::Place { ptr, value_ty: _ } => ptr,
            }
        }
        &Node::Deref { value, deref_ty } => {
            let value = lower(ctx, value, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            let ty = ctx.get_type(ctx.types[deref_ty]);
            ctx.builder.build_load(value, ty)
        }

        &Node::Cast(id) => {
            let cast = &ctx.hir[id];
            let val = lower(ctx, cast.val, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            // TODO: separate into multiple more specific cast instructions in ir
            match &cast.cast_ty {
                CastType::Invalid => build_crash_point(ctx, noreturn),
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
                &CastType::PtrToInt { to } => {
                    ctx.builder.build_ptr_to_int(val, types::get_primitive(to.into()))
                }
                CastType::EnumToInt { .. } => todo!("cast enums to integers, might be removed"),
            }
        }
        &Node::Comparison(l, r, cmp) => {
            let l = lower(ctx, l, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            let r = lower(ctx, r, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            use crate::hir::Comparison;
            let op = match cmp {
                Comparison::Eq => BinOp::Eq,
                Comparison::NE => BinOp::NE,
                Comparison::LT => BinOp::LT,
                Comparison::GT => BinOp::GT,
                Comparison::LE => BinOp::LE,
                Comparison::GE => BinOp::GE,
                Comparison::And => BinOp::And,
                Comparison::Or => BinOp::Or,
            };
            ctx.builder.build_bin_op(op, l, r, IrType::U1)
        }
        &Node::Arithmetic(l, r, op, ty) => {
            let l = lower(ctx, l, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            let r = lower(ctx, r, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }

            use crate::hir::Arithmetic;
            let op = match op {
                Arithmetic::Add => BinOp::Add,
                Arithmetic::Sub => BinOp::Sub,
                Arithmetic::Mul => BinOp::Mul,
                Arithmetic::Div => BinOp::Div,
                Arithmetic::Mod => BinOp::Mod,
            };
            let TypeInfo::Primitive(p) = ctx.types[ty] else {
                panic!("Invalid type {:?} for arithmetic op. Will be handled properly with traits", ctx.types[ty]);
            };
            assert!(p.is_int() || p.is_float(), "Invalid primitive type {p} for arithmetic op. Will be handled properly with traits");
            ctx.builder.build_bin_op(op, l, r, types::get_primitive(p))
        }

        &Node::TupleIndex { tuple_value, index, elem_ty } => {
            let tuple = lower(ctx, tuple_value, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            let elem_ty = ctx.get_type(ctx.types[elem_ty]);
            ctx.builder.build_member_value(tuple, index, elem_ty)
        }
        &Node::ArrayIndex { array, index, elem_ty } => {
            let array = match lower_expr(ctx, array, noreturn) {
                ValueOrPlace::Value(_) => todo!("array indexing without place"),
                ValueOrPlace::Place { ptr, .. } => ptr,
            };
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            let index = lower(ctx, index, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            let elem_ir_ty = ctx.get_type(ctx.types[elem_ty]);
            let elem_ir_ty = ctx.builder.types.add(elem_ir_ty);
            return ValueOrPlace::Place {
                ptr: ctx.builder.build_array_index(array, index, elem_ir_ty),
                value_ty: elem_ty,
            }
        }

        &Node::Return(val) => {
            let val = lower(ctx, val, noreturn);
            if !*noreturn {
                ctx.builder.terminate_block(Terminator::Ret(val));
                *noreturn = true;
            }
            Ref::UNDEF
        }
        &Node::IfElse { cond, then, else_, resulting_ty } => {
            let cond = lower(ctx, cond, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            let then_block = ctx.builder.create_block();
            let else_block = ctx.builder.create_block();
            // after_block is a closure that creates the block lazily and returns it
            let mut after_block = {
                let mut after_block = None;
                move |ctx: &mut Ctx| after_block.unwrap_or_else(|| {
                    let block = ctx.builder.create_block();
                    after_block = Some(block);
                    block
                })
            };
            ctx.builder.terminate_block(Terminator::Branch { cond, on_true: then_block, on_false: else_block });
            let mut check_branch = |ctx: &mut Ctx, value: NodeId| -> Option<(ir::BlockIndex, Ref)> {
                let mut noreturn = false;
                let val = lower(ctx, value, &mut noreturn);
                (!noreturn).then(|| {
                    let block = ctx.builder.current_block();
                    let after_block = after_block(ctx);
                    ctx.builder.terminate_block(Terminator::Goto(after_block));
                    (block, val)
                })
            };
            ctx.builder.begin_block(then_block);
            let then_val = check_branch(ctx, then);
            ctx.builder.begin_block(else_block);
            let else_val = check_branch(ctx, else_);
            match (then_val, else_val) {
                (Some(t), Some(f)) => {
                    let after_block = after_block(ctx);
                    ctx.builder.begin_block(after_block);
                    let ty = ctx.get_type(ctx.types[resulting_ty]);
                    ctx.builder.build_phi([t, f], ty)
                }
                (Some((_, val)), None) | (None, Some((_, val))) => {
                    let after_block = after_block(ctx);
                    ctx.builder.begin_block(after_block);
                    val
                }
                (None, None) => {
                    *noreturn = true;
                    Ref::UNDEF
                }
            }
        }
        Node::Match { .. } => todo!("lower match"),
        &Node::While { cond, body } => {
            let cond_block = ctx.builder.create_block();
            ctx.builder.terminate_block(Terminator::Goto(cond_block));
            ctx.builder.begin_block(cond_block);
            let cond = lower(ctx, cond, noreturn);
            if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
            let body_block = ctx.builder.create_block();
            let after_block = ctx.builder.create_block();
            ctx.builder.terminate_block(Terminator::Branch {
                cond,
                on_true: body_block,
                on_false: after_block,
            });
            ctx.builder.begin_block(body_block);
            let mut body_noreturn = false;
            lower(ctx, body, &mut body_noreturn);
            if !body_noreturn {
                ctx.builder.terminate_block(Terminator::Goto(cond_block));
            }
            ctx.builder.begin_block(after_block);
            Ref::UNIT
        }
        &Node::Call { function, generics: call_generics, args, return_ty } => {
            let mut arg_refs = Vec::with_capacity(args.iter().count());
            for arg in args.iter() {
                let arg = lower(ctx, arg, noreturn);
                if *noreturn { return ValueOrPlace::Value(Ref::UNDEF) }
                arg_refs.push(arg);
            }
            let call_generics = call_generics
                .iter()
                .map(|generic| ctx.types.to_resolved(ctx.types[generic]))
                .collect();
            let func = ctx.get_ir_id(function.0, function.1, call_generics);
            let return_ty = ctx.get_type(ctx.types[return_ty]);
            ctx.builder.build_call(func, arg_refs, return_ty)
        }
    };
    ValueOrPlace::Value(value)
}

fn lower_lval(ctx: &mut Ctx, lval: LValueId, noreturn: &mut bool) -> Ref {
    match ctx.hir[lval] {
        LValue::Invalid => build_crash_point(ctx, noreturn),
        LValue::Variable(id) => ctx.vars[id.idx()],
        LValue::Global(_, _) => todo!("handle ir for globals"),
        LValue::Deref(pointer) => lower(ctx, pointer, noreturn),
    }
}

fn lower_pattern(
    ctx: &mut Ctx,
    pattern: PatternId,
    value: Ref,
    noreturn: &mut bool
) -> Ref {
    match ctx.hir[pattern] {
        Pattern::Invalid => build_crash_point(ctx, noreturn),
        Pattern::Variable(id) => {
            let var_ty = ctx.types[ctx.hir.vars[id.idx()]];
            let ty = ctx.get_type(var_ty);
            let var = ctx.builder.build_decl(ty);
            ctx.vars[id.idx()] = var;
            ctx.builder.build_store(var, value);
            Ref::val(RefVal::True)
        }
        Pattern::Ignore => Ref::val(RefVal::True),
        Pattern::Tuple(_) => todo!(),
        Pattern::Int(sign, val, ty) => {
            let TypeInfo::Primitive(p) = ctx.types[ty] else { panic!("integer type expected") };
            let ty = types::get_primitive(p);
            debug_assert!(p.is_int());
            let mut pattern_value = if let Ok(small) = val.try_into() {
                ctx.builder.build_int(small, ty)
            } else {
                ctx.builder.build_large_int(val, ty)
            };
            if sign {
                pattern_value = ctx.builder.build_neg(pattern_value, ty);
            }
            ctx.builder.build_bin_op(BinOp::Eq, value, pattern_value, ty)
        }
        Pattern::Bool(true) => value,
        Pattern::Bool(false) => ctx.builder.build_not(value, ir::IrType::U1),
        Pattern::Range { .. } => todo!(),
    }
}

fn build_crash_point(ctx: &mut Ctx, noreturn: &mut bool) -> Ref {
    // TODO: build proper crash point
    // let msg = "program reached a compile error at runtime";
    // let msg = ctx.builder.build_string(msg.as_bytes(), true, IrType::Ptr);
    let block = ctx.builder.create_block();
    ctx.builder.terminate_block(Terminator::Goto(block));
    ctx.builder.begin_block(block);
    ctx.builder.terminate_block(Terminator::Goto(block));
    *noreturn = true;
    Ref::UNDEF
}

