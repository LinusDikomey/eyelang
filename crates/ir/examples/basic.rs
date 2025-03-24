//! Example for using the ir crate. A function is constructed, printed, verified and evaluated.

use ir::{BlockTarget, Environment, Primitive, builder::Builder};

fn main() {
    let mut env = Environment::new(Primitive::create_infos());
    let arith = env.get_dialect_module::<ir::dialect::Arith>();
    let mem = env.get_dialect_module::<ir::dialect::Mem>();
    let cf = env.get_dialect_module::<ir::dialect::Cf>();

    let mut builder = ir::builder::Builder::new(&env);
    builder.create_and_begin_block([]);

    let loop_body = builder.create_block();
    let end = builder.create_block();

    let unit_ty = builder.types.add(Primitive::Unit);
    let i1_ty = builder.types.add(Primitive::I1);
    let int_ty = builder.types.add(Primitive::I32);
    let ptr_ty = builder.types.add(Primitive::Ptr);

    let variable = builder.append(mem.Decl(int_ty, ptr_ty));
    let sum = builder.append(mem.Decl(int_ty, ptr_ty));

    let one = builder.append(arith.Int(1, int_ty));
    let counter = builder.append(arith.Int(10, int_ty));
    builder.append(mem.Store(variable, counter, unit_ty));
    let zero = builder.append(arith.Int(0, int_ty));
    builder.append(cf.Goto(BlockTarget(loop_body, &[]), unit_ty));

    builder.begin_block(loop_body, []);
    let loaded = builder.append(mem.Load(variable, int_ty));
    let loaded_sum = builder.append(mem.Load(sum, int_ty));
    let new_sum = builder.append(arith.Add(loaded_sum, loaded, int_ty));
    builder.append(mem.Store(sum, new_sum, unit_ty));
    let new_value = builder.append(arith.Sub(loaded, one, int_ty));
    builder.append(mem.Store(variable, new_value, unit_ty));
    let is_zero = builder.append(arith.Eq(new_value, zero, i1_ty));
    builder.append(cf.Branch(
        is_zero,
        BlockTarget(end, &[]),
        BlockTarget(loop_body, &[]),
        unit_ty,
    ));

    builder.begin_block(end, []);
    let loaded_sum = builder.append(mem.Load(sum, int_ty));
    builder.append(cf.Ret(loaded_sum, unit_ty));

    let function = builder.finish("my_function", int_ty);

    ir::verify::function(&env, &function);

    let display = function.display(&env);
    eprintln!("{display}");

    let value = ir::eval::eval(function.ir().unwrap(), function.types(), &[], &mut env);
    eprintln!("Function evaluated to {value:?}");

    // another example: mul function taking in parameters
    let mul = build_mul(&mut env);
    ir::verify::function(&env, &mul);

    let display = mul.ir().unwrap().display(&env, mul.types());
    eprintln!("{display}");
    let args = [ir::eval::Val::Int(5), ir::eval::Val::Int(3)];
    let result = ir::eval::eval(mul.ir().unwrap(), mul.types(), &args, &mut env)
        .expect("Function call failed");
    eprintln!("{:?}*{:?} = {:?}", args[0], args[1], result);
}

fn build_mul(env: &mut Environment) -> ir::Function {
    let arith = env.get_dialect_module::<ir::dialect::Arith>();
    let cf = env.get_dialect_module::<ir::dialect::Cf>();
    let mut builder = Builder::new(env);
    let int_ty = builder.types.add(Primitive::I32);
    let unit_ty = builder.types.add(Primitive::Unit);
    let (_entry, params) = builder.create_and_begin_block([int_ty; 2]);
    let x = params.nth(0);
    let y = params.nth(1);

    let res = builder.append(arith.Mul(x, y, int_ty));
    builder.append(cf.Ret(res, unit_ty));
    builder.finish("mul", int_ty)
}
