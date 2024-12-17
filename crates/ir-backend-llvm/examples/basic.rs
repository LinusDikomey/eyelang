//! Example for compiling a function using this backend based on llvm. Creates a module, displays
//! it and then emits it to an object file called 'out.o'.

use ir2::{
    dialect::{Arith, Cf, Primitive},
    Environment, ModuleOf, Type,
};

fn main() {
    let mut env = Environment::new(ir2::dialect::Primitive::create_infos());
    let module = env.create_module("main");
    let arith = env.add_dialect_module::<Arith>();
    let cf = env.add_dialect_module::<Cf>();
    env.add_dialect_module::<ir2::dialect::Tuple>();
    env.add_dialect_module::<ir2::dialect::Mem>();

    let mul = build_mul(&env, arith, cf);
    env.add_function(module, mul);

    println!("{}", env.display_module(module));

    let mut backend = ir_backend_llvm::Backend::new();
    backend.enable_logging();
    backend
        .emit_module(
            &env,
            &env[module],
            true,
            None,
            std::path::Path::new("out.o"),
        )
        .expect("Backend failed");
}

fn build_mul(env: &Environment, arith: ModuleOf<Arith>, cf: ModuleOf<Cf>) -> ir2::Function {
    let mut builder = ir2::builder::Builder::new(env, "my_mul");
    let unit = builder.types.add(Primitive::Unit);
    let int_ty = builder.types.add(Primitive::I32);
    //let param_types = builder.types.add_multiple([Primitive::I32.into(); 2]);
    builder.create_and_begin_block();
    let a = builder.append(arith.Int(5), int_ty);
    let b = builder.append(arith.Int(7), int_ty);
    let res = builder.append(arith.Mul(a, b), int_ty);
    builder.append(cf.Ret(res), unit);

    builder.finish(int_ty)
}
