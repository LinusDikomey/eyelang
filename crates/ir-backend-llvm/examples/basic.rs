//! Example for compiling a function using this backend based on llvm. Creates a module, displays
//! it and then emits it to an object file called 'out.o'.

use ir2::{
    dialect::{Arith, Cf, Mem, Primitive},
    Environment, ModuleOf, Type,
};

fn main() {
    let mut env = Environment::new(ir2::dialect::Primitive::create_infos());
    let module = env.create_module("main");
    let dialects = Dialects {
        arith: env.add_dialect_module(),
        cf: env.add_dialect_module(),
        mem: env.add_dialect_module(),
        tuple: env.add_dialect_module(),
    };

    let mul = build_mul(&env, &dialects);
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

struct Dialects {
    arith: ModuleOf<ir2::dialect::Arith>,
    cf: ModuleOf<ir2::dialect::Cf>,
    mem: ModuleOf<ir2::dialect::Mem>,
    tuple: ModuleOf<ir2::dialect::Tuple>,
}

fn build_mul(env: &Environment, dialects: &Dialects) -> ir2::Function {
    let Dialects { arith, cf, .. } = dialects;
    let mut builder = ir2::builder::Builder::new(env, "my_mul");
    let unit = builder.types.add(Primitive::Unit);
    let int_ty = builder.types.add(Primitive::I32);
    let param_types = builder.types.add_multiple([Primitive::I32.into(); 2]);
    let (_, params) = builder.create_and_begin_block(param_types.iter());
    let five = builder.append(arith.Int(5), int_ty);
    let res = builder.append(arith.Add(params.nth(0), five), int_ty);
    let res = builder.append(arith.Mul(res, params.nth(1)), int_ty);
    builder.append(cf.Ret(res), unit);

    builder.finish(int_ty)
}

fn build_main(env: &Environment, dialects: &Dialects) -> ir2::Function {
    let Dialects {
        arith,
        cf,
        mem,
        tuple,
    } = dialects;
    let mut builder = ir2::builder::Builder::new(env, "main");
    let unit = builder.types.add(Primitive::Unit);
    builder.create_and_begin_block([]);
    let ret = builder.append(, unit);
    builder.append(builtin.Un, )
    // TODO: Ref::Unit
    builder.append(cf.Ret(), )
    builder.finish(unit)
}
