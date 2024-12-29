use ir2::{builder::Builder, Environment};
use types::{Primitive, Type};

/// Create function wrapping and calling main to handle exit codes properly.
/// This will return the main functions exit code casted to i32 if it is an integer.
/// If the main returns unit, it will always return 0.
pub fn entry_point(
    eye_main: ir2::FunctionId,
    main_return_ty: &Type,
    env: &Environment,
) -> ir2::Function {
    let arith = env.get_dialect_module::<ir2::dialect::Arith>();
    let cf = env.get_dialect_module::<ir2::dialect::Cf>();

    let mut types = ir2::Types::new();
    let mut builder = Builder::new(env, "main");

    let main_return = match main_return_ty {
        Type::Primitive(Primitive::Unit) => ir2::dialect::Primitive::Unit,
        &Type::Primitive(p) if p.is_int() => super::types::get_primitive(p),
        _ => unreachable!(),
    };

    let main_ret_ty = builder.types.add(main_return);
    let i32_ty = builder.types.add(ir2::dialect::Primitive::I32);

    let main_val = builder.append((eye_main, (), main_ret_ty));
    let exit_code = match main_return {
        ir2::Type::Primitive(p) => match ir2::dialect::Primitive::try_from(p).unwrap() {
            ir2::dialect::Primitive::Unit => builder.append(arith.Int(0, i32_ty)),
            ir2::dialect::Primitive::I32 => main_val,
            _ => builder.append(arith.CastInt(main_val, i32_ty)),
        },
        _ => unreachable!(),
    };
    let unit = builder.types.add(ir2::dialect::Primitive::Unit);
    builder.append(cf.Ret(exit_code, unit));

    builder.finish(i32_ty)
}
