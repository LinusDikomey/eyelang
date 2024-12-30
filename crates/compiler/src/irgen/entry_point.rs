use ir2::{builder::Builder, Environment};
use types::{Primitive, Type};

use crate::compiler::Dialects;

/// Create function wrapping and calling main to handle exit codes properly.
/// This will return the main functions exit code casted to i32 if it is an integer.
/// If the main returns unit, it will always return 0.
pub fn entry_point(
    eye_main: ir2::FunctionId,
    main_return_ty: &Type,
    env: &Environment,
    dialects: &Dialects,
) -> ir2::Function {
    let Dialects { arith, cf, .. } = dialects;

    let mut builder = Builder::new(env, "main");
    builder.create_and_begin_block([]);

    let main_return = match main_return_ty {
        Type::Primitive(Primitive::Unit) => ir2::dialect::Primitive::Unit,
        &Type::Primitive(p) if p.is_int() => super::types::get_primitive(p),
        _ => unreachable!(),
    };

    let main_ret_ty = builder.types.add(main_return);
    let i32_ty = builder.types.add(ir2::dialect::Primitive::I32);

    let main_val = builder.append((eye_main, (), main_ret_ty));
    let exit_code = match main_return {
        ir2::dialect::Primitive::Unit => builder.append(arith.Int(0, i32_ty)),
        ir2::dialect::Primitive::I32 => main_val,
        _ => builder.append(arith.CastInt(main_val, i32_ty)),
    };
    let unit = builder.types.add(ir2::dialect::Primitive::Unit);
    builder.append(cf.Ret(exit_code, unit));

    builder.finish(i32_ty)
}
