use ir::{Environment, builder::Builder};

use crate::{Type, compiler::Dialects};

/// Create function wrapping and calling main to handle exit codes properly.
/// This will return the main functions exit code casted to i32 if it is an integer.
/// If the main returns unit, it will always return 0.
pub fn entry_point(
    eye_main: ir::FunctionId,
    main_return_ty: Type,
    env: &Environment,
    dialects: &Dialects,
) -> ir::Function {
    let Dialects { arith, cf, .. } = dialects;

    let mut builder = Builder::new(env);
    builder.create_and_begin_block([]);

    let main_return = match main_return_ty {
        Type::Unit => ir::Type::UNIT,
        Type::I8 => ir::Type::Primitive(ir::Primitive::I8.into()),
        Type::U8 => ir::Type::Primitive(ir::Primitive::U8.into()),
        Type::I16 => ir::Type::Primitive(ir::Primitive::I16.into()),
        Type::U16 => ir::Type::Primitive(ir::Primitive::U16.into()),
        Type::I32 => ir::Type::Primitive(ir::Primitive::I32.into()),
        Type::U32 => ir::Type::Primitive(ir::Primitive::U32.into()),
        Type::I64 => ir::Type::Primitive(ir::Primitive::I64.into()),
        Type::U64 => ir::Type::Primitive(ir::Primitive::U64.into()),
        Type::I128 => ir::Type::Primitive(ir::Primitive::I128.into()),
        Type::U128 => ir::Type::Primitive(ir::Primitive::U128.into()),
        _ => unreachable!("unexpected return type from main: {main_return_ty:?}"),
    };

    let main_ret_ty = builder.types.add(main_return);
    let i32_ty = builder.types.add(ir::dialect::Primitive::I32);

    let main_val = builder.append((eye_main, (), main_ret_ty));
    let exit_code = match main_return {
        ir::Type::Tuple(_) => builder.append(arith.Int(0, i32_ty)),
        ir::Type::Primitive(p) if ir::Primitive::try_from(p).unwrap() == ir::Primitive::I32 => {
            main_val
        }
        _ => builder.append(arith.CastInt(main_val, i32_ty)),
    };
    let unit = builder.types.add(ir::Type::UNIT);
    builder.append(cf.Ret(exit_code, unit));

    builder.finish("main", i32_ty)
}
