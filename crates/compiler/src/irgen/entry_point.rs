use ir::{
    builder::{IrBuilder, Terminator},
    FunctionId, IrType, IrTypes, TypeRefs,
};
use types::{Primitive, Type};

/// Create function wrapping and calling main to handle exit codes properly.
/// This will return the main functions exit code casted to i32 if it is an integer.
/// If the main returns unit, it will always return 0.
pub fn entry_point(eye_main: FunctionId, main_return_ty: &Type) -> ir2::Function {
    let mut types = IrTypes::new();
    let (mut builder, _params) = IrBuilder::new(&mut types, TypeRefs::EMPTY);
    //let extra = builder.extra_data(&eye_main.bytes());

    let main_return = match main_return_ty {
        Type::Primitive(Primitive::Unit) => IrType::Unit,
        &Type::Primitive(p) if p.is_int() => super::types::get_primitive(p),
        _ => unreachable!(),
    };

    let main_ret_ty = builder.types.add(main_return);
    let i32_ty = builder.types.add(IrType::I32);

    let main_val = builder.build_call(eye_main, [], main_ret_ty);
    let exit_code = match main_return {
        ir2::Type::Primitive(p) => match ir2::dialect::Primitive::try_from(p).unwrap() {
            ir2::dialect::Primitive::Unit => builder.build_int(0, i32_ty),
            ir2::dialect::Primitive::I32 => main_val,
            _ => builder.build_cast_int(main_val, IrType::I32),
        },
        _ => unreachable!(),
    };
    builder.terminate_block(Terminator::Ret(exit_code));

    let ir = builder.finish();

    ir2::Function::new("main", types, vec![], i32_ty, ir)
}
