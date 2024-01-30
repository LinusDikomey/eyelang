use ir::{FunctionId, builder::{IrBuilder, Terminator}, IrTypes, IrType, TypeRefs};
use types::{Type, Primitive};

/// Create function wrapping and calling main to handle exit codes properly.
/// This will return the main functions exit code casted to i32 if it is an integer.
/// If the main returns unit, it will always return 0.
pub fn entry_point(eye_main: FunctionId, main_return_ty: &Type) -> ir::Function {
    let mut types = IrTypes::new();
    let mut builder = IrBuilder::new(&mut types);
    //let extra = builder.extra_data(&eye_main.bytes());

    let main_return = match main_return_ty {
        Type::Primitive(Primitive::Unit) => IrType::Unit,
        &Type::Primitive(p) if p.is_int() => super::types::get_primitive(p),
        _ => unreachable!()
    };

    let main_ret_ty = builder.types.add(main_return);
    let i32_ty = builder.types.add(IrType::I32);

    let main_val = builder.build_call(eye_main, [], main_ret_ty);
    let exit_code = match main_return {
        ir::IrType::I32 => main_val,
        ir::IrType::Unit => builder.build_int(0, i32_ty),
        _ => builder.build_cast_int(main_val, IrType::I32),
    };
    builder.terminate_block(Terminator::Ret(exit_code));
    
    let ir = builder.finish();

    ir::Function {
        name: "main".to_owned(),
        types,
        params: TypeRefs::EMPTY,
        varargs: false,
        return_type: IrType::I32,
        ir: Some(ir)
    }
}
