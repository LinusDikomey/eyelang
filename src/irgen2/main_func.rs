use crate::{resolve::{types::{Type, FunctionHeader}, type_info::{TypeInfo, TypeTable}}, ir::{Function, builder::IrBuilder, FunctionId}, types::{Primitive, IntType}, ast::ModuleId};


/// Add hidden function wrapping and calling main to handle exit codes properly.
/// This will return the main functions exit code casted to i32 if it is an integer.
/// If the main returns unit, it will always return 0.
pub fn main_wrapper(eye_main: FunctionId, module: ModuleId, main_return_ty: Type) -> Function {
    let mut builder = IrBuilder::new(TypeTable::new(0), vec![]);
    //let extra = builder.extra_data(&eye_main.bytes());

    let main_return = match main_return_ty {
        Type::Prim(Primitive::Unit) => None,
        Type::Prim(p) if p.is_int() => Some(p.as_int().unwrap()),
        _ => unreachable!()
    };

    let main_ret_ty = builder.types.add(
        main_return.map_or(TypeInfo::UNIT, |int_ty| TypeInfo::Primitive(int_ty.into()))
    );
    let i32_ty = builder.types.add(TypeInfo::Primitive(Primitive::I32));

    let main_val = builder.build_call(eye_main, [], main_ret_ty);
    let exit_code = match main_return {
        Some(IntType::I32) => main_val,
        Some(_) => builder.build_cast(main_val, i32_ty),
        None => builder.build_int(0, i32_ty)
    };
    builder.build_ret(exit_code);
    
    let ir = builder.finish();

    Function {
        header: FunctionHeader {
            name: "main".to_owned(),
            params: vec![],
            varargs: false,
            return_type: Type::Prim(Primitive::I32),
            inherited_generic_count: 0,
            generics: vec![],
            resolved_body: None,
            module,
        },
        ir: Some(ir)
    }
}