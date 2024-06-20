use ir::{
    builder::{BinOp, IrBuilder, Terminator},
    Function, IrType, IrTypes, Module,
};

fn main() {
    let module = Module {
        name: "main_module".to_owned(),
        funcs: vec![build_add()],
        globals: vec![],
    };
    eprintln!("Module:\n{module}");
    let mut backend = ir_backend_x86::Backend::new();
    backend.enable_logging();
    backend
        .emit_module(&module, true, None, std::path::Path::new("out.o"))
        .expect("Backend failed");
}

fn build_add() -> Function {
    let mut types = IrTypes::new();
    let int_ty = types.add(IrType::I32);
    let mut builder = IrBuilder::new(&mut types);

    let x = builder.build_param(0, int_ty);
    let y = builder.build_param(1, int_ty);
    let res = builder.build_bin_op(BinOp::Add, x, y, int_ty);
    builder.terminate_block(Terminator::Ret(res));

    let ir = builder.finish();
    let params = types.add_multiple([types[int_ty], types[int_ty]]);
    let return_type = types[int_ty];
    Function {
        name: "my_add".to_owned(),
        types,
        params,
        varargs: false,
        return_type,
        ir: Some(ir),
    }
}
