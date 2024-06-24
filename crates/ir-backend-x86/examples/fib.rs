use ir::{
    builder::{BinOp, IrBuilder, Terminator},
    Function, IrType, IrTypes, Module, Ref,
};

fn main() {
    let module = Module {
        name: "main_module".to_owned(),
        funcs: vec![build_loop()],
        globals: vec![],
    };
    eprintln!("Module:\n{module}");
    let mut backend = ir_backend_x86::Backend::new();
    backend.enable_logging();
    backend
        .emit_module(&module, true, None, std::path::Path::new("out.o"))
        .expect("Backend failed");
}

fn build_loop() -> Function {
    let mut types = IrTypes::new();
    let int_ty = types.add(IrType::I32);
    let mut builder = IrBuilder::new(&mut types);

    let end_value = builder.build_param(0, int_ty);
    let loop_var = builder.build_decl(IrType::I32);
    let zero = builder.build_int(0, int_ty);
    builder.build_store(loop_var, zero);

    let loop_body = builder.create_block();
    builder.terminate_block(Terminator::Goto(loop_body));
    builder.begin_block(loop_body);

    let loop_value = builder.build_load(loop_var, int_ty);
    let one = builder.build_int(1, int_ty);
    let new_value = builder.build_bin_op(BinOp::Add, loop_value, one, int_ty);
    builder.build_store(loop_var, new_value);
    let cond = builder.build_bin_op(BinOp::LT, new_value, end_value, IrType::U1);
    let after = builder.create_block();
    builder.terminate_block(Terminator::Branch {
        cond,
        on_true: loop_body,
        on_false: after,
    });

    builder.begin_block(after);
    builder.terminate_block(Terminator::Ret(Ref::UNIT));

    let ir = builder.finish();
    let params = types.add_multiple([types[int_ty]]);
    Function {
        name: "my_loop".to_owned(),
        types,
        params,
        varargs: false,
        return_type: IrType::Unit,
        ir: Some(ir),
    }
}
