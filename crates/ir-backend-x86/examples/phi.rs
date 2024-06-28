use ir::{
    builder::{BinOp, IrBuilder, Terminator},
    Function, IrType, IrTypes, Module,
};

fn main() {
    let module = Module {
        name: "main_module".to_owned(),
        funcs: vec![build_diff()],
        globals: vec![],
    };
    ir::verify::module(&module);
    eprintln!("Module:\n{module}");
    let mut backend = ir_backend_x86::Backend::new();
    backend.enable_logging();
    backend
        .emit_module(&module, true, None, std::path::Path::new("diff.o"))
        .expect("Backend failed");
}

fn build_diff() -> Function {
    let mut types = IrTypes::new();
    let int_ty = types.add(IrType::I32);
    let mut builder = IrBuilder::new(&mut types);

    let x = builder.build_param(0, int_ty);
    let y = builder.build_param(1, int_ty);
    let lt = builder.build_bin_op(BinOp::LT, x, y, IrType::I32);
    let on_true = builder.create_block();
    let on_false = builder.create_block();
    let after = builder.create_block();
    builder.terminate_block(Terminator::Branch {
        cond: lt,
        on_true,
        on_false,
    });

    builder.begin_block(on_true);
    // TODO: should be Sub instruction but that isn't implemented yet
    let y_minus_x = builder.build_bin_op(BinOp::Add, y, x, IrType::I32);
    builder.terminate_block(Terminator::Goto(after));

    builder.begin_block(on_false);
    // TODO: should be Sub instruction but that isn't implemented yet
    let x_minus_y = builder.build_bin_op(BinOp::Add, x, y, IrType::I32);
    builder.terminate_block(Terminator::Goto(after));

    builder.begin_block(after);
    let retval = builder.build_phi([(on_true, y_minus_x), (on_false, x_minus_y)], IrType::I32);
    builder.terminate_block(Terminator::Ret(retval));

    let ir = builder.finish();
    let params = types.add_multiple([types[int_ty], types[int_ty]]);
    let return_type = types[int_ty];
    Function {
        name: "diff".to_owned(),
        types,
        params,
        varargs: false,
        return_type,
        ir: Some(ir),
    }
}
