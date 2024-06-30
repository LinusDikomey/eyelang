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
    eprintln!("Module:\n{module}");
    ir::verify::module(&module);
    let mut backend = ir_backend_x86::Backend::new();
    backend.enable_logging();
    backend
        .emit_module(&module, true, None, std::path::Path::new("diff.o"))
        .expect("Backend failed");
}

fn build_diff() -> Function {
    let mut types = IrTypes::new();
    let int_ty = types.add(IrType::I32);
    let param_types = types.add_multiple([types[int_ty], types[int_ty]]);
    let (mut builder, params) = IrBuilder::new(&mut types, param_types);

    let x = params.nth(0);
    let y = params.nth(1);

    let lt = builder.build_bin_op(BinOp::LT, x, y, IrType::I32);
    let on_true = builder.create_block();
    let on_false = builder.create_block();
    let after = builder.create_block();
    builder.terminate_block(Terminator::Branch {
        cond: lt,
        on_true: (on_true, &[]),
        on_false: (on_false, &[]),
    });

    builder.begin_block(on_true);
    // TODO: should be Sub instruction but that isn't implemented yet
    let y_minus_x = builder.build_bin_op(BinOp::Add, y, x, IrType::I32);
    builder.terminate_block(Terminator::Goto(after, &[y_minus_x]));

    builder.begin_block(on_false);
    // TODO: should be Sub instruction but that isn't implemented yet
    let x_minus_y = builder.build_bin_op(BinOp::Add, x, y, IrType::I32);
    builder.terminate_block(Terminator::Goto(after, &[x_minus_y]));

    let args = builder.begin_block_with_args(after, int_ty.into());
    builder.terminate_block(Terminator::Ret(args.nth(0)));

    let ir = builder.finish();
    let return_type = types[int_ty];
    Function {
        name: "diff".to_owned(),
        types,
        params: param_types,
        varargs: false,
        return_type,
        ir: Some(ir),
    }
}
