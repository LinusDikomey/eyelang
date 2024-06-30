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
    ir::verify::module(&module);
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
    let param_types = types.add_multiple([types[int_ty], types[int_ty]]);
    let (mut builder, params) = IrBuilder::new(&mut types, param_types);
    let x = params.nth(0);
    let y = params.nth(1);

    let stack_val = builder.build_decl(IrType::I32);
    let constant = builder.build_int(0x42, int_ty);
    builder.build_store(stack_val, constant);
    let res = builder.build_bin_op(BinOp::Add, x, y, int_ty);
    let loaded = builder.build_load(stack_val, IrType::I32);
    let res = builder.build_bin_op(BinOp::Add, res, loaded, int_ty);
    builder.terminate_block(Terminator::Ret(res));

    let ir = builder.finish();
    let return_type = types[int_ty];
    Function {
        name: "my_add".to_owned(),
        types,
        params: param_types,
        varargs: false,
        return_type,
        ir: Some(ir),
    }
}
