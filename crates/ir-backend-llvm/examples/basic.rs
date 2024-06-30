//! Example for compiling a function using this backend based on llvm. Creates a module, displays
//! it and then emits it to an object file called 'out.o'.

use ir::{
    builder::{BinOp, IrBuilder, Terminator},
    Function, IrType, IrTypes, Module,
};

fn main() {
    let module = Module {
        name: "main_module".to_owned(),
        funcs: vec![build_mul(), build_extern_printf()],
        globals: vec![],
    };
    eprintln!("Module:\n{module}");
    let mut backend = ir_backend_llvm::Backend::new();
    backend.enable_logging();
    backend
        .emit_module(&module, true, None, std::path::Path::new("out.o"))
        .expect("Backend failed");
}

fn build_mul() -> Function {
    let mut types = IrTypes::new();
    let int_ty = types.add(IrType::I32);
    let param_types = types.add_multiple([types[int_ty], types[int_ty]]);
    let (mut builder, params) = IrBuilder::new(&mut types, param_types);
    let res = builder.build_bin_op(BinOp::Mul, params.nth(0), params.nth(1), int_ty);
    let s = builder.build_string("hello from eye ir!\n".as_bytes(), true);
    builder.build_call(ir::FunctionId::from_bytes(1u64.to_le_bytes()), [s], int_ty);
    builder.terminate_block(Terminator::Ret(res));

    let ir = builder.finish();
    let return_type = types[int_ty];
    Function {
        name: "mul".to_owned(),
        types,
        params: param_types,
        varargs: false,
        return_type,
        ir: Some(ir),
    }
}

fn build_extern_printf() -> Function {
    let mut types = IrTypes::new();
    let params = types.add_multiple([IrType::Ptr]);
    Function {
        name: "printf".to_owned(),
        types,
        params,
        varargs: true,
        return_type: IrType::I32,
        ir: None,
    }
}
