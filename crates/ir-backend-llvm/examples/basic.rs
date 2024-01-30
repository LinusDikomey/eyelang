//! Example for compiling a function using this backend based on llvm. Creates a module, displays
//! it and then emits it to an object file called 'out.o'.

use ir::{IrTypes, IrType, builder::{BinOp, Terminator, IrBuilder}, Function, Module};

fn main() {
    let module = Module {
        name: "main_module".to_owned(),
        funcs: vec![build_mul() , build_extern_printf()],
    };
    eprintln!("Module:\n{module}");
    let mut backend = ir_backend_llvm::Backend::new();
    backend.enable_logging();
    backend.emit_module(&module, true, None, std::path::Path::new("out.o")).expect("Backend failed");
}

fn build_mul() -> Function {
    let mut types = IrTypes::new();
    let int_ty = types.add(IrType::I32);
    let mut builder = IrBuilder::new(&mut types);

    let x = builder.build_param(0, int_ty);
    let y = builder.build_param(1, int_ty);
    let res = builder.build_bin_op(BinOp::Mul, x, y, int_ty);
    let s = builder.build_string("hello from eye ir!\n".as_bytes(), true, IrType::Ptr);
    builder.build_call(ir::FunctionId::from_bytes(1u64.to_le_bytes()), [s], int_ty);
    builder.terminate_block(Terminator::Ret(res));

    let ir = builder.finish();
    let params = types.add_multiple([types[int_ty], types[int_ty]]);
    let return_type = types[int_ty];
    Function {
        name: "mul".to_owned(),
        types,
        params,
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
