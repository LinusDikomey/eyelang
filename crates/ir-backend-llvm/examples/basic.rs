//! Example for compiling a function using this backend based on llvm. Creates a module, displays
//! it and then emits it to an object file called 'out.o'.

use ir::{IrTypes, IrType, builder::{BinOp, Terminator, IrBuilder}, Function, Primitive, Module};

fn main() {
    let module = Module {
        name: "main_module".to_owned(),
        funcs: vec![build_mul(), build_extern_printf()],
    };
    eprintln!("Module:\n{module}");
    let mut backend = ir_backend_llvm::Backend::new();
    backend.enable_logging();
    backend.emit_module(&module, None, std::path::Path::new("out.o")).expect("Backend failed");
}

fn build_mul() -> Function {
    let mut types = IrTypes::new();
    let int_ty = types.add(IrType::Primitive(Primitive::I32));
    let mut builder = IrBuilder::new(&mut types);

    let x = builder.build_param(0, int_ty);
    let y = builder.build_param(1, int_ty);
    let res = builder.build_bin_op(BinOp::Mul, x, y, int_ty);
    builder.terminate_block(Terminator::Ret(res));

    let ir = builder.finish();
    Function {
        name: "mul".to_owned(),
        types,
        params: vec![int_ty, int_ty],
        varargs: false,
        return_type: int_ty,
        ir: Some(ir),
    }
}

fn build_extern_printf() -> Function {
    let mut types = IrTypes::new();
    let ptr_ty = types.add(IrType::Primitive(Primitive::Ptr));
    let int_ty = types.add(IrType::Primitive(Primitive::I32));
    Function {
        name: "printf".to_owned(),
        types,
        params: vec![ptr_ty],
        varargs: true,
        return_type: int_ty,
        ir: None,
    }
}
