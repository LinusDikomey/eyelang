//! Example for using the ir crate. A function is constructed manually and evaluated.
//! It is also debug printed.

use ir::{ir_types::{IrTypes, IrType}, builder::{BinOp, Terminator}, Function, display::Info};
use types::Primitive;

fn main() {
    let mut types = IrTypes::new();
    let mut builder = ir::builder::IrBuilder::new(&mut types);

    let loop_body = builder.create_block();
    let end = builder.create_block();

    let int_ty = builder.types.add(IrType::Primitive(Primitive::I32));

    let variable = builder.build_decl(int_ty);

    let one = builder.build_int(1, int_ty);
    let three = builder.build_int(3, int_ty);
    builder.build_store(variable, three);
    let zero = builder.build_int(0, int_ty);
    builder.terminate_block(Terminator::Goto(loop_body));

    builder.begin_block(loop_body);
    let loaded = builder.build_load(variable, int_ty);
    let new_value = builder.build_bin_op(BinOp::Sub, loaded, one, int_ty);
    builder.build_store(variable, new_value);
    let is_zero = builder.build_bin_op(BinOp::Eq, new_value, zero, IrType::Primitive(Primitive::Bool));
    builder.terminate_block(Terminator::Branch { cond: is_zero, on_true: end, on_false: loop_body });

    builder.begin_block(end);
    builder.terminate_block(Terminator::Ret(three));

    let ir = builder.finish();
    let function = Function {
        name: "my_function".to_owned(),
        types,
        params: vec![],
        varargs: false,
        return_type: int_ty,
        ir: Some(ir),
    };

    let display = function.ir.as_ref().unwrap().display(Info { funcs: &[] }, &function.types);
    eprintln!("{display}");
    let value = ir::eval::eval(&function, &[]);
    eprintln!("Function evaluated to {value:?}");
}
