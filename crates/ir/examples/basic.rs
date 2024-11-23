//! Example for using the ir crate. A function is constructed, printed, verified and evaluated.

use ir::{
    builder::{BinOp, IrBuilder, Terminator},
    display::Info,
    Function, IrType, IrTypes, TypeRefs,
};

fn main() {
    let mut types = IrTypes::new();
    let (mut builder, _params) = ir::builder::IrBuilder::new(&mut types, TypeRefs::EMPTY);

    let loop_body = builder.create_block();
    let end = builder.create_block();

    let int_ty = builder.types.add(IrType::I32);

    let variable = builder.build_decl(int_ty);

    let one = builder.build_int(1, int_ty);
    let three = builder.build_int(3, int_ty);
    builder.build_store(variable, three);
    let zero = builder.build_int(0, int_ty);
    builder.terminate_block(Terminator::Goto(loop_body, &[]));

    builder.begin_block(loop_body);
    let loaded = builder.build_load(variable, int_ty);
    let new_value = builder.build_bin_op(BinOp::Sub, loaded, one, int_ty);
    builder.build_store(variable, new_value);
    let is_zero = builder.build_bin_op(BinOp::Eq, new_value, zero, IrType::U1);
    builder.terminate_block(Terminator::Branch {
        cond: is_zero,
        on_true: (end, &[]),
        on_false: (loop_body, &[]),
    });

    builder.begin_block(end);
    builder.terminate_block(Terminator::Ret(three));

    let ir = builder.finish();
    let function = Function {
        name: "my_function".to_owned(),
        types,
        params: TypeRefs::EMPTY,
        varargs: false,
        return_type: IrType::I32,
        ir: Some(ir),
    };

    let display = function
        .ir
        .as_ref()
        .unwrap()
        .display(Info { funcs: &[] }, &function.types);

    ir::verify::function(&function);

    eprintln!("{display}");
    let value = ir::eval::eval(
        &function.ir.as_ref().unwrap(),
        &function.types,
        &[],
        &mut ir::eval::EmptyEnv,
    );
    eprintln!("Function evaluated to {value:?}");

    // another example: square function taking in parameters
    let mul = build_mul();
    ir::verify::function(&mul);

    let display = mul
        .ir
        .as_ref()
        .unwrap()
        .display(Info { funcs: &[] }, &mul.types);
    eprintln!("{display}");
    let args = [ir::eval::Val::Int(5), ir::eval::Val::Int(3)];
    let result = ir::eval::eval(
        &mul.ir.as_ref().unwrap(),
        &mul.types,
        &args,
        &mut ir::eval::EmptyEnv,
    )
    .expect("Function call failed");
    eprintln!("{:?}*{:?} = {:?}", args[0], args[1], result);
}

fn build_mul() -> Function {
    let mut types = IrTypes::new();
    let param_types = types.add_multiple([IrType::I32; 2]);
    let (mut builder, params) = IrBuilder::new(&mut types, param_types);
    let x = params.nth(0);
    let y = params.nth(1);

    let res = builder.build_bin_op(BinOp::Mul, x, y, param_types.nth(0));
    builder.terminate_block(Terminator::Ret(res));

    let ir = builder.finish();
    Function {
        name: "mul".to_owned(),
        types,
        params: param_types,
        varargs: false,
        return_type: IrType::I32,
        ir: Some(ir),
    }
}
