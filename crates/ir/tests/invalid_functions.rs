use ir::{builder::Terminator, Function, IrType, Ref, RefVal, TypeRefs};

#[test]
#[should_panic(expected = "assertion failed: dom_tree.dominates")]
fn non_dominating_use() {
    let mut types = ir::IrTypes::new();
    let mut builder = ir::builder::IrBuilder::new(&mut types);
    let block_a = builder.create_block();
    let block_b = builder.create_block();
    builder.terminate_block(Terminator::Branch {
        cond: Ref::val(RefVal::True),
        on_true: block_a,
        on_false: block_b,
    });
    builder.begin_block(block_a);
    let a = builder.build_int(10, IrType::I32);
    builder.terminate_block(Terminator::Goto(block_b));

    builder.begin_block(block_b);
    builder.build_neg(a, IrType::I32);
    builder.terminate_block(Terminator::Ret(Ref::UNIT));

    let ir = builder.finish();

    let f = Function {
        name: "invalid_function".to_owned(),
        types,
        params: TypeRefs::EMPTY,
        varargs: false,
        return_type: IrType::Unit,
        ir: Some(ir),
    };
    ir::verify::function(&f);
}
