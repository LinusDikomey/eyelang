use ir::{dialect::Primitive, modify::IrModify, rewrite::LinearRewriteOrder};

fn main() {
    let mut env = ir::Environment::new(Primitive::create_infos());
    let main_module = env.create_module("main");
    let func = create_add_function(&mut env);
    let func_id = env.add_function(main_module, func);
    let mut rewriter = AddZeroRewriter::new(&mut env);
    println!("Before rewrite:\n{}", env.display_module(main_module));

    let mut func_ir = IrModify::new(env.remove_body(func_id).unwrap());
    ir::rewrite::rewrite_in_place(
        &mut func_ir,
        env[func_id].types(),
        &env,
        &mut (),
        &mut rewriter,
        LinearRewriteOrder::new(),
    );
    env.reattach_body(func_id, func_ir.finish_and_compress(&env));

    println!("After rewrite:\n{}", env.display_module(main_module));
}

fn create_add_function(env: &mut ir::Environment) -> ir::Function {
    let arith = env.get_dialect_module::<ir::dialect::Arith>();
    let cf = env.get_dialect_module::<ir::dialect::Cf>();

    let mut builder = ir::builder::Builder::new(&*env);
    let int_ty = builder.types.add(Primitive::I32);
    let (_, args) = builder.create_and_begin_block([int_ty; 3]);
    let result = builder.append(arith.Add(args.nth(0), args.nth(1), int_ty));
    let result = builder.append(arith.Add(result, args.nth(2), int_ty));
    let int_zero = builder.append(arith.Int(0, int_ty));
    let return_value = builder.append(arith.Add(result, int_zero, int_ty));
    builder.append(cf.Ret(return_value, int_ty));
    builder.finish("add", int_ty)
}

// this macro defines a type AddZeroRewriter that implements Rewriter
// it matches all of the listed, potentially recursive rules on each instruction
ir::rewrite::visitor! {
    // name of the rewriter type
    AddZeroRewriter,
    ir::rewrite::Rewrite,
    // define all the arguments, this should never be changed and is only needed so the variables
    // can be used in pattern code
    ir, types, inst, env, _dialects,
    _ctx: ();

    // specify that we want to use the Arith dialect in the rules
    use arith: ir::dialect::Arith;

    patterns:

    // remove trivial adds
    (arith.Add a (arith.Int 0)) => a;
    // swap operands of adds around. This is just a demonstration and not really useful in
    // real-world use cases
    (arith.Add a b) => arith.Add(b, a, inst.ty());
}
