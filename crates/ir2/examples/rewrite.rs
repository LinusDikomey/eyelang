use ir2::dialect::Primitive;

fn main() {
    let mut env = ir2::Environment::new(Primitive::create_infos());
    let main_module = env.create_module("main");
    let func = create_add_function(&mut env);
    let func_id = env.add_function(main_module, func);
    let rewriter = AddZeroRewriter::new(&mut env);
    println!("Before rewrite:\n{}", env.display_module(main_module));

    let mut func_ir = env.remove_body(func_id).unwrap();
    ir2::rewrite::rewrite_in_place(&mut func_ir, env[func_id].types(), &env, rewriter);
    env.reattach_body(func_id, func_ir);

    println!("After rewrite:\n{}", env.display_module(main_module));
}

fn create_add_function(env: &mut ir2::Environment) -> ir2::Function {
    let arith = env.get_dialect_module::<ir2::dialect::Arith>();
    let cf = env.get_dialect_module::<ir2::dialect::Cf>();

    let mut builder = ir2::builder::Builder::new(&*env);
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
ir2::rewrite::rewrite_rules! {
    // name of the rewriter type
    AddZeroRewriter
    // define all the arguments, this should never be changed and is only needed so the variables
    // can be used in pattern code
    ir types inst

    // specify that we want to use the Arith dialect in the rules
    use arith: ir2::dialect::Arith;

    patterns:

    // remove trivial adds
    (arith.Add a (arith.Int 0)) => a;
    // swap operands of adds around. This is just a demonstration and not really useful in
    // real-world use cases
    (arith.Add a b) => arith.Add(b, a, inst.ty());
}
