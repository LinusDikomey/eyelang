use ir2::{
    builder::Builder,
    dialect::{Arith, Cf, Mem, Primitive},
    Environment, Function, ModuleId, ModuleOf, Parameter,
};

fn main() {
    let mut env = Environment::new(Primitive::create_infos());
    let arith = env.add_dialect_module::<Arith>();
    let cf = env.add_dialect_module::<Cf>();
    let mem = env.add_dialect_module::<Mem>();
    let main = env.create_module("main");
    let my_function = env.add_function(
        main,
        Function {
            name: "my_function".into(),
            types: ir2::Types::new(),
            params: vec![Parameter::Ref, Parameter::Ref, Parameter::Ref],
            varargs: false,
            terminator: false,
            return_type: None,
            ir: None,
        },
    );
    let string_constant = env.add_global(
        main,
        "my_string",
        1,
        "Hello, World".to_owned().into_bytes().into_boxed_slice(),
    );
    env.add_global(main, "my_i32", 4, Box::new([1, 2, 3, 4]));

    let mut builder = Builder::new(&env, "add_numbers");
    builder.create_and_begin_block();
    let int_ty = builder.types.add(Primitive::I32);
    let unit = builder.types.add(Primitive::Unit);
    let i1 = builder.types.add(Primitive::I1);
    let ptr = builder.types.add(Primitive::Ptr);
    let one = builder.append(arith.Int(1), int_ty);
    let two = builder.append(arith.Int(2), int_ty);
    let result = builder.append(arith.Add(one, two), int_ty);
    let then_block = builder.create_block();
    let else_block = builder.create_block();
    let cond = builder.append(arith.LT(two, result), i1);
    builder.append(cf.Branch(cond, then_block, else_block), unit);
    builder.begin_block(then_block);
    builder.append(cf.Ret(result), unit);
    builder.begin_block(else_block);
    let my_res = builder.append((my_function, (one, two, result)), int_ty);
    let var = builder.append(mem.Decl(int_ty), ptr);
    builder.append(mem.Store(var, two), unit);
    builder.append(mem.Load(var), int_ty);
    builder.append(mem.Global(string_constant), ptr);
    builder.append(cf.Ret(my_res), unit);

    let my_add = env.add_function(main, builder.finish());

    println!("{}", env.display_module(main));

    let modules = Modules {
        arith,
        cf,
        mem,
        main,
    };
    lower(&modules, &env[my_add]);
}

pub struct Modules {
    arith: ModuleOf<Arith>,
    cf: ModuleOf<Cf>,
    mem: ModuleOf<Mem>,
    main: ModuleId,
}

fn lower(modules: &Modules, function: &Function) {
    let Some(ir) = &function.ir else { return };
    for block in ir.block_ids() {
        for (r, inst) in ir.get_block(block) {
            if let Some(inst) = inst.as_module(modules.arith) {
                match inst.op() {
                    Arith::Int => {
                        println!("int with {:?}", inst.args(ir.extra()).collect::<Vec<_>>());
                    }
                    Arith::Add => {
                        println!("add with {:?}", inst.args(ir.extra()).collect::<Vec<_>>());
                    }
                    _ => {}
                }
            } else if let Some(inst) = inst.as_module(modules.cf) {
                match inst.op() {
                    Cf::Ret => println!("return found"),
                    Cf::Branch => println!(
                        "branch found with {:?}",
                        inst.args(ir.extra()).collect::<Vec<_>>()
                    ),
                    _ => {}
                }
            } else if let Some(_inst) = inst.as_module(modules.mem) {
            } else if inst.module() == modules.main {
            } else {
                panic!("unknown module")
            }
        }
    }
}
