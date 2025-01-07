use ir2::{
    builder::Builder,
    dialect::{Arith, Cf, Mem, Primitive},
    BlockTarget, Environment, Function, ModuleId, ModuleOf,
};

fn main() {
    let mut env = Environment::new(Primitive::create_infos());
    let arith = env.add_dialect_module::<Arith>();
    let cf = env.add_dialect_module::<Cf>();
    let mem = env.add_dialect_module::<Mem>();
    let main = env.create_module("main");
    let my_function = {
        let mut types = ir2::Types::new();
        let i32 = types.add(Primitive::I32);
        let unit = types.add(Primitive::Unit);
        env.add_function(
            main,
            Function::declare("my_function", types, [i32; 3], false, unit),
        )
    };
    let string_constant = env.add_global(
        main,
        "my_string",
        1,
        "Hello, World".to_owned().into_bytes().into_boxed_slice(),
    );
    env.add_global(main, "my_i32", 4, Box::new([1, 2, 3, 4]));

    let mut builder = Builder::new(&env);
    let int_ty = builder.types.add(Primitive::I32);
    let (_entry, params) = builder.create_and_begin_block([int_ty, int_ty]);
    let unit = builder.types.add(Primitive::Unit);
    let i1 = builder.types.add(Primitive::I1);
    let ptr = builder.types.add(Primitive::Ptr);
    let result = builder.append(arith.Add(params.nth(0), params.nth(1), int_ty));
    let then_block = builder.create_block();
    let else_block = builder.create_block();
    let cond = builder.append(arith.LT(params.nth(1), result, i1));
    builder.append((
        ir2::FunctionId {
            module: cf.id(),
            function: Cf::Branch.id(),
        },
        (
            cond,
            BlockTarget(then_block, &[params.nth(0)]),
            BlockTarget(else_block, &[params.nth(1)]),
        ),
        unit,
    ));
    builder.begin_block(then_block, [int_ty]);
    builder.append(cf.Ret(result, unit));
    builder.begin_block(else_block, [int_ty]);
    let my_res = builder.append((my_function, (params.nth(0), params.nth(1), result), int_ty));
    let var = builder.append(mem.Decl(int_ty, ptr));
    builder.append(mem.Store(var, result, unit));
    builder.append(mem.Load(var, int_ty));
    builder.append(mem.Global(string_constant, ptr));
    builder.append(cf.Ret(my_res, unit));

    let my_add = env.add_function(main, builder.finish("add_numbers", int_ty));

    println!("{}", env);

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
    let Some(ir) = function.ir() else { return };
    for block in ir.block_ids() {
        for (_r, inst) in ir.get_block(block) {
            if let Some(inst) = inst.as_module(modules.arith) {
                match inst.op() {
                    Arith::Int => {
                        println!("int with {:?}", ir.typed_args(&inst).collect::<Vec<_>>());
                    }
                    Arith::Add => {
                        println!("add with {:?}", ir.typed_args(&inst).collect::<Vec<_>>());
                    }
                    _ => {}
                }
            } else if let Some(inst) = inst.as_module(modules.cf) {
                match inst.op() {
                    Cf::Ret => println!("return found"),
                    Cf::Branch => {
                        println!(
                            "branch found with {:?}",
                            ir.typed_args(&inst).collect::<Vec<_>>()
                        )
                    }
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
