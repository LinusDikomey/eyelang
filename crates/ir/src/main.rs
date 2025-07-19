use ir::Environment;

fn main() {
    std::concat!();
    std::eprintln!();
    let mut file = None;
    let mut output = None;
    let mut optimize = false;
    let mut passes = false;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--optimize" => optimize = true,
            "--passes" => passes = true,
            "-o" => {
                if output.is_some() {
                    panic!("duplicate option -o");
                }
                output = Some(args.next().expect("file expected after -o"));
            }
            s => {
                if file.is_some() {
                    panic!("unexpected argument '{s}'");
                }
                file = Some(arg);
            }
        }
    }
    let file = file.expect("missing positional argument for input file");
    let contents = std::fs::read_to_string(file).expect("can't read input file");

    let mut env = Environment::new(ir::Primitive::create_infos());
    ir::dialect::register_all(&mut env);
    let (mut ir, mut types) = ir::parse::parse_function_body(&env, &contents);
    println!("Parsed function body:\n{}", ir.display(&env, &types));
    if optimize {
        let mut pipeline = ir::optimize::Pipeline::optimizing(&mut env);
        if passes {
            pipeline.enable_print_passes();
        }
        ir = pipeline.optimize_function(&mut env, ir, &mut types);
        println!("Final IR:\n{}", ir.display(&env, &types));
    }
    if let Some(output) = output {
        color_format::config::set_override(false);
        let s = format!("{}", ir.display(&env, &types));
        std::fs::write(output, s).expect("Failed to write output file");
    }
}
