use color_format::ceprintln;

mod mem2reg;

pub use mem2reg::Mem2Reg;

use crate::{Environment, FunctionIr, ModuleId, Types};

pub trait FunctionPass: std::fmt::Debug {
    fn run(&self, env: &Environment, types: &Types, ir: FunctionIr) -> FunctionIr;
}

#[derive(Default)]
pub struct Pipeline {
    function_passes: Vec<Box<dyn FunctionPass>>,
    print_passes: bool,
}
impl Pipeline {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn optimizing(env: &mut Environment) -> Self {
        let mut pipeline = Self::new();
        pipeline.add_function_pass(Box::new(Mem2Reg::new(env)));
        pipeline
    }

    pub fn add_function_pass(&mut self, pass: Box<dyn FunctionPass>) {
        self.function_passes.push(pass);
    }

    pub fn enable_print_passes(&mut self) {
        self.print_passes = true;
    }

    pub fn optimize_module(&self, env: &mut Environment, module: ModuleId) {
        for i in 0..env[module].functions().len() {
            let Some(mut ir) = env.modules[module.idx()].functions[i].ir.take() else {
                continue;
            };
            if self.print_passes {
                for _ in 0..env[module].functions[i].name.len() {
                    eprint!("-");
                }
                ceprintln!(
                    "-----------------------------\n\
                    IR for #r<{}> before optimizations:\n{}",
                    env[module].functions[i].name,
                    crate::display::BodyDisplay {
                        env,
                        types: &env[module].functions[i].types,
                        ir: &ir,
                    }
                );
            }

            for pass in &self.function_passes {
                ir = pass.run(env, &env[module].functions[i].types, ir);
                if self.print_passes {
                    eprintln!(
                        "after {pass:?}:\n{}",
                        crate::display::BodyDisplay {
                            env,
                            types: &env[module].functions[i].types,
                            ir: &ir,
                        }
                    );
                }
            }
            env.modules[module.idx()].functions[i].ir = Some(ir);
        }
    }
}
