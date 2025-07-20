mod mem2reg;

pub use mem2reg::Mem2Reg;

use crate::{Environment, FunctionIr, ModuleId, Types};

pub trait FunctionPass: std::fmt::Debug {
    fn run(&self, env: &Environment, types: &Types, ir: FunctionIr) -> FunctionIr;
}

#[derive(Default)]
pub struct Pipeline {
    function_passes: Vec<Box<dyn FunctionPass>>,
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

    pub fn optimize_module(&self, env: &mut Environment, module: ModuleId) {
        for i in 0..env[module].functions().len() {
            let Some(mut ir) = env.modules[module.idx()].functions[i].ir.take() else {
                continue;
            };
            tracing::debug!(
                target: "passes",
                function = env[module].functions[i].name,
                "IR for {} before optimizations:\n{}",
                env[module].functions[i].name,
                ir.display(env, &env[module].functions[i].types),
            );

            for pass in &self.function_passes {
                ir = pass.run(env, &env[module].functions[i].types, ir);
                tracing::debug!(
                    target: "passes",
                    function = env[module].functions[i].name,
                    "After {pass:?}:\n{}",
                    ir.display(env, &env[module].functions[i].types),
                );
            }
            tracing::debug!(target: "passes", function = env[module].functions[i].name, "Done optimizing");
            env.modules[module.idx()].functions[i].ir = Some(ir);
        }
    }

    pub fn optimize_function(
        &self,
        env: &mut Environment,
        mut ir: FunctionIr,
        types: &mut Types,
    ) -> FunctionIr {
        tracing::debug!(target: "passes", "IR before optimizations:\n{}", ir.display(env, types));

        for pass in &self.function_passes {
            ir = pass.run(env, types, ir);
            tracing::debug!(target: "passes", "After {pass:?}:\n{}", ir.display(env, types));
        }
        ir
    }
}
