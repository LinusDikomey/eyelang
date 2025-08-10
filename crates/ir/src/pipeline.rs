use crate::{Environment, FunctionIr, ModuleId, Types};

pub trait FunctionPass<State = ()>: std::fmt::Debug {
    fn run(
        &self,
        env: &Environment,
        types: &Types,
        ir: FunctionIr,
        name: &str,
        state: &mut State,
    ) -> (FunctionIr, Option<Types>);
}

#[derive(Default)]
pub struct Pipeline<State = ()> {
    pub context: &'static str,
    function_passes: Vec<Box<dyn FunctionPass<State>>>,
}
impl<State> Pipeline<State> {
    pub fn new(context: &'static str) -> Self {
        Self {
            context,
            function_passes: Vec::new(),
        }
    }

    pub fn add_function_pass(&mut self, pass: Box<dyn FunctionPass<State>>) {
        self.function_passes.push(pass);
    }
}

impl<State: Default> Pipeline<State> {
    pub fn process_module(&self, env: &mut Environment, module: ModuleId) {
        self.process_module_with_regs::<crate::mc::UnknownRegister>(env, module);
    }

    pub fn process_module_with_regs<R: crate::mc::Register>(
        &self,
        env: &mut Environment,
        module: ModuleId,
    ) {
        for i in 0..env[module].functions().len() {
            let Some(mut ir) = env.modules[module.idx()].functions[i].ir.take() else {
                continue;
            };
            tracing::debug!(
                target: "passes",
                stage = self.context,
                function = env[module].functions[i].name,
                "IR for {} before:\n{}",
                env[module].functions[i].name,
                ir.display_with_phys_regs::<R>(env, &env[module].functions[i].types),
            );

            let mut state = State::default();

            for pass in &self.function_passes {
                let types;
                let func = &env[module].functions[i];
                (ir, types) = pass.run(env, &func.types, ir, &func.name, &mut state);
                if let Some(types) = types {
                    env.modules[module.idx()].functions[i].types = types;
                }
                tracing::debug!(
                    target: "passes",
                    function = env[module].functions[i].name,
                    pass = ?pass,
                    "After {pass:?}:\n{}",
                    ir.display(env, &env[module].functions[i].types),
                );
            }
            tracing::debug!(target: "passes", function = env[module].functions[i].name, "Done optimizing");
            env.modules[module.idx()].functions[i].ir = Some(ir);
        }
    }

    pub fn process_function(
        &self,
        env: &mut Environment,
        ir: FunctionIr,
        types: &mut Types,
        name: &str,
    ) -> FunctionIr {
        self.process_function_with_regs::<crate::mc::UnknownRegister>(env, ir, types, name)
    }

    pub fn process_function_with_regs<R: crate::mc::Register>(
        &self,
        env: &mut Environment,
        mut ir: FunctionIr,
        types: &mut Types,
        name: &str,
    ) -> FunctionIr {
        tracing::debug!(target: "passes", function = name, "IR before {}:\n{}", self.context, ir.display_with_phys_regs::<R>(env, types));

        let mut state = State::default();
        for pass in &self.function_passes {
            let new_types;
            (ir, new_types) = pass.run(env, types, ir, name, &mut state);
            if let Some(new_types) = new_types {
                *types = new_types;
            }
            tracing::debug!(target: "passes", pass=?pass, function = name, "After {pass:?}:\n{}", ir.display_with_phys_regs::<R>(env, types));
        }
        ir
    }
}
