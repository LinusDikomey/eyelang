mod dead_code_elimination;
mod mem2reg;

pub use dead_code_elimination::DeadCodeElimination;
pub use mem2reg::Mem2Reg;

use crate::{Environment, pipeline::Pipeline};

pub fn optimizing_pipeline(env: &mut Environment) -> Pipeline {
    let mut pipeline = Pipeline::new("optimize");
    pipeline.add_function_pass(Box::new(Mem2Reg::new(env)));
    pipeline.add_function_pass(Box::new(DeadCodeElimination));
    pipeline
}
