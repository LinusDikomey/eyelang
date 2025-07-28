mod mem2reg;

pub use mem2reg::Mem2Reg;

use crate::{Environment, pipeline::Pipeline};

pub fn optimizing_pipeline(env: &mut Environment) -> Pipeline {
    let mut pipeline = Pipeline::new("optimize");
    pipeline.add_function_pass(Box::new(Mem2Reg::new(env)));
    pipeline
}
