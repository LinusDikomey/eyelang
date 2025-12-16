use dmap::DHashSet;

use crate::{Environment, Function, FunctionIr, ModuleId, Types, mc::UnknownRegister};

pub fn module(env: &Environment, module: ModuleId) {
    for id in env[module].function_ids() {
        function(env, &env[module][id]);
    }
}

pub fn function(env: &Environment, function: &Function) {
    if let Some(body) = function.ir() {
        function_body(env, body, &function.types);
    }
}

pub fn function_body(env: &Environment, body: &FunctionIr, types: &Types) {
    let mut accounted_refs = DHashSet::default();
    for block in body.block_ids() {
        let info = &body.blocks[block.idx()];
        assert_eq!(
            info.args_idx + info.arg_count,
            info.body_idx,
            "Body index of block {block} is desynchronized"
        );
        for r in body.get_block_args(block).iter() {
            accounted_refs.insert(r);
        }
        for (r, _inst) in body.get_block(block) {
            accounted_refs.insert(r);
        }
    }
    for r in body.refs() {
        assert!(
            accounted_refs.contains(&r),
            "Instruction {} is not part of any block",
            body.get_inst(r)
                .display::<UnknownRegister>(r, env, types, body, 0)
        );
    }
}
