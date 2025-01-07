use dmap::DHashMap;

use crate::{
    Argument, BlockId, Builtin, Environment, FunctionIr, Inst, Instruction, Parameter, Ref, TypeId,
    TypedInstruction, INLINE_ARGS,
};

pub struct IrModify {
    ir: FunctionIr,
    additional: Vec<AdditionalInst>,
}
impl IrModify {
    pub fn new(ir: FunctionIr) -> Self {
        Self {
            ir,
            additional: Vec::new(),
        }
    }

    pub fn inst_count(&self) -> u32 {
        (self.ir.insts.len() + self.additional.len()) as _
    }

    pub fn block_ids(&self) -> impl Iterator<Item = BlockId> {
        self.ir.block_ids()
    }

    pub fn args<'a>(
        &'a self,
        inst: &'a Instruction,
        env: &'a Environment,
    ) -> impl Iterator<Item = Argument<'a>> + use<'a> {
        self.ir.args(inst, env)
    }

    pub fn args_n<'a, I: Inst + 'static, const N: usize>(
        &'a self,
        inst: &'a TypedInstruction<I>,
    ) -> [Argument<'a>; N] {
        self.ir.args_n(inst)
    }

    pub fn get_inst(&self, r: Ref) -> &Instruction {
        let i = r.0 as usize;
        if i < self.ir.insts.len() {
            &self.ir.insts[i]
        } else {
            &self.additional[i - self.ir.insts.len()].inst
        }
    }

    pub fn add_block_arg(&mut self, env: &Environment, block: BlockId, ty: TypeId) -> Ref {
        let r = Ref((self.ir.insts.len() + self.additional.len()) as u32);
        let block_info = &mut self.ir.blocks[block.idx()];
        let before = Ref(block_info.idx + block_info.arg_count);
        let prev_arg_count = block_info.arg_count;
        block_info.arg_count += 1;
        self.additional.push(AdditionalInst {
            before,
            inst: crate::builtins::block_arg_inst(ty),
        });
        for pred in &self.ir.blocks[block.idx()].preds {
            let pred_info = &self.ir.blocks[pred.idx()];
            let terminator_idx = pred_info.idx + pred_info.arg_count + pred_info.len - 1;
            let terminator = &mut self.ir.insts[terminator_idx as usize];
            let func = &env[terminator.function];
            let param_count: usize = func.params.iter().map(|p| p.slot_count()).sum();
            let visit_block_target =
                |target_block: BlockId, extra_idx: u32, extra: &mut Vec<u32>| -> u32 {
                    if target_block != block {
                        return extra_idx;
                    }
                    let i = extra_idx as usize;
                    let new_idx = if extra.len() != i + prev_arg_count as usize {
                        let new_idx = extra.len() as u32;
                        // if the old args aren't already at the end of extra, copy them to the end so we
                        // can add an arg
                        extra.extend_from_within(i..i + prev_arg_count as usize);
                        new_idx
                    } else {
                        extra_idx
                    };
                    extra.push(Ref::UNIT.0);
                    new_idx
                };
            if param_count <= INLINE_ARGS && !func.varargs {
                let mut idx = 0;
                for param in &func.params {
                    if *param == Parameter::BlockTarget {
                        terminator.args[idx + 1] = visit_block_target(
                            BlockId(terminator.args[idx]),
                            terminator.args[idx + 1],
                            &mut self.ir.extra,
                        );
                    }
                    idx += param.slot_count();
                }
            } else {
                let mut idx = terminator.args[0] as usize;
                for param in &func.params {
                    if *param == Parameter::BlockTarget {
                        self.ir.extra[idx + 1] = visit_block_target(
                            BlockId(self.ir.extra[idx]),
                            self.ir.extra[idx + 1],
                            &mut self.ir.extra,
                        );
                    }
                    idx += param.slot_count();
                }
            }
        }
        r
    }

    pub fn finish_and_compress(self, env: &Environment) -> FunctionIr {
        if self.additional.is_empty() {
            return self.ir;
        }
        let Self {
            mut ir,
            mut additional,
        } = self;
        additional.sort_by_key(|add| add.before.0);
        let inst_count = ir.insts.len() + additional.len();
        let mut renames: Box<[Ref]> = (0..inst_count as u32).map(Ref).collect();
        let mut insts = Vec::with_capacity(inst_count);
        let new_refs = (ir.insts.len() as u32..).map(Ref);
        let mut old_insts = ir.insts.into_iter();
        let mut new_insts = additional.into_iter().zip(new_refs).peekable();

        let mut block_start_indices: DHashMap<u32, BlockId> = ir
            .blocks
            .iter()
            .map(|info| info.idx)
            .zip((0..).map(BlockId))
            .collect();
        dbg!(&block_start_indices);
        debug_assert_eq!(
            block_start_indices.len(),
            ir.blocks.len(),
            "blocks start at the same idx"
        );

        let mut current = Ref(0);
        let mut current_block = BlockId(u32::MAX);
        loop {
            let Some((r, inst, before_idx)) = new_insts
                .next_if(|(add, _)| add.before == current)
                .map(|(add, r)| (r, add.inst, add.before))
                .or_else(|| {
                    old_insts.next().map(|inst| {
                        let r = current;
                        current.0 += 1;
                        (r, inst, r)
                    })
                })
            else {
                break;
            };
            if let Some(block) = block_start_indices.remove(&before_idx.0) {
                let info = &mut ir.blocks[block.idx()];
                current_block = block;
                info.idx = insts.len() as u32;
                eprintln!("{} with {} args at {}", block, info.arg_count, info.idx);
            }
            if inst
                .as_module(crate::BUILTIN)
                .is_some_and(|inst| inst.op() == Builtin::Nothing)
            {
                renames[r.idx()] = Ref::UNIT;
                ir.blocks[current_block.idx()].len -= 1;
                continue;
            }
            let new_r = Ref(insts.len() as _);
            renames[r.idx()] = new_r;
            insts.push(inst);
        }

        let renamed = |r: Ref| if r.is_ref() { renames[r.idx()] } else { r };

        for inst in &mut insts {
            let func = &env[inst.function];
            let slot_count: usize = func.params().iter().map(|p| p.slot_count()).sum();
            if slot_count > INLINE_ARGS || func.varargs() {
                let mut idx = inst.args[0] as usize;
                let mut visit_param = |param| match param {
                    Parameter::Ref | Parameter::RefOf(_) => {
                        ir.extra[idx] = renamed(Ref(ir.extra[idx])).0;
                        idx += 1;
                    }
                    Parameter::BlockTarget => {
                        let target = BlockId(ir.extra[idx]);
                        let arg_idx = ir.extra[idx + 1];
                        idx += 2;
                        let arg_count = ir.blocks[target.idx()].arg_count;
                        for i in arg_idx..arg_idx + arg_count {
                            ir.extra[i as usize] = renamed(Ref(ir.extra[i as usize])).0;
                        }
                    }
                    Parameter::Int
                    | Parameter::Float
                    | Parameter::Int32
                    | Parameter::TypeId
                    | Parameter::FunctionId
                    | Parameter::GlobalId => idx += param.slot_count(),
                };
                for &param in func.params() {
                    visit_param(param);
                }
                if func.varargs {
                    for _ in 0..inst.args[1] {
                        visit_param(Parameter::Ref);
                    }
                }
            } else {
                let mut idx = 0;
                for param in func.params() {
                    match param {
                        Parameter::Ref | Parameter::RefOf(_) => {
                            inst.args[idx] = renamed(Ref(inst.args[idx])).0;
                            idx += 1;
                        }
                        Parameter::BlockTarget => {
                            let target = BlockId(inst.args[idx]);
                            let args_idx = inst.args[idx + 1];
                            idx += 2;
                            let arg_count = ir.blocks[target.idx()].arg_count;
                            for i in args_idx..args_idx + arg_count {
                                ir.extra[i as usize] = renamed(Ref(ir.extra[i as usize])).0;
                            }
                        }
                        Parameter::Int
                        | Parameter::Float
                        | Parameter::Int32
                        | Parameter::TypeId
                        | Parameter::FunctionId
                        | Parameter::GlobalId => idx += param.slot_count(),
                    }
                }
            }
        }

        ir.insts = insts;
        ir
    }
}

struct AdditionalInst {
    before: Ref,
    inst: Instruction,
}
