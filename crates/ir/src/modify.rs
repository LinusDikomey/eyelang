use dmap::DHashMap;

use crate::{
    Argument, BlockId, BlockInfo, Builtin, Environment, FunctionId, FunctionIr, INLINE_ARGS, Inst,
    Instruction, IntoArgs, MCReg, Parameter, Ref, Refs, TypeId, TypedInstruction,
    builder::write_args, mc::RegClass,
};

pub struct IrModify {
    pub(crate) ir: FunctionIr,
    additional: Vec<AdditionalInst>,
    renames: DHashMap<Ref, Ref>,
}
impl IrModify {
    pub fn new(ir: FunctionIr) -> Self {
        Self {
            ir,
            additional: Vec::new(),
            renames: dmap::new(),
        }
    }

    pub fn inst_count(&self) -> u32 {
        (self.ir.insts.len() + self.additional.len()) as _
    }

    pub fn refs(&self) -> impl use<> + ExactSizeIterator<Item = Ref> {
        self.ir.refs()
    }

    pub fn block_ids(&self) -> impl ExactSizeIterator<Item = BlockId> + use<> {
        self.ir.block_ids()
    }

    pub fn get_ref_ty(&self, r: Ref) -> TypeId {
        if r.idx() < self.ir.insts.len() {
            self.ir.insts[r.idx()].ty
        } else {
            self.additional[r.idx() - self.ir.insts.len()].inst.ty
        }
    }

    pub fn args<'a>(
        &'a self,
        inst: &'a Instruction,
        env: &'a Environment,
    ) -> impl Iterator<Item = Argument<'a>> + use<'a> {
        self.ir.args_iter(inst, env)
    }

    pub fn args_n<'a, I: Inst + 'static, const N: usize>(
        &'a self,
        inst: &'a TypedInstruction<I>,
    ) -> [Argument<'a>; N] {
        self.ir.args_n(inst)
    }

    pub(crate) fn try_get_inst(&self, r: Ref) -> Result<&Instruction, ()> {
        debug_assert!(
            r.is_ref(),
            "Tried to get an instruction from a Ref value: {r}"
        );
        let r = self.renames.get(&r).copied().unwrap_or(r);
        if !r.is_ref() {
            return Err(());
        }
        let i = r.0 as usize;
        Ok(if i < self.ir.insts.len() {
            &self.ir.insts[i]
        } else {
            &self.additional[i - self.ir.insts.len()].inst
        })
    }

    pub fn get_inst(&self, r: Ref) -> &Instruction {
        self.try_get_inst(r)
            .expect("Retrieved instruction was deleted")
    }

    pub fn visit_block_targets_mut(
        &mut self,
        inst: Ref,
        env: &Environment,
        mut f: impl FnMut(BlockId, &mut [Ref]),
    ) {
        let inst = if (inst.0 as usize) < self.ir.insts.len() {
            self.ir.insts[inst.idx()]
        } else {
            self.ir.insts[inst.idx() - self.ir.insts.len()]
        };
        let params = env[inst.function].params();
        let slot_count: usize = params.iter().map(|p| p.slot_count()).sum();
        if slot_count <= INLINE_ARGS {
            let mut idx = 0;
            for param in params {
                if *param == Parameter::BlockTarget {
                    let block = BlockId(inst.args[idx]);
                    let args_idx = inst.args[idx + 1] as usize;
                    let arg_count = self.ir.blocks[block.idx()].arg_count as usize;
                    let args: &mut [u32] = &mut self.ir.extra[args_idx..args_idx + arg_count];
                    // SAFETY: reinterprets the u32s as Refs, Refs are repr(transparent)
                    let args: &mut [Ref] = unsafe {
                        std::slice::from_raw_parts_mut(args.as_mut_ptr().cast(), args.len())
                    };
                    f(block, args)
                }
                idx += param.slot_count();
            }
        } else {
            let mut idx = inst.args[0] as usize;
            for param in params {
                if *param == Parameter::BlockTarget {
                    let block = BlockId(self.ir.extra[idx]);
                    let args_idx = self.ir.extra[idx + 1] as usize;
                    let arg_count = self.ir.blocks[block.idx()].arg_count as usize;
                    let args: &mut [u32] = &mut self.ir.extra[args_idx..args_idx + arg_count];
                    // SAFETY: reinterprets the u32s as Refs, Refs are repr(transparent)
                    let args: &mut [Ref] = unsafe {
                        std::slice::from_raw_parts_mut(args.as_mut_ptr().cast(), args.len())
                    };
                    f(block, args)
                }
                idx += param.slot_count();
            }
        }
    }

    /// adds a block argument of the specified type to the block and returns the Ref to the new arg
    /// as well as it's index in the arg list of that block
    pub fn add_block_arg(&mut self, env: &Environment, block: BlockId, ty: TypeId) -> (Ref, u32) {
        let r = Ref((self.ir.insts.len() + self.additional.len()) as u32);
        let block_info = &mut self.ir.blocks[block.idx()];
        let before = Ref(block_info.idx); // before the first instruction of the body block
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
            if param_count <= INLINE_ARGS && func.varargs.is_none() {
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
        (r, prev_arg_count)
    }

    pub fn add_before<'r>(
        &mut self,
        env: &Environment,
        r: Ref,
        (function, args, ty): (FunctionId, impl IntoArgs<'r>, TypeId),
    ) -> Ref {
        let before = if r.idx() < self.ir.insts.len() {
            r
        } else {
            todo!("add before added insts");
        };
        let def = &env[function];
        debug_assert!(
            !def.flags.terminator(),
            "can't add a terminator before another instruction"
        );
        // PERF: iterating blocks every time is bad, somehow avoid this
        let block = BlockId(
            self.ir
                .blocks
                .iter()
                .position(|info| {
                    let i = info.idx + info.arg_count;
                    (i..i + info.len).contains(&r.0)
                })
                .expect("no block found") as _,
        );
        let args = write_args(
            &mut self.ir.extra,
            block,
            &mut self.ir.blocks,
            &def.params,
            def.varargs,
            args,
        );
        let r = Ref((self.ir.insts.len() + self.additional.len())
            .try_into()
            .expect("too many instructions"));
        self.additional.push(AdditionalInst {
            before,
            inst: Instruction { function, args, ty },
        });
        r
    }

    pub fn add_after<'r>(
        &mut self,
        env: &Environment,
        r: Ref,
        inst: (FunctionId, impl IntoArgs<'r>, TypeId),
    ) -> Ref {
        let i = r
            .into_ref()
            .expect("Can't add an instruction after a value Ref");
        self.add_before(env, Ref::index(i + 1), inst)
    }

    pub fn finish_and_compress(self, env: &Environment) -> FunctionIr {
        let Self {
            mut ir,
            additional,
            renames: rename_map,
        } = self;
        if additional.is_empty() && rename_map.is_empty() {
            return ir;
        }
        let inst_count = ir.insts.len() + additional.len();
        let mut insts = Vec::with_capacity(inst_count);
        let new_refs = (ir.insts.len() as u32..).map(Ref);
        let mut old_insts = ir.insts.into_iter();
        let mut new_insts: Vec<_> = additional.into_iter().zip(new_refs).collect();
        new_insts.sort_by_key(|(inst, _r)| inst.before.0);
        let mut new_insts = new_insts.into_iter().peekable();

        let mut block_start_indices: DHashMap<u32, BlockId> = ir
            .blocks
            .iter()
            .map(|info| info.idx)
            .zip((0..).map(BlockId))
            .collect();
        debug_assert_eq!(
            block_start_indices.len(),
            ir.blocks.len(),
            "blocks start at the same idx"
        );

        let mut renames: Box<[Ref]> = (0..inst_count as u32).map(Ref).collect();

        let mut current = Ref(0);
        let mut current_block = BlockId(u32::MAX);
        loop {
            let mut is_new = false;
            let Some((r, inst, before_idx)) = new_insts
                .next_if(|(add, _)| add.before == current)
                .map(|(add, r)| {
                    is_new = true;
                    (r, add.inst, add.before)
                })
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
                tracing::debug!(target: "compress", "Starting block {block} at {}, info: {info:?}", insts.len());
            }
            if inst
                .as_module(crate::BUILTIN)
                .is_some_and(|inst| inst.op() == Builtin::Nothing)
            {
                renames[r.idx()] = Ref::UNIT;
                ir.blocks[current_block.idx()].len -= 1;
                continue;
            }
            if is_new
                && !inst
                    .as_module(crate::BUILTIN)
                    .is_some_and(|inst| inst.op() == Builtin::BlockArg)
            {
                ir.blocks[current_block.idx()].len += 1;
            }
            let new_r = Ref(insts.len() as _);
            renames[r.idx()] = new_r;
            tracing::debug!(target: "compress", "Renamed due to new position {r} -> {new_r}");
            insts.push(inst);
        }

        let renamed = |r: Ref| {
            let r = rename_map.get(&r).copied().unwrap_or(r);
            if r.is_ref() { renames[r.idx()] } else { r }
        };

        for inst in &mut insts {
            let func = &env[inst.function];
            let slot_count: usize = func.params().iter().map(|p| p.slot_count()).sum();
            if slot_count > INLINE_ARGS || func.varargs().is_some() {
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
                    Parameter::BlockId
                    | Parameter::Int
                    | Parameter::Float
                    | Parameter::Int32
                    | Parameter::TypeId
                    | Parameter::FunctionId
                    | Parameter::GlobalId
                    | Parameter::MCReg(_) => idx += param.slot_count(),
                };
                for &param in func.params() {
                    visit_param(param);
                }
                if let Some(param) = func.varargs {
                    for _ in 0..inst.args[1] {
                        visit_param(param);
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
                        Parameter::BlockId
                        | Parameter::Int
                        | Parameter::Float
                        | Parameter::Int32
                        | Parameter::TypeId
                        | Parameter::FunctionId
                        | Parameter::GlobalId
                        | Parameter::MCReg(_) => idx += param.slot_count(),
                    }
                }
            }
        }

        ir.insts = insts;
        ir
    }

    pub fn new_reg(&mut self, class: RegClass) -> MCReg {
        self.ir.new_reg(class)
    }

    pub fn replace_with(&mut self, r: Ref, new: Ref) {
        self.renames.insert(r, new);
        let inst = if (r.0 as usize) < self.ir.insts.len() {
            &mut self.ir.insts[r.0 as usize]
        } else {
            &mut self.additional[r.0 as usize - self.ir.insts.len()].inst
        };
        inst.function = FunctionId {
            module: crate::ModuleId::BUILTINS,
            function: Builtin::Nothing.id(),
        };
    }

    pub fn replace<'r>(
        &mut self,
        env: &Environment,
        r: Ref,
        (function, args, ty): (FunctionId, impl IntoArgs<'r>, TypeId),
    ) {
        // PERF: iterating blocks every time is bad, somehow avoid this
        let block = BlockId(
            self.ir
                .blocks
                .iter()
                .position(|info| {
                    let i = info.idx + info.arg_count;
                    (i..i + info.len).contains(&r.0)
                })
                .expect("no block found") as _,
        );
        let def = &env[function];
        let args = write_args(
            &mut self.ir.extra,
            block,
            &mut self.ir.blocks,
            &def.params,
            def.varargs,
            args,
        );
        self.replace_with_inst(r, Instruction { function, args, ty });
    }

    pub fn replace_with_inst(&mut self, r: Ref, new_inst: Instruction) {
        if r.idx() < self.ir.insts.len() {
            self.ir.insts[r.idx()] = new_inst;
        } else {
            self.additional[r.idx() - self.ir.insts.len()].inst = new_inst;
        }
    }

    pub fn get_block(&self, block: BlockId) -> &BlockInfo {
        &self.ir.blocks[block.idx()]
    }

    /// Gets the Ref to the first instruction in the given block before potential modifications.
    pub fn get_original_block_start(&self, block: BlockId) -> Ref {
        let info = &self.ir.blocks[block.idx()];
        Ref(info.idx + info.arg_count)
    }

    pub fn get_block_args(&self, block: BlockId) -> Refs {
        // FIXME: this is incorrect since block args can be changed
        self.ir.get_block_args(block)
    }

    pub fn prepare_instruction<'a, A: crate::IntoArgs<'a>>(
        &mut self,
        params: &[Parameter],
        varargs: Option<Parameter>,
        block: BlockId,
        arg: (FunctionId, A, TypeId),
    ) -> Instruction {
        self.ir.prepare_instruction(params, varargs, block, arg)
    }

    pub fn args_iter<'a>(
        &'a self,
        inst: &'a Instruction,
        env: &'a Environment,
    ) -> crate::ArgsIter<'a> {
        self.ir.args_iter(inst, env)
    }
}

#[derive(Debug)]
struct AdditionalInst {
    before: Ref,
    inst: Instruction,
}
