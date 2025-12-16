use dmap::{DHashMap, DHashSet};

use crate::{
    Argument, Bitmap, BlockGraph, BlockId, BlockInfo, BlockTarget, Builtin, Environment,
    FunctionId, FunctionIr, INLINE_ARGS, Inst, Instruction, IntoArgs, MCReg, Parameter, Ref, Refs,
    TypeId, TypedInstruction, argument, builder::write_args, decode_args, dialect::Cf,
    mc::RegClass,
};

pub struct IrModify {
    pub(crate) ir: FunctionIr,
    additional: Vec<AdditionalInst>,
    pub renames: DHashMap<Ref, Ref>,
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

    pub fn renames(&self) -> &DHashMap<Ref, Ref> {
        &self.renames
    }

    pub fn get_ref_ty(&self, r: Ref) -> TypeId {
        match r {
            Ref::UNIT => TypeId::I1,
            Ref::TRUE | Ref::FALSE => TypeId::I1,
            _ => {
                if r.idx() < self.ir.insts.len() {
                    self.ir.insts[r.idx()].ty
                } else {
                    self.additional[r.idx() - self.ir.insts.len()].inst.ty
                }
            }
        }
    }

    pub fn args<'a, A: argument::Args<'a>>(
        &'a self,
        inst: &'a Instruction,
        env: &'a Environment,
    ) -> A {
        self.ir.args(inst, env)
    }

    pub fn typed_args<'a, A: argument::Args<'a>, I: Inst>(
        &'a self,
        inst: &'a TypedInstruction<I>,
    ) -> A {
        self.ir.typed_args(inst)
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
        let before = Ref(block_info.args_idx); // before the first instruction of the body block
        let prev_arg_count = block_info.arg_count;
        block_info.arg_count += 1;
        self.additional.push(AdditionalInst {
            before,
            inst: crate::builtins::block_arg_inst(ty),
        });
        for pred in &self.ir.blocks[block.idx()].preds {
            let pred_info = &self.ir.blocks[pred.idx()];
            let terminator_idx = pred_info.body_idx + pred_info.len - 1;
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
        let before_old = r.idx() < self.ir.insts.len();
        let before = if before_old {
            r
        } else {
            self.additional[r.idx() - self.ir.insts.len()].before
        };
        let def = &env[function];
        debug_assert!(
            !def.flags.terminator() || !before_old,
            "can't add a terminator before another instruction"
        );
        // PERF: iterating blocks every time is bad, somehow avoid this
        let block = BlockId(
            self.ir
                .blocks
                .iter()
                .position(|info| {
                    if info.body_idx < self.ir.insts.len() as _ {
                        let i = info.body_idx;
                        (i..i + info.len).contains(&r.0)
                    } else {
                        info.body_idx == before.0
                    }
                })
                .unwrap_or_else(|| panic!("no block found for instruction {r}")) as _,
        );
        let args = write_args(
            &mut self.ir.extra,
            block,
            &mut self.ir.blocks,
            &def.params,
            def.varargs,
            args,
        );
        self.add_inst_before(before, Instruction { function, args, ty })
    }

    pub fn add_inst_before(&mut self, before: Ref, inst: Instruction) -> Ref {
        let r = Ref((self.ir.insts.len() + self.additional.len())
            .try_into()
            .expect("too many instructions"));
        self.additional.push(AdditionalInst { before, inst });
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
        let cf = env.get_dialect_module_if_present::<Cf>();
        let Self {
            mut ir,
            additional,
            renames: rename_map,
        } = self;
        if additional.is_empty() && rename_map.is_empty() {
            return ir;
        }

        let block_graph = BlockGraph::calculate(&ir, env);

        let inst_count = ir.insts.len() + additional.len();
        // TODO: IrModify could keep track of number of deleted instructions sot that we can always
        // preallocate perfectly here. Also could know if the ir should still be compressed with no
        // renames/additional instructions
        let mut insts = Vec::with_capacity(inst_count);
        let new_refs = (ir.insts.len() as u32..).map(Ref);
        let old_insts = ir.insts;
        let mut new_insts: Vec<_> = additional.into_iter().zip(new_refs).collect();
        new_insts.sort_by_key(|(inst, _r)| inst.before.0);

        let mut renames: Box<[Ref]> = (0..inst_count as u32).map(Ref).collect();

        let mut visited_blocks = Bitmap::new(ir.blocks.len());
        let mut removed_blocks = DHashSet::default();

        for &current_block in block_graph.postorder().iter().rev() {
            if visited_blocks.get(current_block.idx()) {
                continue;
            }

            let mut arg_renames: Option<std::vec::IntoIter<Ref>> = None;
            let mut appending_block = None;

            let mut current_block = current_block;
            'add_block_contents: loop {
                visited_blocks.set(current_block.idx(), true);
                let info = &mut ir.blocks[current_block.idx()];
                let mut new_idx = match new_insts
                    .binary_search_by_key(&info.args_idx, |(add, _)| add.before.0)
                {
                    Ok(mut new_idx) => {
                        while new_idx > 0 && new_insts[new_idx - 1].0.before.0 == info.args_idx {
                            new_idx -= 1;
                        }
                        new_idx
                    }
                    Err(i) => i,
                };

                // check if block was added after and all insts will be in additional
                let is_new_block = info.args_idx >= old_insts.len() as _;
                let inst_range = if is_new_block {
                    info.args_idx..info.args_idx + 1
                } else {
                    info.args_idx..info.body_idx + info.len
                }
                .map(Ref);
                info.args_idx = insts.len() as u32;
                info.body_idx = info.args_idx + info.arg_count;
                for current in inst_range {
                    'before: while let Some((inst, r)) = new_insts.get(new_idx)
                        && inst.before == current
                    {
                        debug_assert!(
                            !inst
                                .inst
                                .as_module(crate::BUILTIN)
                                .is_some_and(|inst| inst.op() == Builtin::Nothing),
                            "Nothing in additional shouldn't happen"
                        );
                        new_idx += 1;
                        if inst
                            .inst
                            .as_module(crate::BUILTIN)
                            .is_some_and(|inst| inst.op() == Builtin::BlockArg)
                        {
                            if let Some(renamed) =
                                arg_renames.as_mut().and_then(|renames| renames.next())
                            {
                                renames[r.idx()] = renamed;
                                continue 'before;
                            }
                        } else {
                            ir.blocks[appending_block.unwrap_or(current_block).idx()].len += 1;
                        }
                        let new_r = Ref(insts.len() as _);
                        renames[r.idx()] = new_r;
                        insts.push(inst.inst);
                    }

                    if is_new_block {
                        // there can we no instructions in the old because the block is new
                        continue;
                    }
                    let inst = &old_insts[current.idx()];
                    if inst
                        .as_module(crate::BUILTIN)
                        .is_some_and(|inst| inst.op() == Builtin::Nothing)
                    {
                        renames[current.idx()] = Ref::UNIT;
                        if appending_block.is_none() {
                            ir.blocks[current_block.idx()].len -= 1;
                        }
                        continue;
                    } else if let Some(cf) = cf
                        && let Some(cf_inst) = inst.as_module(cf)
                        && cf_inst.op() == Cf::Goto
                    {
                        let params = cf_inst.inst.params();
                        let varargs = cf_inst.inst.varargs();
                        let mut args_iter =
                            decode_args(&inst.args, params, varargs, &ir.blocks, &ir.extra);
                        let Some(Argument::BlockTarget(BlockTarget(target, args))) =
                            args_iter.next()
                        else {
                            unreachable!()
                        };
                        debug_assert!(args_iter.next().is_none());
                        let target_info = &mut ir.blocks[target.idx()];
                        let compress_trivial_gotos = false;
                        if compress_trivial_gotos && target_info.preds.len() == 1 {
                            // Goto whose target has only a single predecessor:
                            // combine into one block
                            debug_assert_eq!(current_block, *target_info.preds.first().unwrap());
                            debug_assert_eq!(args.len(), target_info.arg_count as usize);
                            debug_assert!(!visited_blocks.get(target.idx()), "RPO is wrong");

                            // successors of the next block become successors of the current block
                            let succs = std::mem::take(&mut target_info.succs);
                            let appending = appending_block.unwrap_or(current_block);
                            let info = &mut ir.blocks[appending.idx()];
                            debug_assert_eq!(info.succs.len(), 1);
                            debug_assert_eq!(info.succs[0], target);
                            info.succs = succs;

                            removed_blocks.insert(target);

                            // trivial goto is removed
                            ir.blocks[appending_block.unwrap_or(current_block).idx()].len -= 1;

                            // continue appending the successor to the current block
                            arg_renames = Some(args.into_owned().into_iter());
                            if appending_block.is_none() {
                                appending_block = Some(current_block);
                            }
                            current_block = target;
                            continue 'add_block_contents;
                        }
                    }
                    let new_r = Ref(insts.len() as _);
                    renames[current.idx()] = new_r;
                    if let Some(appending) = appending_block {
                        ir.blocks[appending.idx()].len += 1;
                    }
                    insts.push(*inst);
                }
                break 'add_block_contents;
            }
        }
        visited_blocks.visit_unset_bits(|i| {
            removed_blocks.insert(BlockId(i as _));
        });

        let renamed = |r: Ref| {
            let r = rename_map.get(&r).copied().unwrap_or(r);
            if r.is_ref() { renames[r.idx()] } else { r }
        };

        let mut renamed_blocks = DHashMap::default();
        for &removed in &removed_blocks {
            while removed_blocks.contains(&BlockId(ir.blocks.len() as u32 - 1)) {
                ir.blocks.pop();
                continue;
            }
            if removed.idx() >= ir.blocks.len() {
                continue;
            }
            ir.blocks.swap_remove(removed.idx());
            renamed_blocks.insert(BlockId(ir.blocks.len() as u32), removed);
        }

        for inst in &mut insts {
            crate::update_inst_refs(inst, env, &mut ir.extra, &ir.blocks, renamed, |block| {
                renamed_blocks.get(&block).copied().unwrap_or(block)
            });
        }
        if !renamed_blocks.is_empty() {
            for block in &mut ir.blocks {
                for b in block.succs.iter_mut().chain(block.preds.iter_mut()) {
                    *b = renamed_blocks.get(b).copied().unwrap_or(*b);
                }
            }
        }

        ir.insts = insts;
        ir
    }

    pub fn new_reg(&mut self, class: RegClass) -> MCReg {
        self.ir.new_reg(class)
    }

    pub fn add_block(&mut self, args: impl IntoIterator<Item = TypeId>) -> (BlockId, Refs, Ref) {
        let id = BlockId(self.ir.blocks.len() as _);
        let insert_idx = (self.ir.insts.len() + self.additional.len()) as u32;
        self.additional
            .extend(args.into_iter().map(|arg_ty| AdditionalInst {
                // add all arguments "before" the first one so they all get grouped properly
                before: Ref(insert_idx),
                inst: Instruction {
                    function: crate::FunctionId {
                        module: crate::ModuleId::BUILTINS,
                        function: Builtin::BlockArg.id(),
                    },
                    args: [0, 0],
                    ty: arg_ty,
                },
            }));
        let arg_count = (self.ir.insts.len() + self.additional.len()) as u32 - insert_idx;
        self.ir.blocks.push(BlockInfo {
            arg_count,
            args_idx: insert_idx,
            body_idx: insert_idx,
            len: 0,
            preds: Vec::new(),
            succs: Vec::new(),
        });
        let arg_refs = Refs {
            idx: insert_idx,
            count: arg_count,
        };
        (id, arg_refs, Ref(insert_idx))
    }

    pub fn replace_with(&mut self, env: &Environment, r: Ref, new: Ref) {
        let block = self.inst_block(r);
        self.on_inst_remove(env, r, block);
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

    pub fn delete(&mut self, env: &Environment, r: Ref) {
        self.replace_with(env, r, Ref::UNIT);
    }

    pub fn inst_block(&self, r: Ref) -> BlockId {
        let r = if r.idx() < self.ir.insts.len() {
            r
        } else {
            self.additional[r.idx()].before
        };
        // PERF: iterating blocks every time is bad, avoid this maybe with a BTreeMap in IrModify
        BlockId(
            self.ir
                .blocks
                .iter()
                .position(|info| {
                    // FIXME: arg_count does not work as the offset after adding block args
                    (info.args_idx..info.args_idx + info.arg_count + info.len).contains(&r.0)
                })
                .unwrap_or_else(|| panic!("no block found for ref {r}")) as _,
        )
    }

    pub fn replace<'r>(
        &mut self,
        env: &Environment,
        r: Ref,
        (function, args, ty): (FunctionId, impl IntoArgs<'r>, TypeId),
    ) {
        let block = self.inst_block(r);
        let def = &env[function];
        let args = write_args(
            &mut self.ir.extra,
            block,
            &mut self.ir.blocks,
            &def.params,
            def.varargs,
            args,
        );
        self.replace_with_inst(env, r, Instruction { function, args, ty });
    }

    pub fn replace_with_inst(&mut self, env: &Environment, r: Ref, new_inst: Instruction) {
        let block = self.inst_block(r);
        self.on_inst_remove(env, r, block);
        if r.idx() < self.ir.insts.len() {
            self.ir.insts[r.idx()] = new_inst;
        } else {
            self.additional[r.idx() - self.ir.insts.len()].inst = new_inst;
        }
    }

    fn on_inst_remove(&mut self, env: &Environment, r: Ref, block: BlockId) {
        let mut succs = std::mem::take(&mut self.ir.blocks[block.idx()].succs);
        let inst = self.get_inst(r);
        let def = &env[inst.function];
        let args = inst.args_inner(def.params(), def.varargs(), &self.ir.blocks, &self.ir.extra);
        let mut removed = Vec::new();
        for arg in args {
            if let Argument::BlockTarget(BlockTarget(target, _)) = arg {
                let i = succs
                    .iter()
                    .position(|&succ| succ == target)
                    .expect("Successor was not present");
                succs.swap_remove(i);
                removed.push(target);
            }
        }
        debug_assert!(self.ir.blocks[block.idx()].succs.is_empty());
        self.ir.blocks[block.idx()].succs = succs;
        for target in removed {
            let info = &mut self.ir.blocks[target.idx()];
            let i = info
                .preds
                .iter()
                .position(|&pred| pred == block)
                .expect("Predecessor was not present");
            info.preds.swap_remove(i);
        }
    }

    pub fn get_block(&self, block: BlockId) -> &BlockInfo {
        &self.ir.blocks[block.idx()]
    }

    /// Gets the Ref to the first instruction in the given block before potential modifications.
    pub fn get_original_block_start(&self, block: BlockId) -> Ref {
        let info = &self.ir.blocks[block.idx()];
        Ref(info.args_idx + info.arg_count)
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
    ) -> crate::ArgsIter<'a, 'a> {
        self.ir.args_iter(inst, env)
    }

    pub fn split_block_after(&mut self, r: Ref) -> BlockId {
        let block = self
            .ir
            .blocks
            .iter()
            .position(|block| (block.body_idx..block.body_idx + block.len).contains(&r.0))
            .unwrap();
        let info = &mut self.ir.blocks[block];
        let is_end = info.body_idx + info.len == r.0 + 1;
        let split_offset = r.0 - info.body_idx + 1;
        let new_block_len = if is_end {
            0
        } else {
            let old_count = split_offset;
            let new_block_len = info.len - old_count;
            info.len = old_count;
            new_block_len
        };
        let new_block_idx = info.body_idx + split_offset;
        let succs = if is_end {
            Vec::new()
        } else {
            std::mem::take(&mut info.succs)
        };
        let id = BlockId(self.ir.blocks.len() as _);
        self.ir.blocks.push(BlockInfo {
            arg_count: 0,
            args_idx: new_block_idx,
            body_idx: new_block_idx,
            len: new_block_len,
            preds: Vec::new(),
            succs,
        });
        id
    }
}

#[derive(Debug)]
struct AdditionalInst {
    before: Ref,
    inst: Instruction,
}

#[cfg(test)]
mod tests {
    use crate::{BlockId, Environment, Primitive, dialect, modify::IrModify, verify};

    #[test]
    fn add_block_arg() {
        let mut env = Environment::new(Primitive::create_infos());
        env.get_dialect_module::<dialect::Arith>();
        env.get_dialect_module::<dialect::Cf>();
        let src = r#"
            b0:
                %0 = arith.Int 0 :: I32
                     cf.Goto b1
            b1:
                %3 = arith.Int 10 :: I32
                %4 = arith.LT %0 %3 :: I1
                     cf.Branch %4 b2 b3
            b2:
                %7 = arith.Int 1 :: I32
                %8 = arith.Add %0 %7 :: I32
                     cf.Goto b1
            b3:
                     cf.Ret unit
        "#;
        let (function, mut types) = crate::parse::parse_function_body(&env, src);
        verify::function_body(&env, &function, &types);
        let mut ir = IrModify::new(function);
        let i64 = types.add(Primitive::I64);
        let (_, n) = ir.add_block_arg(&env, BlockId(1), i64);
        assert_eq!(n, 0);
        let function = ir.finish_and_compress(&env);
        println!("{}", function.display(&env, &types));
        verify::function_body(&env, &function, &types);
    }
}
