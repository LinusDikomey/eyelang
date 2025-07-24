use std::convert::Infallible;

use ir::{
    BlockGraph, BlockId, BlockTarget, Environment, FunctionId, FunctionIr, MCReg, ModuleOf,
    Primitive, Ref, Type, Types,
    mc::{Mc, parallel_copy},
    modify::IrModify,
    rewrite::{ReverseRewriteOrder, Rewrite},
    slots::Slots,
};

use crate::arch::x86::{abi::Abi, isa::Reg};

pub fn codegen(
    env: &Environment,
    body: &ir::FunctionIr,
    types: &ir::Types,
    isel: &mut InstructionSelector,
    mc: ModuleOf<Mc>,
    abi: &'static dyn Abi,
) -> (FunctionIr, ir::Types) {
    /*
    let mut mir = MachineIR::new();
    let mut builder = mir.begin_block(MirBlock::ENTRY);
    let mut values = vec![MCValue::None; body.inst_count() as usize];

    builder.inst(Inst::push64, [Op::Reg(Reg::rbp)]);
    builder.inst(Inst::movrr64, [Op::Reg(Reg::rbp), Op::Reg(Reg::rsp)]);
    // This instruction's immediate operand will be updated at the end with the used stack space.
    // In the future, the stack size might be known a priori when the IR tracks a list of stack
    // slots.
    let stack_setup_indices = vec![builder.next_inst_index()];
    builder.inst(Inst::subri64, [Op::Reg(Reg::rsp), Op::Imm(0)]);
    */

    /*
    let abi = abi::get_function_abi(
        types,
        function.params().iter().map(|p| {
            let Parameter::RefOf(ty) = p else { panic!() };
            ty
        }),
        function.return_type().unwrap(),
        env.primitives(),
    );
    */

    //let (mir_entry_block, entry_block_args) =
    //    builder.create_block(abi.arg_registers().iter().map(|r| r.class()));
    //let (mir_entry_block, entry_block_args) = builder.create_block([]);
    //builder.register_successor(mir_entry_block);
    /*
    builder.build_copyargs(
        Inst::Copyargs,
        entry_block_args.iter().map(|vreg| vreg.op()),
        abi.arg_registers().iter().copied().map(Op::Reg),
    );
    */

    let mut body = body.clone();

    let mut regs = Slots::with_default(&body, types, MCReg::from_virt(0));
    for r in body.refs() {
        _ = regs.visit_primitive_slots_mut::<Infallible, _>(
            r,
            types[body.get_ref_ty(r)],
            types,
            |regs, p| {
                use Primitive as P;
                match p {
                    P::Unit => {}
                    P::I1 | P::I8 | P::U8 => regs[0] = body.new_reg(ir::mc::RegClass::GP8),
                    P::I16 | P::U16 => regs[0] = body.new_reg(ir::mc::RegClass::GP16),
                    P::I32 | P::U32 => regs[0] = body.new_reg(ir::mc::RegClass::GP32),
                    P::I64 | P::U64 | P::Ptr => regs[0] = body.new_reg(ir::mc::RegClass::GP64),
                    P::F32 => regs[0] = body.new_reg(ir::mc::RegClass::F32),
                    P::F64 => regs[0] = body.new_reg(ir::mc::RegClass::F64),
                    _ => todo!(),
                };
                Ok(())
            },
        );
    }
    let mut types = types.clone();
    let block_graph = BlockGraph::calculate(&body, env);
    let mut use_counts = vec![0; body.inst_count() as usize].into_boxed_slice();
    for i in 0..body.inst_count() {
        let inst = body.get_inst(Ref::index(i));
        for arg in body.args_iter(inst, env) {
            match arg {
                ir::Argument::Ref(r) => {
                    if let Some(r) = r.into_ref() {
                        use_counts[r as usize] += 1;
                    }
                }
                ir::Argument::BlockTarget(BlockTarget(_block, args)) => {
                    for r in args {
                        if let Some(r) = r.into_ref() {
                            use_counts[r as usize] += 1;
                        }
                    }
                }
                ir::Argument::BlockId(_)
                | ir::Argument::Int(_)
                | ir::Argument::Float(_)
                | ir::Argument::TypeId(_)
                | ir::Argument::FunctionId(_)
                | ir::Argument::GlobalId(_)
                | ir::Argument::MCReg(_) => {}
            }
        }
    }
    let unit = types.add(Type::Tuple(ir::TypeIds::EMPTY));

    let mut body = IrModify::new(body);
    let args = body.get_block_args(BlockId::ENTRY);
    abi.implement_params(args, &mut body, env, mc, &types, &regs, unit);

    let mut ctx = IselCtx {
        stack_size: 0,
        unit,
        regs,
        mc,
        use_counts,
        abi,
    };

    ir::rewrite::rewrite_in_place(
        &mut body,
        &types,
        env,
        &mut ctx,
        isel,
        ReverseRewriteOrder::new(&block_graph),
    );

    /*
    for idx in stack_setup_indices {
        mir.replace_operand(idx, 1, offset_op(mir.stack_offset() as i32));
    }
    mir
    */
    (body.finish_and_compress(env), types)
}

pub struct IselCtx {
    stack_size: u32,
    unit: ir::TypeId,
    regs: Slots<MCReg>,
    mc: ModuleOf<Mc>,
    use_counts: Box<[u32]>,
    abi: &'static dyn Abi,
}
impl ir::rewrite::RewriteCtx for IselCtx {
    fn begin_block(&mut self, env: &Environment, ir: &mut IrModify, block: BlockId) {
        if block == BlockId::ENTRY {
            return;
        }
        let info = ir.get_block(block);
        let args = self
            .regs
            .get_range(Ref::index(info.idx), Ref::index(info.idx + info.arg_count));
        let f = FunctionId {
            module: self.mc.id(),
            function: Mc::IncomingBlockArgs.id(),
        };
        let start = ir.get_original_block_start(block);
        ir.add_before(env, start, (f, ((), args), self.unit));
    }
}
impl IselCtx {
    fn use_count(&self, r: Ref) -> u32 {
        if let Some(r) = r.into_ref() {
            self.use_counts[r as usize]
        } else {
            0
        }
    }

    fn create_args_copy(
        &mut self,
        env: &Environment,
        before: Ref,
        mc: ModuleOf<Mc>,
        ir: &mut IrModify,
        target: BlockId,
        args: &[Ref],
    ) {
        let arg_refs = ir.get_block_args(target);
        debug_assert_eq!(args.len(), arg_refs.count() as usize);
        let copyargs: Vec<MCReg> = arg_refs
            .iter()
            .zip(args)
            .flat_map(|(to, &from)| {
                let to = self.regs.get(to);
                let from = if from.is_ref() {
                    self.regs.get(from)
                } else {
                    match from {
                        Ref::UNIT => &[],
                        Ref::TRUE | Ref::FALSE => todo!("bools in copyargs"),
                        _ => unreachable!(),
                    }
                };
                debug_assert_eq!(from.len(), to.len());
                to.iter()
                    .copied()
                    .zip(from.iter().copied())
                    .flat_map(|(a, b)| [a, b])
            })
            .collect();
        if !copyargs.is_empty() {
            ir.add_before(
                env,
                before,
                ir::mc::parallel_copy_args(mc, &copyargs, self.unit),
            );
        }
    }

    pub fn copy(
        &mut self,
        env: &Environment,
        before: Ref,
        mc: ModuleOf<Mc>,
        ir: &mut IrModify,
        args: &[MCReg],
    ) {
        ir.add_before(env, before, parallel_copy(mc, args, self.unit));
    }
}

fn primitive_of_ref(r: Ref, ir: &IrModify, types: &Types) -> Primitive {
    let Type::Primitive(p) = types[ir.get_ref_ty(r)] else {
        unreachable!()
    };
    p.try_into().expect("Invalid primitive encountered")
}

enum IntSize {
    I8,
    I16,
    I32,
    I64,
    I128,
}

fn int_size_of_ref(r: Ref, ir: &IrModify, types: &Types) -> IntSize {
    match primitive_of_ref(r, ir, types) {
        Primitive::I8 | Primitive::U8 => IntSize::I8,
        Primitive::I16 | Primitive::U16 => IntSize::I16,
        Primitive::I32 | Primitive::U32 => IntSize::I32,
        Primitive::I64 | Primitive::U64 => IntSize::I64,
        Primitive::I128 | Primitive::U128 => IntSize::I128,
        Primitive::Unit | Primitive::I1 | Primitive::F32 | Primitive::F64 | Primitive::Ptr => {
            unreachable!()
        }
    }
}

ir::visitor! {
    InstructionSelector,
    Rewrite,
    ir, types, inst, env,
    ctx: IselCtx;

    use builtin: ir::Builtin;
    use arith: ir::dialect::Arith;
    use tuple: ir::dialect::Tuple;
    use mem: ir::dialect::Mem;
    use cf: ir::dialect::Cf;

    use x86: crate::arch::x86::isa::X86;
    use mc: ir::mc::Mc;

    patterns:
    (builtin.Undef) => {
        // don't need to do anything, registers are already allocated
    };
    (%r = arith.Int (#x)) => {
        let regs = ctx.regs.get(r);
        match int_size_of_ref(r, ir, types) {
            IntSize::I8 => {
                ir.replace(env, r, x86.mov_ri8(regs[0], x as u8 as u32, ctx.unit));
            }
            IntSize::I16 => {
                ir.replace(env, r, x86.mov_ri16(regs[0], x as u16 as u32, ctx.unit));
            }
            IntSize::I32 => {
                ir.replace(env, r, x86.mov_ri32(regs[0], x as u32, ctx.unit));
            }
            IntSize::I64 => {
                if x > u32::MAX as u64 {
                    todo!()
                }
                ir.replace(env, r, x86.mov_ri64(regs[0], x.try_into().unwrap(), ctx.unit));
            }
            IntSize::I128 => todo!("128 bit ints"),
        }
    };
    (%r = arith.Neg x) => {
        let x = ctx.regs.get(x);
        let out = ctx.regs.get(r);
        match int_size_of_ref(r, ir, types) {
            IntSize::I8 => {
                let (&[out], &[x]) = (out, x) else { unreachable!() };
                ctx.copy(env, r, mc, ir, &[out, x]);
                ir.replace(env, r, x86.neg_r8(out, ctx.unit));
            }
            IntSize::I16 | IntSize::I32 => {
                let (&[out], &[x]) = (out, x) else { unreachable!() };
                ctx.copy(env, r, mc, ir, &[out, x]);
                ir.replace(env, r, x86.neg_r32(x, ctx.unit));
            }
            IntSize::I64 => {
                let (&[out], &[x]) = (out, x) else { unreachable!() };
                ctx.copy(env, r, mc, ir, &[out, x]);
                ir.replace(env, r, x86.neg_r64(x, ctx.unit));
            }
            IntSize::I128 => todo!(),
        }
    };
    (%r = cf.Ret value) => {
        ctx.abi.implement_return(value, ir, env, mc, types, &ctx.regs, r, ctx.unit);
        x86.ret(ctx.unit)
    };
    (%r = cf.Goto (@b b_args)) => {
        let b_args = b_args.to_vec();
        ctx.create_args_copy(env, r, mc, ir, b, &b_args);
        x86.jmp(b, ctx.unit)
    };
    //(arith.LT a b) => { panic!(); Rewrite::Rename(Ref::UNIT)}; // FIXME: this is only to temporarily make the Branch below work
    (%r = cf.Branch (%lt = arith.LT a b) (@b1 b1_args) (@b2 b2_args)) => {
        // FIXmE: should be condition on this pattern
        assert_eq!(ctx.use_count(lt), 1);
        // PERF: cloning the args here
        let b1_args = b1_args.to_vec();
        let b2_args = b2_args.to_vec();
        ir.replace_with(lt, Ref::UNIT);
        match (ctx.regs.get(a), ctx.regs.get(b)) {
            (&[a], &[b]) => {
                ir.replace(env, lt, x86.cmp_rr32(a, b, ctx.unit));
            }
            _ => todo!("large int comparisons"),
        }
        ctx.create_args_copy(env, r, mc, ir, b1, &b1_args.to_vec());
        let jl = x86.jl(b1, ctx.unit);
        ir.add_before(env, r, jl);
        ctx.create_args_copy(env, r, mc, ir, b2, &b2_args.to_vec());
        x86.jmp(b2, ctx.unit)
    };
    (%r = arith.Add a b) => {
        let primitive = primitive_of_ref(r, ir, types);
        let mut single_reg = || {
            let out = ctx.regs.get_one(r);
            let a = ctx.regs.get_one(a);
            let b = ctx.regs.get_one(b);
            ctx.copy(env, r, mc, ir, &[out, a]);
            (out, b)
        };
        match primitive {
            Primitive::I1 => todo!(),
            Primitive::I8 | Primitive::U8 => {
                let (out, b) = single_reg();
                ir.replace(env, r, x86.add_rr8(out, b, ctx.unit));
            }
            Primitive::I16 | Primitive::U16 => {
                let (out, b) = single_reg();
                ir.replace(env, r, x86.add_rr16(out, b, ctx.unit));
            }
            Primitive::I32 | Primitive::U32 => {
                let (out, b) = single_reg();
                ir.replace(env, r, x86.add_rr32(out, b, ctx.unit));
            }
            Primitive::I64 | Primitive::U64 => {
                let (out, b) = single_reg();
                ir.replace(env, r, x86.add_rr64(out, b, ctx.unit));
            }
            Primitive::I128 | Primitive::U128 => todo!("128-bit add"),
            Primitive::F32 => todo!(),
            Primitive::F64 => todo!(),
            Primitive::Unit | Primitive::Ptr => unreachable!(),
        }
    };
    (%r = mem.Decl (type ty)) => {
        let layout = ir::type_layout(types[ty], types, env.primitives());
        let align = layout.align.get() as u32;
        if ctx.stack_size % align != 0 {
            ctx.stack_size += align - (ctx.stack_size % align);
        }
        ctx.stack_size += layout.size as u32;
        let offset = ctx.stack_size;
        let out = ctx.regs.get_one(r);
        x86.lea_rm64(out, MCReg::from_phys(Reg::rsp), (-(offset as i32)) as u32, ctx.unit)
    };
    (%r = mem.Load ptr) => {
        let ptr = ctx.regs.get_one(ptr);
        match types[ir.get_ref_ty(r)] {
            Type::Primitive(primitive_id) => match Primitive::try_from(primitive_id).unwrap() {
                Primitive::Unit => {}
                Primitive::I1 | Primitive::I8 | Primitive::U8 => {
                    ir.replace(env, r, x86.mov_rm8(ctx.regs.get_one(r), ptr, 0, ctx.unit));
                }
                Primitive::I16 | Primitive::U16 => {
                    ir.replace(env, r, x86.mov_rm16(ctx.regs.get_one(r), ptr, 0, ctx.unit));
                }
                Primitive::I32 | Primitive::U32 | Primitive::F32 => {
                    ir.replace(env, r, x86.mov_rm32(ctx.regs.get_one(r), ptr, 0, ctx.unit));
                }
                Primitive::I64 | Primitive::U64 | Primitive::F64 | Primitive::Ptr => {
                    ir.replace(env, r, x86.mov_rm64(ctx.regs.get_one(r), ptr, 0, ctx.unit));
                }
                Primitive::I128 => todo!(),
                Primitive::U128 => todo!(),
            }
            Type::Array(_, _) => todo!(),
            Type::Tuple(_) => todo!(),
        }
    };
    (%r = _) => {
        todo!("unhandled instruction at {r}: {}", env.get_inst_name(ir.get_inst(r)));
        #[allow(clippy::unused_unit, unreachable_code)]
        ()
    };
}
