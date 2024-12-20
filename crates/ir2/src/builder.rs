use crate::{
    argument::IntoArgs, builtins::Builtin, Argument, BlockId, BlockInfo, Environment, Function,
    FunctionId, Instruction, Parameter, Ref, Refs, TypeId, Types,
};

pub struct Builder<'a> {
    env: &'a Environment,
    name: Box<str>,
    pub types: Types,
    insts: Vec<Instruction>,
    extra: Vec<u32>,
    blocks: Vec<BlockInfo>,
    current_block: Option<BlockId>,
}
impl<'a> Builder<'a> {
    pub fn new(env: &'a Environment, name: impl Into<Box<str>>) -> Self {
        Self {
            env,
            name: name.into(),
            types: Types::new(),
            insts: Vec::new(),
            extra: Vec::new(),
            blocks: Vec::new(),
            current_block: None,
        }
    }

    #[track_caller]
    pub fn append<'r>(
        &mut self,
        (function, args): (FunctionId, impl IntoArgs<'r>),
        ty: TypeId,
    ) -> Ref {
        let Some(current_block) = self.current_block else {
            panic!("tried to append to block while no block was active");
        };
        debug_assert!(self.current_block.is_some());
        let def = &self.env[function];
        let terminator = def.terminator;
        let params = &def.params[..];
        let args = args.into_args();
        if args.len() != params.len() {
            panic!(
                "invalid parameter count, expected {} but found {}",
                params.len(),
                args.len()
            );
        }
        let count: usize = params.iter().map(|p| p.slot_count()).sum();
        let mut args = args.zip(params.iter()).flat_map(|(arg, param)| {
            let (a, b) = match (arg, param) {
                (Argument::Ref(r), crate::Parameter::Ref | crate::Parameter::RefOf(_)) => {
                    (r.0, None)
                }
                (Argument::BlockTarget(target), crate::Parameter::BlockTarget) => {
                    let idx = self.extra.len() as u32;
                    // TODO: check block has the correct number of arguments
                    // (currently can't because it is set to 0 before start)
                    self.extra.extend(target.1.iter().map(|&r| r.0));
                    (target.0 .0, Some(idx))
                }
                (Argument::Int(i), crate::Parameter::Int) => (i as u32, Some((i >> 32) as u32)),
                (Argument::Int(i), crate::Parameter::Int32) => {
                    (i.try_into().expect("Int value too large for Int32"), None)
                }
                (Argument::TypeId(id), crate::Parameter::TypeId) => (id.0, None),
                (Argument::FunctionId(id), crate::Parameter::TypeId) => {
                    (id.module.0, Some(id.function.0))
                }
                (Argument::GlobalId(id), crate::Parameter::GlobalId) => (id.module.0, Some(id.idx)),
                _ => panic!("argument was of unexpected kind, expected {param:?}"),
            };
            std::iter::once(a).chain(b)
        });
        let args = if count <= 2 {
            [
                args.next().unwrap_or_default(),
                args.next().unwrap_or_default(),
            ]
        } else {
            let args: Vec<_> = args.collect(); // PERF: no extra collect here
            let idx = self.extra.len() as u32;
            self.extra.extend(args);
            [idx, count as u32]
        };
        let r = Ref(self.insts.len() as _);
        self.insts.push(Instruction { function, args, ty });
        self.blocks[current_block.0 as usize].len += 1;
        if terminator {
            self.current_block = None;
        }
        r
    }

    pub fn create_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as _);
        self.blocks.push(BlockInfo {
            arg_count: 0,
            idx: 0,
            len: 0,
        });
        id
    }

    pub fn begin_block(&mut self, id: BlockId, args: impl IntoIterator<Item = TypeId>) -> Refs {
        debug_assert!(
            self.current_block.is_none(),
            "there was already an active block"
        );
        let block = &mut self.blocks[id.0 as usize];
        debug_assert!(
            block.len == 0 && block.arg_count == 0,
            "can't begin a block twice"
        );
        block.idx = self.insts.len() as _;
        self.insts.extend(args.into_iter().map(|ty| Instruction {
            function: crate::FunctionId {
                module: crate::ModuleId::BUILTINS,
                function: Builtin::BlockArg.id(),
            },
            args: [0, 0],
            ty,
        }));
        block.arg_count = self.insts.len() as u32 - block.idx;
        self.current_block = Some(id);
        Refs {
            idx: block.idx,
            count: block.arg_count,
        }
    }

    pub fn create_and_begin_block(
        &mut self,
        args: impl IntoIterator<Item = TypeId>,
    ) -> (BlockId, Refs) {
        debug_assert!(
            self.current_block.is_none(),
            "there was already an active block"
        );
        let idx = self.insts.len() as u32;
        self.insts.extend(args.into_iter().map(|ty| Instruction {
            function: crate::FunctionId {
                module: crate::ModuleId::BUILTINS,
                function: Builtin::BlockArg.id(),
            },
            args: [0, 0],
            ty,
        }));
        let id = BlockId(self.blocks.len() as _);
        let arg_count = self.insts.len() as u32 - idx;
        let args = Refs {
            idx,
            count: arg_count,
        };
        self.blocks.push(BlockInfo {
            arg_count,
            idx,
            len: 0,
        });
        self.current_block = Some(id);
        (id, args)
    }

    pub fn finish(self, return_type: TypeId) -> Function {
        let ir = crate::FunctionIr {
            blocks: self.blocks,
            insts: self.insts,
            extra: self.extra,
        };
        let entry = &ir.blocks[BlockId::ENTRY.idx()];
        let params = (entry.idx..entry.idx + entry.arg_count)
            .map(|i| {
                let ty = ir.insts[i as usize].ty;
                Parameter::RefOf(ty)
            })
            .collect();
        Function {
            name: self.name,
            types: self.types,
            params,
            varargs: false,
            terminator: false,
            return_type: Some(return_type),
            ir: Some(ir),
        }
    }
}
