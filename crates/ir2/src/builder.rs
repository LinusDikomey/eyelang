use crate::{
    argument::IntoArgs, Argument, BlockId, BlockInfo, Environment, Function, FunctionId,
    Instruction, Ref, TypeId, Types,
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
    pub fn append(&mut self, (function, args): (FunctionId, impl IntoArgs), ty: TypeId) -> Ref {
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
                (Argument::Block(block_id), crate::Parameter::BlockId) => (block_id.0, None),
                (Argument::Int(i), crate::Parameter::Int) => (i, None),
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

    pub fn begin_block(&mut self, id: BlockId) {
        debug_assert!(
            self.current_block.is_none(),
            "there was already an active block"
        );
        let block = &mut self.blocks[id.0 as usize];
        debug_assert!(block.len == 0, "can't begin a block twice");
        block.idx = self.insts.len() as _;
        self.current_block = Some(id);
    }

    pub fn create_and_begin_block(&mut self) -> BlockId {
        debug_assert!(
            self.current_block.is_none(),
            "there was already an active block"
        );
        let id = BlockId(self.blocks.len() as _);
        self.blocks.push(BlockInfo {
            arg_count: 0,
            idx: self.insts.len() as _,
            len: 0,
        });
        self.current_block = Some(id);
        id
    }

    pub fn finish(self, return_type: TypeId) -> Function {
        let ir = crate::FunctionIr {
            blocks: self.blocks,
            insts: self.insts,
            extra: self.extra,
        };
        Function {
            name: self.name,
            types: self.types,
            params: vec![],
            varargs: false,
            terminator: false,
            return_type: Some(return_type),
            ir: Some(ir),
        }
    }
}
