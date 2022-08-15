use crate::{
    ast::ModuleId,
    ir::{Instruction, typing::{TypeTable, TypeInfo}, Data, Tag, TypeTableIndex, Ref, FunctionIr, BlockIndex},
    error::Errors, span::TSpan
};

use super::TypingCtx;

#[derive(Clone, Debug)]
pub struct IrBuilder {
    module: ModuleId,
    pub inst: Vec<Instruction>,
    pub emit: bool,
    current_block: u32,
    next_block: u32,
    pub blocks: Vec<u32>,
    pub types: TypeTable,
    pub extra: Vec<u8>,
}
impl IrBuilder {
    pub fn new(module: ModuleId) -> Self {
        Self {
            module,
            inst: vec![Instruction {
                data: Data { block: BlockIndex(0) },
                tag: Tag::BlockBegin,
                ty: TypeTableIndex::NONE,
                used: false
            }],
            emit: true,
            current_block: 0,
            next_block: 1,
            blocks: vec![0],
            types: TypeTable::new(),
            extra: Vec::new(),
        }
    }

    /// Internal function to add an instruction. This will not add anything if `emit` is set to false.
    fn add_inst(&mut self, inst: Instruction) -> Ref {
        let idx = Ref::index(self.inst.len() as u32);
        if self.emit {
            if inst.tag == Tag::BlockBegin {
                debug_assert!(self.inst.last().map_or(true, |last| last.tag.is_terminator()),
                    "New block started without preceding terminator: \n{}", self.clone().finish());
            } else {
                debug_assert!(self.inst.last().map_or(true, |last| !last.tag.is_terminator()),
                    "Instruction added after a terminator: instruction: {:?}\n\n{}", inst, self.clone().finish());
            }
            self.inst.push(inst);
        }
        idx
    }

    #[must_use = "Use add_unused if the result of this instruction isn't needed."]
    pub fn add(&mut self, data: Data, tag: Tag, ty: TypeTableIndex) -> Ref {
        debug_assert!(!tag.is_untyped(), "The IR instruction {tag:?} doesn't need a type");
        debug_assert!(tag.is_usable(), "The IR instruction {tag:?} doesn't have a usable result");
        self.add_inst(Instruction {
            data,
            tag,
            ty,
            used: true
        })
    }

    #[must_use = "Use add_unused_untyped if the result of this instruction isn't needed."]
    pub fn _add_untyped(&mut self, tag: Tag, data: Data) -> Ref {
        debug_assert!(tag.is_untyped(), "The IR instruction {tag:?} needs a type");
        debug_assert!(tag.is_usable(), "The IR instruction {tag:?} doesn't have a usable result");
        self.add_inst(Instruction {
            data,
            tag,
            ty: TypeTableIndex::NONE,
            used: false
        })
    }

    pub fn _add_unused(&mut self, tag: Tag, data: Data, ty: TypeTableIndex) {
        debug_assert!(!tag.is_untyped(), "The unused IR instruction {tag:?} doesn't need a type");
        self.add_inst(Instruction {
            data,
            tag,
            ty,
            used: false
        });
    }

    pub fn add_unused_untyped(&mut self, tag: Tag, data: Data) {
        debug_assert!(tag.is_untyped(), "The unused IR instruction {tag:?} needs a type");
        self.add_inst(Instruction {
            data,
            tag,
            ty: TypeTableIndex::NONE,
            used: false
        });
    }

    pub fn extra_data(&mut self, bytes: &[u8]) -> u32 {
        let idx = self.extra.len() as u32;
        self.extra.extend(bytes);
        idx
    }

    pub fn _extra_len(&mut self, bytes: &[u8]) -> (u32, u32) {
        (self.extra_data(bytes), bytes.len() as u32)
    }

    pub fn create_block(&mut self) -> BlockIndex {
        let idx = BlockIndex(self.next_block);
        if self.emit {
            self.next_block += 1;
            self.blocks.push(u32::MAX);
        }
        idx
    }

    pub fn currently_terminated(&self) -> bool {
        self.inst.last().map_or(false, |last| last.tag.is_terminator())
    }

    pub fn begin_block(&mut self, idx: BlockIndex) {
        if self.emit {
            debug_assert!(
                self.currently_terminated(),
                "Can't begin next block without exiting previous one"
            );
            self.current_block = idx.0;
            debug_assert_eq!(self.blocks[idx.0 as usize], u32::MAX,
                "begin_block called twice on the same block");
            let block_pos = self.inst.len() as u32;
            self.blocks[idx.0 as usize] = block_pos;
            self.add_inst(Instruction {
                data: Data { block: idx },
                tag: Tag::BlockBegin,
                ty: TypeTableIndex::NONE,
                used: false
            });
        }
    }

    pub fn current_block(&self) -> BlockIndex {
        BlockIndex(self.current_block)
    }

    pub fn finish(self) -> FunctionIr {
        #[cfg(debug_assertions)]
        for pos in &self.blocks {
            assert_ne!(*pos, u32::MAX, "block wasn't initialized");
        }
        FunctionIr {
            inst: self.inst,
            extra: self.extra,
            types: self.types.finalize(),
            blocks: self.blocks,
        }
    }

    pub fn _create_and_begin_block(&mut self) -> BlockIndex {
        let block = self.create_block();
        self.begin_block(block);
        block
    }

    pub fn specify(&mut self, idx: TypeTableIndex, info: TypeInfo, errors: &mut Errors, span: TSpan, ctx: &TypingCtx) {
        self.types.specify(idx, info, errors, span.in_mod(self.module), ctx);
    }

    pub fn invalidate(&mut self, idx: TypeTableIndex) {
        self.types.update_type(idx, TypeInfo::Invalid);
    }

    pub fn build_decl(&mut self, ty: impl Into<TypeTableIdxOrInfo>) -> Ref {
        let ty = ty.into().into_idx(&mut self.types);
        let ptr_ty = self.types.add(TypeInfo::Pointer(ty));
        self.add(Data { ty }, Tag::Decl, ptr_ty)
    }
}

pub enum TypeTableIdxOrInfo {
    Idx(TypeTableIndex),
    Info(TypeInfo),
}
impl TypeTableIdxOrInfo {
    pub fn into_idx(self, types: &mut TypeTable) -> TypeTableIndex {
        match self {
            TypeTableIdxOrInfo::Idx(idx) => idx,
            TypeTableIdxOrInfo::Info(info) => types.add(info),
        }
    }
}
impl From<TypeTableIndex> for TypeTableIdxOrInfo {
    fn from(idx: TypeTableIndex) -> Self { Self::Idx(idx) }
}
impl From<TypeInfo> for TypeTableIdxOrInfo {
    fn from(info: TypeInfo) -> Self { Self::Info(info) }
}