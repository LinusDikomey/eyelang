use crate::{
    ast::ModuleId,
    ir::{Instruction, typing::{TypeTable, TypeInfo}, Data, Tag, TypeTableIndex, Ref, FunctionIr, BlockIndex},
    lexer::Span,
    error::Errors
};

pub struct IrBuilder {
    module: ModuleId,
    ir: Vec<Instruction>,
    current_block: u32,
    next_block: u32,
    pub types: TypeTable,
    extra_data: Vec<u8>,
}
impl IrBuilder {
    pub fn new(module: ModuleId) -> Self {
        Self {
            module,
            ir: vec![Instruction {
                data: Data { block: BlockIndex(0) },
                tag: Tag::BlockBegin,
                span: Span::new(0, 0, module),
                ty: TypeTableIndex::NONE,
                used: false
            }],
            current_block: 0,
            next_block: 1,
            types: TypeTable::new(),
            extra_data: Vec::new(),
        }
    }

    #[must_use = "Use add_unused if the result of this instruction isn't needed."]
    pub fn add(&mut self, data: Data, tag: Tag, ty: TypeTableIndex) -> Ref {
        debug_assert!(!tag.is_untyped(), "The IR instruction {tag:?} doesn't need a type");
        let idx = self.ir.len() as u32;
        self.ir.push(Instruction {
            data,
            tag,
            ty,
            span: Span::todo(self.module),
            used: true
        });
        Ref::index(idx)
    }

    pub fn add_untyped(&mut self, tag: Tag, data: Data) {
        debug_assert!(tag.is_untyped(), "The IR instruction {tag:?} needs a type");
        self.ir.push(Instruction {
            data,
            tag,
            ty: TypeTableIndex::NONE,
            span: Span::todo(self.module),
            used: false
        })
    }

    pub fn add_unused(&mut self, tag: Tag, data: Data, ty: TypeTableIndex) {
        debug_assert!(!tag.is_untyped(), "The unused IR instruction {tag:?} doesn't need a type");
        self.ir.push(Instruction {
            data,
            tag,
            ty: ty,
            span: Span::todo(self.module),
            used: false
        });
    }

    pub fn add_unused_untyped(&mut self, tag: Tag, data: Data) {
        debug_assert!(tag.is_untyped(), "The unused IR instruction {tag:?} needs a type");
        self.ir.push(Instruction {
            data,
            tag,
            ty: TypeTableIndex::NONE,
            span: Span::todo(self.module),
            used: false
        });
    }

    pub fn extra_data<'a>(&mut self, bytes: &[u8]) -> u32 {
        let idx = self.extra_data.len() as u32;
        self.extra_data.extend(bytes);
        idx
    }

    pub fn _extra_len(&mut self, bytes: &[u8]) -> (u32, u32) {
        (self.extra_data(bytes), bytes.len() as u32)
    }

    pub fn create_block(&mut self) -> BlockIndex {
        let idx = BlockIndex(self.next_block);
        self.next_block += 1;
        idx
    }

    pub fn begin_block(&mut self, idx: BlockIndex) {
        debug_assert!(
            matches!(
                self.ir[self.ir.len() - 1].tag,
                Tag::Branch | Tag::Goto | Tag::Ret
            ),
            "Can't begin next block without exiting previous one (Branch/Goto/Ret)"
        );

        self.current_block = idx.0;
        self.ir.push(Instruction {
            data: Data { block: idx },
            tag: Tag::BlockBegin,
            ty: TypeTableIndex::NONE,
            span: Span::todo(self.module),
            used: false
        });
    }

    pub fn finish(self) -> FunctionIr {
        FunctionIr {
            inst: self.ir,
            extra: self.extra_data,
            types: self.types.finalize(),
            block_count: self.next_block,
        }
    }

    pub fn _create_and_begin_block(&mut self) -> BlockIndex {
        let block = self.create_block();
        self.begin_block(block);
        block
    }

    pub fn specify(&mut self, idx: TypeTableIndex, info: TypeInfo, errors: &mut Errors) {
        self.types.specify(idx, info, errors, self.module)
    }
}
