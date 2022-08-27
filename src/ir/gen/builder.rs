use crate::{
    ast::ModuleId,
    ir::{Instruction, typing::{TypeTable, TypeInfo}, Data, Tag, TypeTableIndex, Ref, FunctionIr, BlockIndex},
    error::Errors, span::TSpan
};

use super::{TypingCtx, GenCtx, exhaust::Exhaustion};

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

    // exhaustion checks are deferred until the end of the IR generation for the type is known.
    exhaustion_checks: Vec<(Exhaustion, TypeTableIndex, TSpan)>,
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

            exhaustion_checks: Vec::new(),
        }
    }

    /// Internal function to add an instruction. This will not add anything if `emit` is set to false.
    #[cfg_attr(debug_assertions, track_caller)]
    fn add_inst(&mut self, inst: Instruction) -> Ref {
        let idx = Ref::index(self.inst.len() as u32);
        if self.emit {
            if inst.tag == Tag::BlockBegin {
                debug_assert!(self.inst.last().map_or(true, |last| last.tag.is_terminator()),
                    "New block started without preceding terminator");
            } else {
                debug_assert!(self.inst.last().map_or(true, |last| !last.tag.is_terminator()),
                    "Instruction added after a terminator: instruction: {:?}", inst);
            }
            self.inst.push(inst);
        }
        idx
    }

    #[must_use = "Use add_unused if the result of this instruction isn't needed."]
    #[cfg_attr(debug_assertions, track_caller)]
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
    #[cfg_attr(debug_assertions, track_caller)]
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

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn _add_unused(&mut self, tag: Tag, data: Data, ty: TypeTableIndex) {
        debug_assert!(!tag.is_untyped(), "The unused IR instruction {tag:?} doesn't need a type");
        self.add_inst(Instruction {
            data,
            tag,
            ty,
            used: false
        });
    }

    #[cfg_attr(debug_assertions, track_caller)]
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

    #[track_caller]
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

    pub fn finish(self, errors: &mut Errors) -> FunctionIr {
        #[cfg(debug_assertions)]
        for pos in &self.blocks {
            assert_ne!(*pos, u32::MAX, "block wasn't initialized");
        }
        let types = self.types.finalize();
        for (exhaustion, ty, span) in self.exhaustion_checks {
            let ty = &types[ty];
            match exhaustion.is_exhausted(ty) {
                Some(true) => {}
                Some(false) => {
                    errors.emit_span(crate::error::Error::Inexhaustive, span.in_mod(self.module));
                }
                None => debug_assert!(errors.has_errors(),
                    "there should have been at least one error if this exhaustion is invalid")
            }
        }
        FunctionIr {
            inst: self.inst,
            extra: self.extra,
            types,
            blocks: self.blocks,
        }
    }

    pub fn _create_and_begin_block(&mut self) -> BlockIndex {
        let block = self.create_block();
        self.begin_block(block);
        block
    }

    pub fn specify(&mut self, idx: TypeTableIndex, info: TypeInfo, errors: &mut Errors, span: TSpan, ctx: &TypingCtx,
    ) {
        self.types.specify(idx, info, errors, span.in_mod(self.module), ctx);
    }
    pub fn specify_enum_variant(&mut self, idx: TypeTableIndex, name_span: TSpan, ctx: &mut GenCtx) {
        
        let name = ctx.src(name_span);
        
        // avoid creating enum TypeInfo unnecessarily to avoid allocations and complex comparisons
        if let TypeInfo::Enum(names) = self.types.get_type(idx) {
            if !self.types.get_names(names).iter().any(|s| *s == name) {
                let new_names = self.types.extend_names(names, std::iter::once(name.to_owned()));
                self.types.update_type(idx, TypeInfo::Enum(new_names));
            }
        } else {
            let variant = self.types.add_names(std::iter::once(name.to_owned()));
            self.types.specify(
                idx,
                TypeInfo::Enum(variant),
                &mut ctx.errors,
                name_span.in_mod(self.module),
                &ctx.ctx,
            );
        }
    }

    pub fn invalidate(&mut self, idx: TypeTableIndex) {
        self.types.update_type(idx, TypeInfo::Invalid);
    }

    pub fn add_exhaustion_check(&mut self, exhaustion: Exhaustion, idx: TypeTableIndex, span: TSpan) {
        self.exhaustion_checks.push((exhaustion, idx, span));
    }

    /// --------------------------------------------------------------
    /// -------------------- instruction builders --------------------
    /// --------------------------------------------------------------

    pub fn build_goto(&mut self, block: BlockIndex) {
        self.add_unused_untyped(Tag::Goto, Data { block })
    }

    pub fn build_uninit(&mut self, ty: TypeTableIndex) -> Ref {
        self.add(Data { none: () }, Tag::Uninit, ty)
    }

    pub fn build_branch(&mut self, cond: Ref, on_true: BlockIndex, on_false: BlockIndex) {
        let branch_extra = self.extra_data(&on_true.0.to_le_bytes());
        self.extra_data(&on_false.0.to_le_bytes());
        self.add_unused_untyped(Tag::Branch, Data { branch: (cond, branch_extra) });
    }

    pub fn build_decl(&mut self, ty: impl Into<TypeTableIdxOrInfo>) -> Ref {
        let ty = ty.into().into_idx(&mut self.types);
        let ptr_ty = self.types.add(TypeInfo::Pointer(ty));
        self.add(Data { ty }, Tag::Decl, ptr_ty)
    }

    pub fn build_enum_lit(&mut self, variant: &str, ty: impl Into<TypeTableIdxOrInfo>) -> Ref {
        let ty = ty.into().into_idx(&mut self.types);
        let extra = self.extra_data(variant.as_bytes());
        self.add(Data { extra_len: (extra, variant.len() as u32) }, Tag::EnumLit, ty)
    }

    pub fn build_phi(&mut self, branches: impl IntoIterator<Item = (BlockIndex, Ref)>, expected: TypeTableIndex)
    -> Ref {
        let extra = self.extra.len() as u32;
        let mut branch_count = 0;
        for (branch, r) in branches.into_iter() {
            branch_count += 1;
            self.extra_data(&branch.bytes());
            self.extra_data(&r.to_bytes());
        }
        self.add(Data { extra_len: (extra, branch_count) }, Tag::Phi, expected)
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