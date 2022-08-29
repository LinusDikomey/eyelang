use crate::{
    ast::ModuleId,
    ir::{Instruction, typing::{TypeTable, TypeInfo}, Data, Tag, TypeTableIndex, Ref, FunctionIr, BlockIndex, SymbolKey},
    error::Errors, span::TSpan, types::Primitive
};

use super::{TypingCtx, GenCtx, exhaust::Exhaustion};

pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    Or,
    And,
    
    Eq,
    NE,

    LT,
    GT,
    LE,
    GE,
}
impl From<BinOp> for Tag {
    fn from(op: BinOp) -> Self {
        match op {
            BinOp::Add => Tag::Add,
            BinOp::Sub => Tag::Sub,
            BinOp::Mul => Tag::Mul,
            BinOp::Div => Tag::Div,
            BinOp::Mod => Tag::Mod,
            BinOp::Or => Tag::Or,
            BinOp::And => Tag::And,
            BinOp::Eq => Tag::Eq,
            BinOp::NE => Tag::NE,
            BinOp::LT => Tag::LT,
            BinOp::GT => Tag::GT,
            BinOp::LE => Tag::LE,
            BinOp::GE => Tag::GE,
        }
    }
}

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
    fn add(&mut self, data: Data, tag: Tag, ty: TypeTableIndex) -> Ref {
        debug_assert!(!tag.is_untyped(), "The IR instruction {tag:?} doesn't need a type");
        debug_assert!(tag.is_usable(), "The IR instruction {tag:?} doesn't have a usable result");
        self.add_inst(Instruction {
            data,
            tag,
            ty,
            used: true
        })
    }

    /*
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
    */

    #[cfg_attr(debug_assertions, track_caller)]
    fn add_unused_untyped(&mut self, tag: Tag, data: Data) {
        debug_assert!(tag.is_untyped(), "The unused IR instruction {tag:?} needs a type");
        self.add_inst(Instruction {
            data,
            tag,
            ty: TypeTableIndex::NONE,
            used: false
        });
    }

    fn extra_data(&mut self, bytes: &[u8]) -> u32 {
        let idx = self.extra.len() as u32;
        self.extra.extend(bytes);
        idx
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

    pub fn finish(self, ctx: &TypingCtx, errors: &mut Errors) -> FunctionIr {
        #[cfg(debug_assertions)]
        for pos in &self.blocks {
            assert_ne!(*pos, u32::MAX, "block wasn't initialized");
        }
        let types = self.types.finalize();
        for (exhaustion, ty, span) in self.exhaustion_checks {
            let ty = &types[ty];
            match exhaustion.is_exhausted(ty, ctx) {
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

    pub fn build_ret(&mut self, val: Ref) {
        self.add_unused_untyped(Tag::Ret, Data { un_op: val });
    }

    pub fn build_ret_undef(&mut self) {
        self.add_unused_untyped(Tag::RetUndef, Data { none: () });
    }

    pub fn build_param(&mut self, param_idx: u32, param_ptr_ty: TypeTableIndex) -> Ref {
        self.add(Data { int32: param_idx }, Tag::Param, param_ptr_ty)
    }

    pub fn build_uninit(&mut self, ty: TypeTableIndex) -> Ref {
        self.add(Data { none: () }, Tag::Uninit, ty)
    }

    pub fn build_int(&mut self, int: u64, int_ty: TypeTableIndex) -> Ref {
        self.add(Data { int }, Tag::Int, int_ty)
    }

    pub fn build_large_int(&mut self, int: u128, int_ty: TypeTableIndex) -> Ref {
        debug_assert!(int > u64::MAX as u128, "use build_int if the int is smaller than u64::MAX");
        let extra = self.extra_data(&int.to_le_bytes());
        self.add(Data { extra }, Tag::LargeInt, int_ty)
    }

    pub fn build_float(&mut self, float: f64, float_ty: TypeTableIndex) -> Ref {
        self.add(Data { float }, Tag::Float, float_ty)
    }

    pub fn build_enum_lit(&mut self, variant: &str, ty: impl Into<TypeTableIdxOrInfo>) -> Ref {
        let ty = ty.into().into_idx(&mut self.types);
        let extra = self.extra_data(variant.as_bytes());
        self.add(Data { extra_len: (extra, variant.len() as u32) }, Tag::EnumLit, ty)
    }
    
    pub fn build_func(&mut self, func_symbol: SymbolKey, ty: TypeTableIndex) -> Ref {
        self.add(Data { symbol: func_symbol }, Tag::TraitFunc, ty)
    }

    pub fn build_trait_func(&mut self, trait_symbol: SymbolKey, func_idx: u32, ty: TypeTableIndex) -> Ref {
        let symbol_extra = self.extra_data(&trait_symbol.bytes());
        self.add(Data { trait_func: (symbol_extra, func_idx) }, Tag::TraitFunc, ty)
    }

    pub fn build_type(&mut self, type_symbol: SymbolKey, ty: TypeTableIndex) -> Ref {
        self.add(Data { symbol: type_symbol }, Tag::Type, ty)
    }

    pub fn build_trait(&mut self, trait_symbol: SymbolKey, ty: TypeTableIndex) -> Ref {
        self.add(Data { symbol: trait_symbol }, Tag::Trait, ty)
    }

    pub fn build_local_type(&mut self, local_type: TypeTableIndex, ty: TypeTableIndex) -> Ref {
        self.add(Data { ty: local_type }, Tag::LocalType, ty)
    }

    pub fn build_module(&mut self, module: ModuleId, ty: TypeTableIndex) -> Ref {
        self.add(Data { int32: module.inner() }, Tag::Module, ty)
    }

    pub fn build_decl(&mut self, ty: impl Into<TypeTableIdxOrInfo>) -> Ref {
        let ty = ty.into().into_idx(&mut self.types);
        let ptr_ty = self.types.add(TypeInfo::Pointer(ty));
        self.add(Data { ty }, Tag::Decl, ptr_ty)
    }

    pub fn build_load(&mut self, var: Ref, ty: TypeTableIndex) -> Ref {
        self.add(Data { un_op: var }, Tag::Load, ty)
    }

    pub fn build_store(&mut self, var: Ref, val: Ref) {
        self.add_unused_untyped(Tag::Store, Data { bin_op: (var, val) });
    }

    pub fn build_string(&mut self, string: &[u8], null_terminate: bool, ty: TypeTableIndex) -> Ref {
        #[cfg(debug_assertions)]
        {
            let TypeInfo::Pointer(pointee_ty) = self.types[ty] else { panic!("'*i8' type expected") };
            if !matches!(self.types[pointee_ty], TypeInfo::Primitive(Primitive::I8)) {
                panic!("'*i8' type expected");
            }
        }
        debug_assert!(string.len() <= u32::MAX as usize, "String is too long");
        let extra = self.extra_data(string);
        if null_terminate {
            self.extra_data(&[b'\0']);
        }
        self.add(Data { extra_len: (extra, string.len() as u32) }, Tag::String, ty)
    }

    pub fn build_call(&mut self, func: SymbolKey, params: impl IntoIterator<Item = Ref>, return_ty: TypeTableIndex)
    -> Ref {
        let extra = self.extra_data(&func.bytes());
        let mut param_count = 0;
        for param in params {
            self.extra_data(&param.to_bytes());
            param_count += 1;
        }
        self.add(Data { extra_len: (extra, param_count) }, Tag::Call, return_ty)
    }

    pub fn build_neg(&mut self, val: Ref, ty: TypeTableIndex) -> Ref {
        self.add(Data { un_op: val }, Tag::Neg, ty)
    }

    pub fn build_not(&mut self, val: Ref, ty: TypeTableIndex) -> Ref {
        self.add(Data { un_op: val }, Tag::Not, ty)
    }

    pub fn build_global(&mut self, global: SymbolKey, ptr_ty: TypeTableIndex) -> Ref {
        self.add(Data { symbol: global }, Tag::Global, ptr_ty)
    }

    
    pub fn build_bin_op(&mut self, bin_op: BinOp, l: Ref, r: Ref, ty: TypeTableIndex) -> Ref {
        self.add(Data { bin_op: (l, r) }, bin_op.into(), ty)
    }

    pub fn build_member(&mut self, var: Ref, member_idx: Ref, ty: TypeTableIndex) -> Ref {
        self.add(Data { bin_op: (var, member_idx) }, Tag::Member, ty)
    }
    pub fn build_member_int(&mut self, var: Ref, idx: u32, ty: TypeTableIndex) -> Ref {
        let u32_ty = self.types.add(TypeInfo::Primitive(Primitive::U32));
        let idx = self.build_int(idx as u64, u32_ty);
        self.build_member(var, idx, ty)
    }

    pub fn build_cast(&mut self, val: Ref, target_ty: TypeTableIndex) -> Ref {
        self.add(Data { un_op: val }, Tag::Cast, target_ty)
    }

    pub fn build_goto(&mut self, block: BlockIndex) {
        self.add_unused_untyped(Tag::Goto, Data { block });
    }

    pub fn build_branch(&mut self, cond: Ref, on_true: BlockIndex, on_false: BlockIndex) {
        let branch_extra = self.extra_data(&on_true.0.to_le_bytes());
        self.extra_data(&on_false.0.to_le_bytes());
        self.add_unused_untyped(Tag::Branch, Data { branch: (cond, branch_extra) });
    }

    pub fn build_phi(&mut self, branches: impl IntoIterator<Item = (BlockIndex, Ref)>, expected: TypeTableIndex)
    -> Ref {
        let extra = self.extra.len() as u32;
        let mut branch_count = 0;
        for (branch, r) in branches {
            branch_count += 1;
            self.extra_data(&branch.bytes());
            self.extra_data(&r.to_bytes());
        }
        self.add(Data { extra_len: (extra, branch_count) }, Tag::Phi, expected)
    }

    pub fn build_asm(&mut self, asm_str: &str, values: impl IntoIterator<Item = Ref>) {
        assert!(asm_str.len() <= u16::MAX as usize, "inline assembly string is too long");
        let extra = self.extra_data(asm_str.as_bytes());
        let mut count = 0;
        for r in values {
            self.extra_data(&r.to_bytes());
            count += 1;
        }
        assert!(count <= u16::MAX as usize, "too many arguments for inline assembly");
        self.add_unused_untyped(Tag::Asm, Data { asm: (extra, asm_str.len() as u16, count as u16) });
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