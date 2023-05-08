use crate::{
    ast::{GlobalId, VariantId},
    ir::{Instruction, Data, Tag, Ref, FunctionIr, BlockIndex},
    types::Primitive, resolve::type_info::{TypeInfo, TypeTable}, irgen::CreateReason,
};

use super::{RefVal, FunctionId, types::{TypeRef, IrType, IrTypes}};

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

#[derive(Debug)]
pub struct IrBuilder<'a> {
    pub inst: Vec<Instruction>,
    pub emit: bool,
    current_block: u32,
    next_block: u32,
    pub blocks: Vec<u32>,
    pub extra: Vec<u8>,
    pub types: IrTypes,
    pub inferred_types: &'a TypeTable,
    create_reason: CreateReason,
}
impl<'a> IrBuilder<'a> {
    pub fn new(ir_types: IrTypes, inferred_types: &'a TypeTable, create_reason: CreateReason) -> Self {
        Self {
            inst: vec![Instruction {
                data: Data { block: BlockIndex(0) },
                tag: Tag::BlockBegin,
                ty: TypeRef::NONE,
                used: false
            }],
            emit: true,
            current_block: 0,
            next_block: 1,
            blocks: vec![0],
            extra: Vec::new(),
            types: ir_types,
            inferred_types,
            create_reason,
        }
    }

    pub fn create_reason(&self) -> CreateReason { self.create_reason }

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
    fn add(&mut self, data: Data, tag: Tag, ty: impl Into<IdxOrTy>) -> Ref {
        debug_assert!(!tag.is_untyped(), "The IR instruction {tag:?} doesn't need a type");
        debug_assert!(tag.is_usable(), "The IR instruction {tag:?} doesn't have a usable result");
        let ty = self.ty(ty);
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
            ty: TypeRef::NONE,
            used: false
        });
    }

    fn extra_data(&mut self, bytes: &[u8]) -> u32 {
        let idx = self.extra.len() as u32;
        self.extra.extend(bytes);
        idx
    }

    #[must_use = "block has to be begun somewhere"]
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
                ty: TypeRef::NONE,
                used: false
            });
        }
    }

    pub fn current_block(&self) -> BlockIndex {
        BlockIndex(self.current_block)
    }

    pub fn finish(self) -> FunctionIr<IrTypes> {
        #[cfg(debug_assertions)]
        for pos in &self.blocks {
            assert_ne!(*pos, u32::MAX, "block wasn't initialized");
        }

        FunctionIr {
            inst: self.inst,
            extra: self.extra,
            blocks: self.blocks,
            types: self.types,
        }
    }

    /// --------------------------------------------------------------
    /// -------------------- instruction builders --------------------
    /// --------------------------------------------------------------

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn build_ret(&mut self, val: Ref) {
        self.add_unused_untyped(Tag::Ret, Data { un_op: val });
    }

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn build_ret_undef(&mut self) {
        self.add_unused_untyped(Tag::RetUndef, Data { none: () });
    }

    pub fn build_param(&mut self, param_idx: u32, param_ptr_ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { int32: param_idx }, Tag::Param, param_ptr_ty)
    }

    pub fn _build_uninit(&mut self, ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { none: () }, Tag::Uninit, ty)
    }

    pub fn build_int(&mut self, int: u64, ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { int }, Tag::Int, ty)
    }

    pub fn build_large_int(&mut self, int: u128, int_ty: impl Into<IdxOrTy>) -> Ref {
        debug_assert!(int > u64::MAX as u128, "use build_int if the int is smaller than u64::MAX");
        let extra = self.extra_data(&int.to_le_bytes());
        self.add(Data { extra }, Tag::LargeInt, int_ty)
    }

    pub fn build_float(&mut self, float: f64, float_ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { float }, Tag::Float, float_ty)
    }

    /*pub fn build_enum_lit(&mut self, variant: &str, ty: impl Into<TypeTableIdxOrInfo>) -> Ref {
        let ty = ty.into().into_idx(&mut self.types);
        let extra = self.extra_data(variant.as_bytes());
        self.add(Data { extra_len: (extra, variant.len() as u32) }, Tag::EnumLit, ty)
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
    pub fn build_func(&mut self, func_symbol: FunctionId, ty: TypeRef) -> Ref {
        self.add(Data { func_symbol }, Tag::Func, ty)
    }
    */

    pub fn build_type(&mut self, ty: TypeRef) -> Ref {
        self.add(Data { ty }, Tag::Type, IrType::Primitive(Primitive::Type))
    }

    fn ty(&mut self, ty: impl Into<IdxOrTy>) -> TypeRef {
        match ty.into() {
            IdxOrTy::Idx(idx) => idx,
            IdxOrTy::Ty(ty) => self.types.add(ty)
        }
    }

    pub fn build_decl(&mut self, ty: impl Into<IdxOrTy>) -> Ref {
        let ty = self.ty(ty);
        let ptr_ty = self.types.add_ptr_ty(ty);
        self.add(Data { ty }, Tag::Decl, ptr_ty)
    }

    pub fn build_load(&mut self, var: Ref, ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { un_op: var }, Tag::Load, ty)
    }

    pub fn build_store(&mut self, var: Ref, val: Ref) {
        self.add_unused_untyped(Tag::Store, Data { bin_op: (var, val) });
    }

    pub fn build_string(&mut self, string: &[u8], null_terminate: bool, ty: impl Into<IdxOrTy>) -> Ref {
        let ty = self.ty(ty);
        debug_assert!(string.len() <= u32::MAX as usize, "String is too long");
        let extra = self.extra_data(string);
        if null_terminate {
            self.extra_data(&[b'\0']);
        }
        self.add(Data { extra_len: (extra, string.len() as u32) }, Tag::String, ty)
    }

    pub fn build_call(&mut self, func: FunctionId, params: impl IntoIterator<Item = Ref>, return_ty: impl Into<IdxOrTy>)
    -> Ref {
        let extra = self.extra_data(&func.to_bytes());
        let mut param_count = 0;
        for param in params {
            self.extra_data(&param.to_bytes());
            param_count += 1;
        }
        self.add(Data { extra_len: (extra, param_count) }, Tag::Call, return_ty)
    }

    pub fn build_neg(&mut self, val: Ref, ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { un_op: val }, Tag::Neg, ty)
    }

    pub fn build_not(&mut self, val: Ref, ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { un_op: val }, Tag::Not, ty)
    }

    pub fn build_global(&mut self, global: GlobalId, ptr_ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { global_symbol: global }, Tag::Global, ptr_ty)
    }

    
    pub fn build_bin_op(&mut self, bin_op: BinOp, l: Ref, r: Ref, ty: impl Into<IdxOrTy>) -> Ref {
        let tag = match bin_op {
            BinOp::Add => Tag::Add,
            BinOp::Sub => Tag::Sub,
            BinOp::Mul => Tag::Mul,
            BinOp::Div => Tag::Div,
            BinOp::Mod => Tag::Mod,
            BinOp::Or => {
                if l.into_val() == Some(RefVal::True) || r.into_val() == Some(RefVal::True) {
                    return Ref::val(RefVal::True);
                } else if l.into_val() == Some(RefVal::False) {
                    return r;
                } else if r.into_val() == Some(RefVal::False) {
                    return l;
                }
                Tag::Or
            }
            BinOp::And => {
                if l.into_val() == Some(RefVal::True) {
                    return r;
                } else if r.into_val() == Some(RefVal::True) {
                    return l;
                } else if l.into_val() == Some(RefVal::False) || r.into_val() == Some(RefVal::False) {
                    return Ref::val(RefVal::False);
                }
                Tag::And
            }
            BinOp::Eq => Tag::Eq,
            BinOp::NE => Tag::NE,
            BinOp::LT => Tag::LT,
            BinOp::GT => Tag::GT,
            BinOp::LE => Tag::LE,
            BinOp::GE => Tag::GE,
        };
        self.add(Data { bin_op: (l, r) }, tag, ty)
    }

    pub fn build_member(&mut self, var: Ref, member_idx: Ref, ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { bin_op: (var, member_idx) }, Tag::Member, ty)
    }
    pub fn build_member_int(&mut self, var: Ref, idx: u32, ty: impl Into<IdxOrTy>) -> Ref {
        let u32_ty = self.types.add(IrType::Primitive(Primitive::U32));
        let idx = self.build_int(idx as u64, u32_ty);
        self.build_member(var, idx, ty)
    }

    pub fn build_enum_tag(&mut self, enum_ptr: Ref, tag_ptr_ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { un_op: enum_ptr }, Tag::EnumTag, tag_ptr_ty)
    }
    pub fn build_enum_value_tag(&mut self, enum_val: Ref, tag_ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { un_op: enum_val }, Tag::EnumValueTag, tag_ty)
    }

    pub fn build_enum_variant_member(&mut self, var: Ref, variant: VariantId, arg: u16, ty: impl Into<IdxOrTy>)
    -> Ref {
        self.add(Data { variant_member: (var, variant, arg) }, Tag::EnumVariantMember, ty)
    }

    pub fn build_enum_value_variant_member(&mut self, var: Ref, variant: VariantId, arg: u16, ty: impl Into<IdxOrTy>)
    -> Ref {
        self.add(Data { variant_member: (var, variant, arg) }, Tag::EnumValueVariantMember, ty)
    }

    pub fn build_value(&mut self, val: Ref, idx: u32, ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { ref_int: (val, idx) }, Tag::Value, ty)
    }

    pub fn build_cast(&mut self, val: Ref, target_ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { un_op: val }, Tag::Cast, target_ty)
    }

    pub fn build_goto(&mut self, block: BlockIndex) {
        self.add_unused_untyped(Tag::Goto, Data { block });
    }

    pub fn build_branch(&mut self, cond: Ref, on_true: BlockIndex, on_false: BlockIndex) {
        let branch_extra = self.extra_data(&on_true.0.to_le_bytes());
        self.extra_data(&on_false.0.to_le_bytes());
        self.add_unused_untyped(Tag::Branch, Data { ref_int: (cond, branch_extra) });
    }

    pub fn build_phi(&mut self, branches: impl IntoIterator<Item = (BlockIndex, Ref)>, expected: impl Into<IdxOrTy>)
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

    /// TODO: proper semantics for asm expressions
    pub fn _build_asm(&mut self, asm_str: &str, values: impl IntoIterator<Item = Ref>) {
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

pub enum IdxOrTy {
    Idx(TypeRef),
    Ty(IrType),
}
impl From<TypeRef> for IdxOrTy {
    fn from(value: TypeRef) -> Self {
        Self::Idx(value)
    }
}
impl From<IrType> for IdxOrTy {
    fn from(value: IrType) -> Self {
        Self::Ty(value)
    }
}

pub enum TypeTableIdxOrInfo {
    Idx(TypeRef),
    Info(TypeInfo),
}
impl From<TypeRef> for TypeTableIdxOrInfo {
    fn from(idx: TypeRef) -> Self { Self::Idx(idx) }
}
impl From<TypeInfo> for TypeTableIdxOrInfo {
    fn from(info: TypeInfo) -> Self { Self::Info(info) }
}
