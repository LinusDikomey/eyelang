use crate::{Instruction, Data, Tag, Ref, FunctionIr, BlockIndex, TypeRefs};

use super::{RefVal, FunctionId, ir_types::{TypeRef, IrType, IrTypes}};

#[derive(Clone, Copy, Debug)]
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

#[derive(Clone, Copy, Debug)]
pub enum Terminator {
    Ret(Ref),
    Goto(BlockIndex),
    Branch {
        cond: Ref,
        on_true: BlockIndex,
        on_false: BlockIndex,
    },
}

#[derive(Debug)]
pub struct IrBuilder<'a> {
    pub inst: Vec<Instruction>,
    pub emit: bool,
    current_block: u32,
    current_block_terminated: bool,
    next_block: u32,
    pub blocks: Vec<u32>,
    pub extra: Vec<u8>,
    pub types: &'a mut IrTypes,
}
impl<'a> IrBuilder<'a> {
    pub fn new(types: &'a mut IrTypes) -> Self {
        Self {
            inst: vec![Instruction {
                data: Data { block: BlockIndex(0) },
                tag: Tag::BlockBegin,
                ty: TypeRef::NONE,
                used: false
            }],
            emit: true,
            current_block: 0,
            current_block_terminated: false,
            next_block: 1,
            blocks: vec![0],
            extra: Vec::new(),
            types,
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
    fn add(&mut self, data: Data, tag: Tag, ty: impl Into<IdxOrTy>) -> Ref {
        debug_assert!(!self.current_block_terminated);
        debug_assert!(tag.is_usable(), "The IR instruction {tag:?} doesn't have a usable result");
        let ty = self.ty(ty);
        self.add_inst(Instruction {
            data,
            tag,
            ty,
            used: true
        })
    }

    #[cfg_attr(debug_assertions, track_caller)]
    fn add_unused(&mut self, tag: Tag, data: Data) {
        debug_assert!(!tag.is_usable());
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

    #[track_caller]
    pub fn begin_block(&mut self, idx: BlockIndex) {
        if self.emit {
            debug_assert!(
                self.current_block_terminated,
                "Can't begin next block without exiting previous one"
            );
            self.current_block = idx.0;
            self.current_block_terminated = false;
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

    pub fn finish(self) -> FunctionIr {
        debug_assert!(self.current_block_terminated, "Last IR block wasn't terminated");

        #[cfg(debug_assertions)]
        for pos in &self.blocks {
            assert_ne!(*pos, u32::MAX, "block wasn't initialized");
        }

        FunctionIr {
            inst: self.inst,
            extra: self.extra,
            blocks: self.blocks,
        }
    }

    /// --------------------------------------------------------------
    /// -------------------- instruction builders --------------------
    /// --------------------------------------------------------------

    pub fn terminate_block(&mut self, terminator: Terminator) {
        debug_assert!(!self.current_block_terminated, "Tried to terminate block twice");
        self.current_block_terminated = true;
        let (tag, data) = match terminator {
            Terminator::Ret(val) => (Tag::Ret, Data { un_op: val }),
            Terminator::Goto(block) => (Tag::Goto, Data { block }),
            Terminator::Branch { cond, on_true, on_false } => {

                let branch_extra = self.extra_data(&on_true.0.to_le_bytes());
                self.extra_data(&on_false.0.to_le_bytes());
                (Tag::Branch, Data { ref_int: (cond, branch_extra )})
            }
        };
        self.add_inst(Instruction { data, tag, ty: TypeRef::NONE, used: false });
    }

    pub fn build_param(&mut self, param_idx: u32, param_ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { int32: param_idx }, Tag::Param, param_ty)
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

    fn ty(&mut self, ty: impl Into<IdxOrTy>) -> TypeRef {
        match ty.into() {
            IdxOrTy::Idx(idx) => idx,
            IdxOrTy::Ty(ty) => self.types.add(ty)
        }
    }

    pub fn build_decl(&mut self, ty: impl Into<IdxOrTy>) -> Ref {
        let ty = self.ty(ty);
        self.add(Data { ty }, Tag::Decl, IrType::Ptr)
    }

    pub fn build_load(&mut self, var: Ref, ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { un_op: var }, Tag::Load, ty)
    }

    pub fn build_store(&mut self, var: Ref, val: Ref) {
        self.add_unused(Tag::Store, Data { bin_op: (var, val) });
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

    /*
    pub fn build_global(&mut self, global: GlobalId, ptr_ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { global_symbol: global }, Tag::Global, ptr_ty)
    }
    */

    
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

    pub fn build_member_ptr(&mut self, var: Ref, idx: u32, elem_types: TypeRefs) -> Ref {
        debug_assert!(idx < elem_types.count, "member ptr is out of bounds");
        let extra = self.extra.len() as u32;
        self.extra.extend(elem_types.to_bytes());
        self.extra.extend(idx.to_le_bytes());
        self.add(Data { ref_int: (var, extra) }, Tag::MemberPtr, IrType::Ptr)
    }

    pub fn build_member_value(&mut self, val: Ref, idx: u32, ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { ref_int: (val, idx) }, Tag::MemberValue, ty)
    }

    pub fn build_cast_int(&mut self, val: Ref, target_ty: IrType) -> Ref {
        debug_assert!(target_ty.is_int());
        self.add(Data { un_op: val }, Tag::CastInt, target_ty)
    }

    pub fn build_cast_float(&mut self, val: Ref, target_ty: IrType) -> Ref {
        debug_assert!(target_ty.is_float());
        self.add(Data { un_op: val }, Tag::CastFloat, target_ty)
    }

    pub fn build_cast_int_to_float(&mut self, val: Ref, target_ty: IrType) -> Ref {
        debug_assert!(target_ty.is_float());
        self.add(Data { un_op: val }, Tag::CastIntToFloat, target_ty)
    }

    pub fn build_cast_float_to_int(&mut self, val: Ref, target_ty: IrType) -> Ref {
        debug_assert!(target_ty.is_int());
        self.add(Data { un_op: val }, Tag::CastFloatToInt, target_ty)
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
        self.add_unused(Tag::Asm, Data { asm: (extra, asm_str.len() as u16, count as u16) });
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
