use crate::{
    BlockArgs, BlockIndex, BlockInfo, Data, FunctionIr, GlobalId, Instruction, Ref, Tag, TypeRefs,
};

use super::{
    ir_types::{IrType, IrTypes, TypeRef},
    FunctionId, RefVal,
};

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

    Xor,
    Rol,
    Ror,
}

#[derive(Clone, Copy, Debug)]
pub enum Terminator<'a> {
    Ret(Ref),
    Goto(BlockIndex, &'a [Ref]),
    Branch {
        cond: Ref,
        on_true: (BlockIndex, &'a [Ref]),
        on_false: (BlockIndex, &'a [Ref]),
    },
}

#[derive(Debug)]
pub struct IrBuilder<'a> {
    pub inst: Vec<Instruction>,
    current_block: u32,
    current_block_terminated: bool,
    next_block: u32,
    blocks: Vec<BlockInfo>,
    pub extra: Vec<u8>,
    pub types: &'a mut IrTypes,
}
impl<'a> IrBuilder<'a> {
    pub fn new(types: &'a mut IrTypes, params: TypeRefs) -> (Self, BlockArgs) {
        let inst = params
            .iter()
            .map(|ty| Instruction {
                tag: Tag::BlockArg,
                data: Data { none: () },
                ty,
            })
            .collect();
        (
            Self {
                inst,
                current_block: 0,
                current_block_terminated: false,
                next_block: 1,
                blocks: vec![BlockInfo {
                    arg_count: params.count,
                    start: params.count,
                    len: 0,
                }],
                extra: Vec::new(),
                types,
            },
            BlockArgs {
                start: 0,
                count: params.count,
            },
        )
    }

    /// Internal function to add an instruction. This will not add anything if `emit` is set to false.
    #[cfg_attr(debug_assertions, track_caller)]
    fn add_inst(&mut self, inst: Instruction) -> Ref {
        assert!(!self.current_block_terminated);

        let idx = Ref::index(self.inst.len() as u32);
        self.inst.push(inst);
        idx
    }

    #[cfg_attr(debug_assertions, track_caller)]
    fn add(&mut self, data: Data, tag: Tag, ty: impl Into<IdxOrTy>) -> Ref {
        debug_assert!(!self.current_block_terminated);
        let ty = self.ty(ty);
        self.add_inst(Instruction { data, tag, ty })
    }

    fn extra_data(&mut self, bytes: &[u8]) -> u32 {
        let idx = self.extra.len() as u32;
        self.extra.extend(bytes);
        idx
    }

    #[must_use = "block has to be begun somewhere"]
    pub fn create_block(&mut self) -> BlockIndex {
        let idx = BlockIndex(self.next_block);
        self.next_block += 1;
        self.blocks.push(BlockInfo {
            arg_count: 0,
            start: 0,
            len: 0,
        });
        idx
    }

    pub fn begin_block(&mut self, idx: BlockIndex) {
        self.begin_block_with_args(idx, TypeRefs::EMPTY);
    }

    pub fn begin_block_with_args(&mut self, idx: BlockIndex, args: TypeRefs) -> BlockArgs {
        debug_assert!(
            self.current_block_terminated,
            "Can't begin next block without exiting previous one"
        );
        self.current_block = idx.0;
        self.current_block_terminated = false;
        debug_assert_eq!(
            self.blocks[idx.0 as usize],
            BlockInfo {
                arg_count: 0,
                start: 0,
                len: 0
            },
            "begin_block called twice on the same block"
        );

        let block_args_start = self.inst.len() as u32;
        for arg in args.iter() {
            self.inst.push(Instruction {
                tag: Tag::BlockArg,
                data: Data { none: {} },
                ty: arg,
            });
        }
        let block_pos = self.inst.len() as u32;
        self.blocks[idx.0 as usize] = BlockInfo {
            arg_count: args.count,
            start: block_pos,
            len: 0,
        };
        BlockArgs {
            start: block_args_start,
            count: args.count,
        }
    }

    pub fn current_block(&self) -> BlockIndex {
        BlockIndex(self.current_block)
    }

    pub fn finish(self) -> FunctionIr {
        debug_assert!(
            self.current_block_terminated,
            "Last IR block wasn't terminated"
        );

        #[cfg(debug_assertions)]
        for (info, i) in self.blocks.iter().copied().zip(0..) {
            assert_ne!(info.len, 0, "block {} is empty", BlockIndex(i));
        }

        let block_indices = self
            .blocks
            .iter()
            .map(|info| info.start - info.arg_count)
            .zip((0..).map(BlockIndex))
            .collect();

        FunctionIr {
            inst: self.inst,
            extra: self.extra,
            blocks: self.blocks,
            block_indices,
        }
    }

    /// --------------------------------------------------------------
    /// -------------------- instruction builders --------------------
    /// --------------------------------------------------------------

    pub fn terminate_block(&mut self, terminator: Terminator) {
        let (tag, data) = match terminator {
            Terminator::Ret(val) => (Tag::Ret, Data { un_op: val }),
            Terminator::Goto(block, args) => {
                debug_assert!(block != BlockIndex::MISSING);
                let mut arg_iter = args.iter();
                let extra = arg_iter
                    .next()
                    .map_or(0, |arg| self.extra_data(&arg.to_bytes()));
                for arg in arg_iter {
                    self.extra_data(&arg.to_bytes());
                }
                (
                    Tag::Goto,
                    Data {
                        block_extra: (block, extra),
                    },
                )
            }
            Terminator::Branch {
                cond,
                on_true,
                on_false,
            } => {
                // TODO: track number of block args
                debug_assert!(on_true.0 != BlockIndex::MISSING);
                debug_assert!(on_false.0 != BlockIndex::MISSING);
                let branch_extra = self.extra_data(&on_true.0 .0.to_le_bytes());
                self.extra_data(&on_false.0.bytes());
                for arg in on_true.1 {
                    self.extra_data(&arg.to_bytes());
                }
                for arg in on_false.1 {
                    self.extra_data(&arg.to_bytes());
                }
                (
                    Tag::Branch,
                    Data {
                        ref_int: (cond, branch_extra),
                    },
                )
            }
        };
        self.add_inst(Instruction {
            data,
            tag,
            ty: TypeRef::NONE,
        });
        self.current_block_terminated = true;
        let block_start = self.blocks[self.current_block as usize].start;
        assert_eq!(self.blocks[self.current_block as usize].len, 0);
        let len = (self.inst.len() - block_start as usize) as u32;
        self.blocks[self.current_block as usize].len = len;
    }

    pub fn build_int(&mut self, int: u64, ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { int }, Tag::Int, ty)
    }

    pub fn build_large_int(&mut self, int: u128, int_ty: impl Into<IdxOrTy>) -> Ref {
        debug_assert!(
            int > u64::MAX as u128,
            "use build_int if the int is smaller than u64::MAX"
        );
        let extra = self.extra_data(&int.to_le_bytes());
        self.add(Data { extra }, Tag::LargeInt, int_ty)
    }

    pub fn build_float(&mut self, float: f64, float_ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { float }, Tag::Float, float_ty)
    }

    fn ty(&mut self, ty: impl Into<IdxOrTy>) -> TypeRef {
        match ty.into() {
            IdxOrTy::Idx(idx) => idx,
            IdxOrTy::Ty(ty) => self.types.add(ty),
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
        self.add(Data { bin_op: (var, val) }, Tag::Store, TypeRef::NONE);
    }

    pub fn build_string(&mut self, string: &[u8], null_terminate: bool) -> Ref {
        let extra = self.extra_data(string);
        let len = if null_terminate {
            self.extra_data(&[b'\0']);
            string.len() + 1
        } else {
            string.len()
        };
        debug_assert!(len <= u32::MAX as usize, "String is too long");
        self.add(
            Data {
                extra_len: (extra, len as u32),
            },
            Tag::String,
            IrType::Ptr,
        )
    }

    pub fn build_call(
        &mut self,
        func: FunctionId,
        args: impl IntoIterator<Item = Ref>,
        return_ty: impl Into<IdxOrTy>,
    ) -> Ref {
        let extra = self.extra_data(&func.to_bytes());
        let mut arg_count = 0;
        for arg in args {
            self.extra_data(&arg.to_bytes());
            arg_count += 1;
        }
        self.add(
            Data {
                extra_len: (extra, arg_count),
            },
            Tag::Call,
            return_ty,
        )
    }

    pub fn build_function_ptr(&mut self, function: FunctionId) -> Ref {
        self.add(Data { function }, Tag::FunctionPtr, IrType::Ptr)
    }

    pub fn build_call_ptr(
        &mut self,
        func: Ref,
        args: impl IntoIterator<Item = Ref>,
        arg_types: TypeRefs,
        return_ty: impl Into<IdxOrTy>,
    ) -> Ref {
        let extra = self.extra_data(&func.to_bytes());
        self.extra_data(&arg_types.to_bytes());
        let mut arg_count = 0;
        for arg in args {
            self.extra_data(&arg.to_bytes());
            arg_count += 1;
        }
        debug_assert_eq!(arg_count, arg_types.count);
        self.add(
            Data {
                extra_len: (extra, arg_count),
            },
            Tag::CallPtr,
            return_ty,
        )
    }

    pub fn build_neg(&mut self, val: Ref, ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { un_op: val }, Tag::Neg, ty)
    }

    pub fn build_not(&mut self, val: Ref, ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { un_op: val }, Tag::Not, ty)
    }

    pub fn build_global(&mut self, global: GlobalId, ptr_ty: impl Into<IdxOrTy>) -> Ref {
        self.add(Data { global }, Tag::Global, ptr_ty)
    }

    pub fn build_bin_op(&mut self, bin_op: BinOp, l: Ref, r: Ref, ty: impl Into<IdxOrTy>) -> Ref {
        let tag = match bin_op {
            BinOp::Add => Tag::Add,
            BinOp::Sub => Tag::Sub,
            BinOp::Mul => Tag::Mul,
            BinOp::Div => Tag::Div,
            BinOp::Mod => Tag::Rem,
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
                } else if l.into_val() == Some(RefVal::False) || r.into_val() == Some(RefVal::False)
                {
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
            BinOp::Xor => Tag::Xor,
            BinOp::Rol => Tag::Rol,
            BinOp::Ror => Tag::Ror,
        };
        self.add(Data { bin_op: (l, r) }, tag, ty)
    }

    pub fn build_member_ptr(&mut self, var: Ref, idx: u32, elem_types: TypeRefs) -> Ref {
        debug_assert!(idx < elem_types.count, "member ptr is out of bounds");
        let extra = self.extra.len() as u32;
        self.extra.extend(elem_types.to_bytes());
        self.extra.extend(idx.to_le_bytes());
        self.add(
            Data {
                ref_int: (var, extra),
            },
            Tag::MemberPtr,
            IrType::Ptr,
        )
    }

    pub fn build_member_value(&mut self, val: Ref, idx: u32, ty: impl Into<IdxOrTy>) -> Ref {
        self.add(
            Data {
                ref_int: (val, idx),
            },
            Tag::MemberValue,
            ty,
        )
    }

    pub fn build_insert_member(
        &mut self,
        tuple: Ref,
        idx: u32,
        value: Ref,
        ty: impl Into<IdxOrTy>,
    ) -> Ref {
        let i = self.extra_data(&idx.to_le_bytes());
        self.extra_data(&value.to_bytes());
        self.add(
            Data {
                ref_int: (tuple, i),
            },
            Tag::InsertMember,
            ty,
        )
    }

    pub fn build_array_index(&mut self, array_var: Ref, idx: Ref, elem_type: TypeRef) -> Ref {
        let extra = self.extra.len() as u32;
        self.extra.extend(elem_type.to_bytes());
        self.extra.extend(idx.to_bytes());
        self.add(
            Data {
                ref_int: (array_var, extra),
            },
            Tag::ArrayIndex,
            IrType::Ptr,
        )
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

    pub fn build_int_to_ptr(&mut self, val: Ref) -> Ref {
        self.add(Data { un_op: val }, Tag::IntToPtr, IrType::Ptr)
    }

    pub fn build_ptr_to_int(&mut self, val: Ref, target_ty: IrType) -> Ref {
        debug_assert!(target_ty.is_int());
        self.add(Data { un_op: val }, Tag::PtrToInt, target_ty)
    }

    /// TODO: proper semantics for asm expressions
    pub fn _build_asm(&mut self, asm_str: &str, values: impl IntoIterator<Item = Ref>) {
        assert!(
            asm_str.len() <= u16::MAX as usize,
            "inline assembly string is too long"
        );
        let extra = self.extra_data(asm_str.as_bytes());
        let mut count = 0;
        for r in values {
            self.extra_data(&r.to_bytes());
            count += 1;
        }
        assert!(
            count <= u16::MAX as usize,
            "too many arguments for inline assembly"
        );
        self.add(
            Data {
                asm: (extra, asm_str.len() as u16, count as u16),
            },
            Tag::Asm,
            TypeRef::NONE,
        );
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
