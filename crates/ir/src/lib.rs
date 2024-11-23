#![feature(variant_count)]

use color_format::*;
use std::{
    collections::BTreeMap,
    fmt,
    ops::{Index, IndexMut, Range},
};

pub mod builder;
pub mod display;
/// helper functions for folding constants
pub mod fold;
/// machine code ir representation that is generic over the ISA
pub mod mc;
/// optimizations that operate on the ir
pub mod optimize;
/// Verify that a module or function is correctly constructed.
pub mod verify;

mod bitmap;
mod block_graph;
mod const_value;
mod eval;
mod instruction;
mod ir_types;
mod layout;

pub use bitmap::Bitmap;
pub use block_graph::BlockGraph;
pub use const_value::ConstValue;
pub use eval::{eval, EmptyEnv, Environment, Error, StackMem, Val, BACKWARDS_JUMP_LIMIT};
pub use instruction::{Data, Instruction, Tag};
pub use ir_types::{IrType, IrTypes, TypeRef, TypeRefs};
pub use layout::{offset_in_tuple, type_layout, Layout};

pub struct Module {
    pub name: String,
    pub funcs: Vec<Function>,
    pub globals: Vec<Global>,
}
impl Index<FunctionId> for Module {
    type Output = Function;

    fn index(&self, index: FunctionId) -> &Self::Output {
        &self.funcs[index.0 as usize]
    }
}
impl IndexMut<FunctionId> for Module {
    fn index_mut(&mut self, index: FunctionId) -> &mut Self::Output {
        &mut self.funcs[index.0 as usize]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FunctionId(pub u64);
impl FunctionId {
    pub fn to_bytes(self) -> [u8; 8] {
        self.0.to_le_bytes()
    }
    pub fn from_bytes(bytes: [u8; 8]) -> Self {
        Self(u64::from_le_bytes(bytes))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GlobalId(pub u64);
impl fmt::Display for GlobalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        cwrite!(f, "#m<global {}>", self.0)
    }
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub types: IrTypes,
    pub params: TypeRefs,
    pub varargs: bool,
    pub return_type: IrType,
    pub ir: Option<FunctionIr>,
}

#[derive(Debug)]
pub struct FunctionIr {
    pub inst: Vec<Instruction>,
    pub extra: Vec<u8>,
    blocks: Vec<BlockInfo>,
    // Map of indices into the inst list for each start position, includes block argument
    // instructions
    block_indices: BTreeMap<u32, BlockIndex>,
}
impl FunctionIr {
    pub fn get_ref_ty(&self, r: Ref, types: &IrTypes) -> IrType {
        match r.into_val() {
            Some(RefVal::True | RefVal::False) => IrType::U1,
            Some(RefVal::Unit) => IrType::Unit,
            Some(RefVal::Undef) => todo!(), // maybe remove undef because it's untyped
            None => types[self.inst[r.into_ref().unwrap() as usize].ty],
        }
    }

    pub fn get_block_args(&self, block: BlockIndex) -> BlockArgs {
        let info = &self.blocks[block.0 as usize];
        BlockArgs {
            start: info.start - info.arg_count,
            count: info.arg_count,
        }
    }

    pub fn get_block_range(&self, block: BlockIndex) -> Range<u32> {
        let info = &self.blocks[block.idx() as usize];
        info.start..info.start + info.len
    }

    pub fn get_inst(&self, idx: u32) -> Instruction {
        self.inst[idx as usize]
    }

    pub fn total_inst_count(&self) -> u32 {
        self.inst.len() as u32
    }

    pub fn get_block<'a>(
        &'a self,
        block: BlockIndex,
    ) -> impl 'a + ExactSizeIterator<Item = (u32, Instruction)> {
        let info = &self.blocks[block.idx() as usize];
        (info.start..info.start + info.len).map(|i| (i, self.inst[i as usize]))
    }

    pub fn get_block_from_index(&self, index: u32) -> BlockIndex {
        *self
            .block_indices
            .range(..=index)
            .next_back()
            .unwrap_or_else(|| panic!("Block for index {index} not found"))
            .1
    }

    pub fn blocks(&self) -> impl ExactSizeIterator<Item = BlockIndex> {
        (0..self.blocks.len() as _).map(BlockIndex)
    }

    pub fn replace(&mut self, idx: u32, inst: Instruction) {
        self.inst[idx as usize] = inst;
    }

    pub fn delete(&mut self, idx: u32) {
        debug_assert_ne!(
            self.inst[idx as usize].tag,
            Tag::BlockArg,
            "don't delete BlockArgs"
        );
        self.inst[idx as usize] = Instruction::NOTHING;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockInfo {
    arg_count: u32,
    start: u32,
    len: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockArgs {
    start: u32,
    count: u32,
}
impl BlockArgs {
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    pub fn count(self) -> usize {
        self.count as usize
    }

    pub fn nth(&self, index: u32) -> Ref {
        assert!(
            index < self.count,
            "Block arg {index} out of range, there are only {} args",
            self.count
        );
        Ref::index(self.start + index)
    }

    pub fn iter(self) -> impl ExactSizeIterator<Item = u32> {
        self.start..self.start + self.count
    }

    pub fn range(self) -> Range<usize> {
        self.start as usize..self.start as usize + self.count as usize
    }
}

pub struct Global {
    pub name: String,
    pub types: IrTypes,
    pub ty: IrType,
    pub value: ConstValue,
}

const INDEX_OFFSET: u32 = std::mem::variant_count::<RefVal>() as u32;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Ref(u32);
impl Ref {
    pub const UNDEF: Self = Self::val(RefVal::Undef);
    pub const UNIT: Self = Self::val(RefVal::Unit);

    pub const fn val(val: RefVal) -> Self {
        Self(val as u32)
    }

    pub const fn bool(b: bool) -> Self {
        Self::val(if b { RefVal::True } else { RefVal::False })
    }

    pub fn index(idx: u32) -> Self {
        Self(INDEX_OFFSET + idx)
    }
    pub fn is_val(self) -> bool {
        self.0 < INDEX_OFFSET
    }
    pub fn into_val(self) -> Option<RefVal> {
        self.is_val()
            .then(|| unsafe { std::mem::transmute(self.0 as u8) })
    }
    pub fn is_ref(self) -> bool {
        !self.is_val()
    }
    pub fn into_ref(self) -> Option<u32> {
        self.is_ref().then(|| self.0 - INDEX_OFFSET)
    }

    pub fn to_bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }

    pub fn from_bytes(b: [u8; 4]) -> Self {
        Self(u32::from_le_bytes(b))
    }
}
impl fmt::Debug for Ref {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(val) = self.into_val() {
            write!(f, "Val({val})")
        } else if let Some(r) = self.into_ref() {
            write!(f, "Ref({r})")
        } else {
            unreachable!()
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum RefVal {
    True,
    False,
    Unit,
    Undef,
}
impl fmt::Display for RefVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RefVal::True => write!(f, "true"),
            RefVal::False => write!(f, "false"),
            //RefVal::Zero => write!(f, "0"),
            //RefVal::One => write!(f, "1"),
            RefVal::Unit => write!(f, "()"),
            RefVal::Undef => write!(f, "undef"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BlockIndex(u32);
impl block_graph::Block for BlockIndex {
    const ENTRY: Self = Self::ENTRY;

    fn from_raw(value: u32) -> Self {
        Self(value)
    }

    fn idx(self) -> usize {
        self.0 as usize
    }
}
impl BlockIndex {
    pub const ENTRY: Self = Self(0);
    pub const MISSING: Self = Self(u32::MAX);

    pub fn bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }
    pub fn from_bytes(bytes: [u8; 4]) -> Self {
        Self(u32::from_le_bytes(bytes))
    }
    pub fn idx(self) -> u32 {
        self.0
    }
}
impl From<u32> for BlockIndex {
    fn from(value: u32) -> Self {
        Self(value)
    }
}
impl fmt::Display for BlockIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        cwrite!(f, "#b<b{}>", self.0)
    }
}
