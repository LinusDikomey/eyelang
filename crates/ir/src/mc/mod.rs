mod builder;
mod regalloc;

pub use builder::BlockBuilder;
pub use regalloc::regalloc;

use std::fmt;
use std::ops::BitAnd;
use std::ops::Not;
use std::usize;

use crate::FunctionId;

pub struct MachineIR<I: Instruction> {
    insts: Vec<InstructionStorage<I>>,
    blocks: Vec<BlockInfo>,
    next_virtual: u64,
    stack_slots: Vec<StackSlot>,
    stack_offset: u64,
}
impl<I: Instruction> MachineIR<I> {
    pub fn new() -> Self {
        Self {
            insts: Vec::new(),
            blocks: vec![BlockInfo {
                start: 0,
                len: 0,
                successors: Vec::new(),
            }],
            next_virtual: 0,
            stack_slots: Vec::new(),
            stack_offset: 0,
        }
    }

    pub fn create_block(&mut self) -> MirBlock {
        let block = MirBlock(self.blocks.len().try_into().expect("too many blocks"));
        self.blocks.push(BlockInfo {
            start: 0,
            len: 0,
            successors: Vec::new(),
        });
        block
    }

    pub fn begin_block<'a>(&'a mut self, block: MirBlock) -> BlockBuilder<'a, I> {
        let info = &mut self.blocks[block.0 as usize];
        debug_assert!(
            info.start == 0 && info.len == 0,
            "block has already been created"
        );
        info.start = self.insts.len() as u32;
        BlockBuilder { mir: self, block }
    }

    pub fn block_insts(&self, block: MirBlock) -> &[InstructionStorage<I>] {
        let block = &self.blocks[block.0 as usize];
        &self.insts[block.start as usize..block.start as usize + block.len as usize]
    }

    pub fn block_successors(&self, block: MirBlock) -> &[MirBlock] {
        &self.blocks[block.0 as usize].successors
    }

    pub fn block_count(&self) -> u32 {
        self.blocks.len() as _
    }

    pub fn replace_operand(&mut self, index: u32, operand_index: usize, op: Op<I::Register>) {
        let index = index as usize;
        #[cfg(debug_assertions)]
        {
            let expected = self.insts[index].inst.ops()[operand_index];
            if expected != op.op_type() {
                panic!(
                    "replaced instruction operand {operand_index} of {} \
                    with invalid type {:?}, expected {:?}",
                    self.insts[index].inst.to_str(),
                    op.op_type(),
                    expected
                );
            }
        }
        self.insts[index].ops[operand_index] = op.encode();
    }

    /// creates a fresh virtual register
    pub fn reg(&mut self) -> VReg {
        let r = self.next_virtual;
        assert!(r & (1 << 63) == 0, "too many virtual registers created");
        self.next_virtual += 1;
        VReg(r)
    }

    pub fn virtual_register_count(&self) -> usize {
        self.next_virtual as usize
    }

    /// creates a new stack slot and returns the slot's offset. On targets where the stack grows
    /// down, the offset should be subtracted from the base pointer.
    pub fn create_stack_slot(&mut self, layout: Layout) -> u64 {
        if layout.size == 0 {
            return 0;
        }
        let misalignment = self.stack_offset % layout.align.get();
        if misalignment != 0 {
            self.stack_offset += layout.align.get() - misalignment;
        }
        let offset = self.stack_offset;
        self.stack_slots.push(StackSlot {
            offset,
            size: layout.size,
        });
        self.stack_offset += layout.size;
        offset
    }

    /// gets the current offset of the stack required for storing all created stack slots
    pub fn stack_offset(&self) -> u64 {
        self.stack_offset
    }
}
impl<I: Instruction> fmt::Display for MachineIR<I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn write_op<I: Instruction>(
            f: &mut fmt::Formatter,
            (op_value, ty): (u64, OpType),
            pad_to: usize,
        ) -> fmt::Result {
            let op = Op::<I::Register>::decode(op_value, ty);
            let dead = matches!(op, Op::Reg(_) | Op::VReg(_)) && op_value & DEAD_BIT != 0;
            let dead = if dead { "!" } else { "" };
            let len = op.printed_len() + dead.len();
            let padding = pad_to.saturating_sub(len);
            for _ in 0..padding {
                write!(f, " ")?;
            }
            write!(f, " {dead}{}", op)?;
            Ok(())
        }
        for (_, block) in self.blocks.iter().zip((0..).map(MirBlock)) {
            writeln!(f, "  bb{}:", block.0)?;
            for inst in self.block_insts(block) {
                write!(f, "  ")?;
                let ops = inst
                    .ops
                    .iter()
                    .copied()
                    .zip(inst.inst.ops())
                    .take_while(|&(_, ty)| ty != OpType::Non)
                    .zip(inst.inst.op_usage());
                let mut first = true;
                let mut add_comma = false;
                for (op, usage) in ops {
                    if first {
                        first = false;
                        if usage == OpUsage::Use {
                            write!(f, "        {}", inst.inst.to_str())?;
                        } else {
                            write_op::<I>(f, op, 4)?;
                            write!(f, " = {}", inst.inst.to_str())?;
                            if usage == OpUsage::Def {
                                continue;
                            }
                        }
                    }
                    if add_comma {
                        write!(f, ",")?;
                    }
                    add_comma = true;
                    write_op::<I>(f, op, 4)?;
                }
                if first {
                    write!(f, "        {}", inst.inst.to_str())?;
                }
                let implicit = inst.inst.implicit_uses();
                if !implicit.is_empty() {
                    write!(f, " implicit")?;
                    for &reg in implicit {
                        let dead = if reg.get_bit(&inst.implicit_dead) {
                            "!"
                        } else {
                            ""
                        };
                        write!(f, " {dead}{}", reg.to_str())?;
                    }
                }
                writeln!(f)?;
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
pub struct InstructionStorage<I: Instruction> {
    pub inst: I,
    pub ops: [u64; 4],
    pub implicit_dead: <I::Register as Register>::RegisterBits,
}
impl<I: Instruction> InstructionStorage<I> {
    pub fn decode_ops(&self) -> impl Iterator<Item = (Op<I::Register>, OpUsage)> {
        self.inst
            .ops()
            .into_iter()
            .take_while(|&op| op != OpType::Non)
            .zip(self.ops)
            .zip(self.inst.op_usage())
            .map(|((ty, val), usage)| (Op::<I::Register>::decode(val, ty), usage))
    }

    pub fn reg_ops_mut(&mut self) -> impl Iterator<Item = (&mut u64, OpUsage)> {
        self.inst
            .ops()
            .into_iter()
            .take_while(|&op| op != OpType::Non)
            .zip(self.ops.iter_mut())
            .zip(self.inst.op_usage())
            .filter_map(|((ty, v), usage)| (ty == OpType::Reg).then_some((v, usage)))
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MirBlock(pub u32);
impl MirBlock {
    pub const ENTRY: Self = Self(0);
}

struct BlockInfo {
    start: u32,
    len: u32,
    successors: Vec<MirBlock>,
}

pub trait Instruction: Copy {
    type Register: Register;

    fn to_str(self) -> &'static str;
    fn ops(self) -> [OpType; 4];
    fn op_usage(self) -> [OpUsage; 4];
    fn implicit_defs(self) -> &'static [Self::Register];
    fn implicit_uses(self) -> &'static [Self::Register];
    fn is_copy(self) -> bool;
}
pub trait Register: 'static + Copy {
    const DEFAULT: Self;
    type RegisterBits: Copy + BitAnd<Output = Self::RegisterBits> + Not<Output = Self::RegisterBits>;
    const NO_BITS: Self::RegisterBits;
    const ALL_BITS: Self::RegisterBits;

    fn to_str(self) -> &'static str;
    fn encode(self) -> u32;
    fn decode(value: u32) -> Self;

    fn get_bit(self, bits: &Self::RegisterBits) -> bool;
    fn set_bit(self, bits: &mut Self::RegisterBits, bit: bool);
    fn allocate_reg(free_bits: Self::RegisterBits, class: SizeClass) -> Option<Self>;
}

#[derive(Debug, Clone, Copy)]
pub enum Op<R: Register> {
    Reg(R),
    VReg(VReg),
    Imm(u64),
    Block(MirBlock),
    Func(FunctionId),
    None,
}
impl<R: Register> Op<R> {
    pub fn op_type(&self) -> OpType {
        match self {
            Self::Reg(_) | Self::VReg(_) => OpType::Reg,
            Self::Imm(_) => OpType::Imm,
            Self::Block(_) => OpType::Blk,
            Self::Func(_) => OpType::Fun,
            Self::None => OpType::Non,
        }
    }

    pub fn encode(&self) -> u64 {
        match self {
            Self::Reg(r) => (1 << 63) | r.encode() as u64,
            &Self::VReg(r) => r.0,
            &Self::Imm(value) => value,
            Self::Block(block) => block.0 as u64,
            Self::Func(id) => id.0,
            Self::None => 0,
        }
    }

    pub fn decode(value: u64, ty: OpType) -> Self {
        match ty {
            OpType::Non => Self::None,
            OpType::Reg => match decode_reg(value) {
                RegType::Reg(r) => Self::Reg(r),
                RegType::Virtual(v) => Self::VReg(v),
            },
            OpType::Mem => todo!(),
            OpType::Imm => Self::Imm(value),
            OpType::Blk => Self::Block(MirBlock(value as u32)),
            OpType::Fun => Self::Func(FunctionId(value)),
        }
    }

    /// Get the number of characters the fmt::Display implementation will print. Used for padding.
    pub fn printed_len(self) -> usize {
        match self {
            Op::Reg(r) => r.to_str().len(),
            Op::VReg(n) => (u64::checked_ilog10(n.0).unwrap_or_default() + 2) as usize,
            Op::Imm(n) => {
                let n = n as i64;
                let mut signed = false;
                let n = if n < 0 {
                    signed = true;
                    n.checked_neg().map_or(i64::MAX as u64 + 1, |n| n as u64)
                } else {
                    n as u64
                };
                (u64::checked_ilog10(n).unwrap_or_default() + 1 + signed as u32) as usize
            }
            Op::Block(b) => (u32::checked_ilog10(b.0).unwrap_or_default() + 3) as usize,
            Op::Func(f) => (u64::checked_ilog10(f.0).unwrap_or_default() + 4) as usize,
            Op::None => 0,
        }
    }
}
impl<R: Register> fmt::Display for Op<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Op::Reg(r) => write!(f, "{}", r.to_str()),
            Op::VReg(n) => write!(f, "%{}", n.0),
            &Op::Imm(value) => write!(f, "{}", value as i64),
            Op::Block(b) => write!(f, "bb{}", b.0),
            Op::Func(func) => write!(f, "<#{}>", func.0),
            Op::None => Ok(()),
        }
    }
}

pub enum RegType<R> {
    Reg(R),
    Virtual(VReg),
}
pub fn decode_reg<R: Register>(r: u64) -> RegType<R> {
    if r & (1 << 63) != 0 {
        RegType::Reg(R::decode(r as u32))
    } else {
        RegType::Virtual(VReg(r & !DEAD_BIT))
    }
}

pub const PHYSICAL_BIT: u64 = 1 << 63;
pub const DEAD_BIT: u64 = 1 << 62;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpType {
    Non,
    Reg,
    Mem,
    Imm,
    Blk,
    Fun,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpUsage {
    Def = 0b01,
    Use = 0b10,
    DefUse = 0b11,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SizeClass {
    S1,
    S8,
    S16,
    S32,
    S64,
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VReg(u64);
impl VReg {
    pub fn op<R: Register>(self) -> Op<R> {
        Op::VReg(self)
    }
}

pub struct StackSlot {
    pub offset: u64,
    pub size: u64,
}

#[macro_export]
macro_rules! ident_count {
    () => {
        0
    };
    ($i: ident $($rest: ident)*) => {
        1 + $crate::mc::ident_count!($($rest)*)
    };
}
pub use crate::ident_count;

#[macro_export]
macro_rules! first_reg {
    () => {
        compile_error!("Register list can't be empty");
    };
    ($id: ident $($rest: ident)*) => {
        Self::$id
    };
}
pub use crate::first_reg;

#[macro_export]
macro_rules! inst {
    ($name: ident $register: ident $($variant: ident $($op: ident: $use_ty: ident ),* $(!implicit_def $($implicit_def: ident)*)? $(!implicit $($implicit: ident)*)? ;)*) => {
        #[rustfmt::skip]
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        pub enum $name {
            /// special meta-instruction that all ISAs contain. It represents a copy of an
            /// arbitrary register to another. Use this instead of specific mov instructions to
            /// make the register allocator aware of potential elidable copies
            Copy = 0,
            $($variant, )*
        }

        impl $crate::mc::Instruction for $name {
            type Register = $register;

            fn to_str(self) -> &'static str {
                match self {
                    Self::Copy => "copy",
                    $(Self::$variant => stringify!($variant),)*
                }
            }

            fn ops(self) -> [$crate::mc::OpType; 4] {
                let mut ops = [$crate::mc::OpType::Non; 4];
                let inst_ops: &[$crate::mc::OpType] = match self {
                    Self::Copy => &[$crate::mc::OpType::Reg, $crate::mc::OpType::Reg],
                    $(Self::$variant => &[$($crate::mc::OpType::$op,)*],)*
                };
                ops[..inst_ops.len()].copy_from_slice(inst_ops);
                ops
            }

            fn op_usage(self) -> [$crate::mc::OpUsage; 4] {
                let mut uses = [$crate::mc::OpUsage::Def; 4];
                let inst_uses: &[$crate::mc::OpUsage] = match self {
                    Self::Copy => &[$crate::mc::OpUsage::Def, $crate::mc::OpUsage::Use],
                    $(Self::$variant => &[$($crate::mc::OpUsage::$use_ty),*],)*
                };
                uses[..inst_uses.len()].copy_from_slice(inst_uses);
                uses
            }

            fn implicit_defs(self) -> &'static [$register] {
                match self {
                    Self::Copy => &[],
                    $(Self::$variant => &[$($($register::$implicit_def,)*)?],)*
                }
            }

            fn implicit_uses(self) -> &'static [$register] {
                match self {
                    Self::Copy => &[],
                    $(Self::$variant => &[$($($register::$implicit,)*)?],)*
                }
            }

            fn is_copy(self) -> bool {
                self == Self::Copy
            }
        }
    };
}
pub use crate::inst;

#[macro_export]
macro_rules! registers {
    ($name: ident $bits: ident $($size: ident => $($variant: ident)*;)*) => {
        #[rustfmt::skip]
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        #[repr(u8)]
        pub enum $name {
            $($($variant,)*)*
        }

        impl $name {
            pub fn size(self) -> $crate::mc::SizeClass {
                match self {
                    $($(Self::$variant => $crate::mc::SizeClass::$size,)*)*
                }
            }
        }
        impl $crate::mc::Register for $name {
            const DEFAULT: Self = $crate::mc::first_reg!($($($variant)*)*);
            const NO_BITS: $bits = $bits::new();
            const ALL_BITS: $bits = $bits::all();
            type RegisterBits = $bits;

            fn to_str(self) -> &'static str {
                match self {
                    $($(Self::$variant => stringify!($variant),)*)*
                }
            }

            fn encode(self) -> u32 {
                self as u32
            }

            fn decode(value: u32) -> Self {
                let count = $crate::mc::ident_count!($($($variant)*)*);
                debug_assert!(value < count);
                unsafe { std::mem::transmute(value as u8) }
            }

            fn get_bit(self, bits: &$bits) -> bool {
                bits.get(self)
            }

            fn set_bit(self, bits: &mut $bits, set: bool) {
                bits.set(self, set);
            }

            fn allocate_reg(free: Self::RegisterBits, class: $crate::mc::SizeClass) -> Option<Self> {
                $(
                    if class == $crate::mc::SizeClass::$size {
                        $(if Self::$variant.get_bit(&free) {
                            return Some(Self::$variant)
                        })*
                    }
                )*
                None
            }
        }
    };
}
pub use crate::registers;
use crate::Layout;
