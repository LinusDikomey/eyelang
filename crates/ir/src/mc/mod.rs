mod regalloc;

pub use regalloc::regalloc;

use std::fmt;
use std::ops::BitAnd;
use std::ops::Not;
use std::usize;

use crate::FunctionId;

pub struct MachineIR<I: Instruction> {
    pub insts: Vec<InstructionStorage<I>>,
    next_virtual: u64,
}
impl<I: Instruction> MachineIR<I> {
    pub fn new() -> Self {
        Self {
            insts: Vec::new(),
            next_virtual: 0,
        }
    }

    #[cfg_attr(debug_assertions, track_caller)]
    pub fn inst<const N: usize>(&mut self, inst: I, operands: [Operand<I::Register>; N]) {
        #[cfg(debug_assertions)]
        {
            let expected = inst.ops();
            let mut found = [OpType::None; 4];
            found[..N].copy_from_slice(&operands.map(|op| op.op_type()));
            if expected != found {
                panic!("invalid operands to instruction {}", inst.to_str());
            }
        }
        let mut all_operands = [0; 4];
        all_operands[..operands.len()].copy_from_slice(&operands.map(|op| op.encode()));
        self.insts.push(InstructionStorage {
            inst,
            ops: all_operands,
            implicit_dead: I::Register::NO_BITS,
        });
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
}
impl<I: Instruction> fmt::Display for MachineIR<I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn write_op<I: Instruction>(
            f: &mut fmt::Formatter,
            (op_value, ty): (u64, OpType),
            pad_to: usize,
        ) -> fmt::Result {
            let op = Operand::<I::Register>::decode(op_value, ty);
            let dead = matches!(op, Operand::Reg(_) | Operand::VReg(_)) && op_value & DEAD_BIT != 0;
            let dead = if dead { "!" } else { "" };
            let len = op.printed_len() + dead.len();
            let padding = pad_to.saturating_sub(len);
            for _ in 0..padding {
                write!(f, " ")?;
            }
            write!(f, " {dead}{}", op)?;
            Ok(())
        }
        for inst in &self.insts {
            write!(f, "  ")?;
            let ops = inst
                .ops
                .iter()
                .copied()
                .zip(inst.inst.ops())
                .take_while(|&(_, ty)| ty != OpType::None)
                .zip(inst.inst.op_usage());
            let mut first = true;
            let mut add_comma = false;
            for (op, usage) in ops {
                if first {
                    first = false;
                    if usage == OpUsage::Use {
                        write!(f, "{}", inst.inst.to_str())?;
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
    pub fn decode_ops(&self) -> impl Iterator<Item = (Operand<I::Register>, OpUsage)> {
        self.inst
            .ops()
            .into_iter()
            .take_while(|&op| op != OpType::None)
            .zip(self.ops)
            .zip(self.inst.op_usage())
            .map(|((ty, val), usage)| (Operand::<I::Register>::decode(val, ty), usage))
    }

    pub fn reg_ops_mut(&mut self) -> impl Iterator<Item = (&mut u64, OpUsage)> {
        self.inst
            .ops()
            .into_iter()
            .take_while(|&op| op != OpType::None)
            .zip(self.ops.iter_mut())
            .zip(self.inst.op_usage())
            .filter_map(|((ty, v), usage)| (ty == OpType::Reg).then_some((v, usage)))
    }
}

pub trait Instruction: Copy {
    type Register: Register;

    fn to_str(self) -> &'static str;
    fn ops(self) -> [OpType; 4];
    fn op_usage(self) -> [OpUsage; 4];
    fn implicit_uses(self) -> &'static [Self::Register];
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
pub enum Operand<R: Register> {
    Reg(R),
    VReg(VReg),
    Imm(u64),
    Func(FunctionId),
    None,
}
impl<R: Register> Operand<R> {
    pub fn op_type(&self) -> OpType {
        match self {
            Self::Reg(_) | Self::VReg(_) => OpType::Reg,
            Self::Imm(_) => OpType::Imm,
            Self::Func(_) => OpType::Func,
            Self::None => OpType::None,
        }
    }

    pub fn encode(&self) -> u64 {
        match self {
            Self::Reg(r) => (1 << 63) | r.encode() as u64,
            &Self::VReg(r) => r.0,
            &Self::Imm(value) => value,
            Self::Func(id) => id.0,
            Self::None => 0,
        }
    }

    pub fn decode(value: u64, ty: OpType) -> Self {
        match ty {
            OpType::None => Self::None,
            OpType::Reg => match decode_reg(value) {
                RegType::Reg(r) => Self::Reg(r),
                RegType::Virtual(v) => Self::VReg(v),
            },
            OpType::Mem => todo!(),
            OpType::Imm => Self::Imm(value),
            OpType::Func => Self::Func(FunctionId(value)),
        }
    }

    /// Get the number of characters the fmt::Display implementation will print. Used for padding.
    pub fn printed_len(self) -> usize {
        match self {
            Operand::Reg(r) => r.to_str().len(),
            Operand::VReg(n) => (u64::checked_ilog10(n.0).unwrap_or_default() + 2) as usize,
            Operand::Imm(n) => (u64::checked_ilog10(n).unwrap_or_default() + 1) as usize,
            Operand::Func(f) => (u64::checked_ilog10(f.0).unwrap_or_default() + 4) as usize,
            Operand::None => 0,
        }
    }
}
impl<R: Register> fmt::Display for Operand<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Reg(r) => write!(f, "{}", r.to_str()),
            Operand::VReg(n) => write!(f, "%{}", n.0),
            Operand::Imm(value) => write!(f, "{value}"),
            Operand::Func(func) => write!(f, "<#{}>", func.0),
            Operand::None => Ok(()),
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

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum OpType {
    None,
    Reg,
    Mem,
    Imm,
    Func,
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
    S2,
    S4,
    S8,
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VReg(u64);
impl VReg {
    pub fn op<R: Register>(self) -> Operand<R> {
        Operand::VReg(self)
    }
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
    ($name: ident $register: ident $($variant: ident $($op: ident: $use_ty: ident ),* $(!implicit $($implicit_reg: ident)*)? ;)*) => {
        #[rustfmt::skip]
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        pub enum $name {
            $($variant, )*
        }

        impl $crate::mc::Instruction for $name {
            type Register = $register;

            fn to_str(self) -> &'static str {
                match self {
                    $(Self::$variant => stringify!($variant),)*
                }
            }

            fn ops(self) -> [$crate::mc::OpType; 4] {
                let mut ops = [$crate::mc::OpType::None; 4];
                let inst_ops: &[$crate::mc::OpType] = match self {
                    $(Self::$variant => &[$($crate::mc::OpType::$op,)*],)*
                };
                for (p, op) in ops.iter_mut().zip(inst_ops) {
                    *p = *op;
                }
                ops
            }

            fn op_usage(self) -> [$crate::mc::OpUsage; 4] {
                let mut uses = [$crate::mc::OpUsage::Def; 4];
                let inst_uses: &[$crate::mc::OpUsage] = match self {
                    $(Self::$variant => &[$($crate::mc::OpUsage::$use_ty),*],)*
                };
                uses[..inst_uses.len()].copy_from_slice(inst_uses);
                uses
            }

            fn implicit_uses(self) -> &'static [$register] {
                match self {
                    $(Self::$variant => &[$($($register::$implicit_reg,)*)?],)*
                }
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
                assert!(value < $crate::mc::ident_count!($($($variant)*)*));
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
