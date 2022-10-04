use std::fmt;

use color_format::cwrite;

use crate::help::write_delimited_with;

use super::{TypeTableIndex, Ref, SymbolKey, BlockIndex, typing::FinalTypeTable};


#[derive(Debug, Clone, Copy)]
pub struct Instruction {
    pub data: Data,
    pub tag: Tag,
    pub ty: TypeTableIndex,
    pub used: bool
}
pub struct InstructionDisplay<'a> {
    inst: &'a Instruction,
    extra: &'a [u8],
    types: &'a FinalTypeTable,
}
impl Instruction {
    pub fn display<'a>(&'a self, extra: &'a [u8], types: &'a FinalTypeTable) -> InstructionDisplay<'a> {
        InstructionDisplay { inst: self, extra, types }
    }

    fn display_data(&self, f: &mut fmt::Formatter<'_>, extra: &[u8], types: &FinalTypeTable) -> fmt::Result {
        let write_ref = |f: &mut fmt::Formatter<'_>, r: Ref| {
            if let Some(val) = r.into_val() {
                cwrite!(f, "#y<{}>", val)
            } else {
                cwrite!(f, "#c<%{}>", r.into_ref().unwrap())
            }
        };
        unsafe { match self.tag.union_data_type() {
            DataVariant::Int => cwrite!(f, "#y<{}>", self.data.int),
            DataVariant::Int32 => cwrite!(f, "#y<{}>", self.data.int32),
            DataVariant::Block => cwrite!(f, "{}", self.data.block),
            DataVariant::LargeInt => {
                let bytes = &extra[
                    self.data.extra as usize
                    .. (self.data.extra + 16) as usize
                ];
                let mut bytes_arr = [0; 16];
                bytes_arr.copy_from_slice(bytes);
                cwrite!(f, "#y<{}>", u128::from_le_bytes(bytes_arr))
            }
            DataVariant::String => {
                let string = String::from_utf8_lossy(&extra[
                    self.data.extra_len.0 as usize
                    .. (self.data.extra_len.0 + self.data.extra_len.1) as usize
                ]);
                cwrite!(f, "#y<{:?}>", string)
            }
            DataVariant::Call => {
                let start = self.data.extra_len.0 as usize;
                let mut bytes = [0; 8];
                bytes.copy_from_slice(&extra[start..start+8]);
                let func = SymbolKey(u64::from_le_bytes(bytes));
                let refs = (0..self.data.extra_len.1).map(|i| {
                    let mut ref_bytes = [0; 4];
                    let begin = 8 + start + (4 * i) as usize;
                    ref_bytes.copy_from_slice(&extra[begin..begin+4]);
                    Ref::from_bytes(ref_bytes)
                });
                cwrite!(f, "#r<f{}>(", func.0)?;
                write_delimited_with(f, refs, |f, r| write_ref(f, r), ", ")?;
                cwrite!(f, ")")
            }
            DataVariant::ExtraBranchRefs => {
                for i in 0..self.data.extra_len.1 {
                    if i != 0 {
                        cwrite!(f, ", ")?;
                    }
                    let mut current_bytes = [0; 4];
                    let begin = (self.data.extra_len.0 + i * 8) as usize;
                    current_bytes.copy_from_slice(&extra[begin..begin + 4]);
                    let block = u32::from_le_bytes(current_bytes);
                    current_bytes.copy_from_slice(&extra[begin + 4 .. begin + 8]);
                    current_bytes.copy_from_slice(&extra[begin + 4 .. begin + 8]);
                    let r = Ref::from_bytes(current_bytes);
                    cwrite!(f, "[")?;
                    cwrite!(f, "#b!<b{}>, ", block)?;
                    write_ref(f, r)?;
                    cwrite!(f, "]")?;
                }
                Ok(())
            }
            DataVariant::Float => cwrite!(f, "#y<{}>", self.data.float),
            DataVariant::Symbol => cwrite!(f, "f#m<{}>", self.data.symbol.0),
            DataVariant::TraitFunc => {
                let mut buf = [0; 8];
                buf.copy_from_slice(&extra[self.data.trait_func.0 as usize ..self.data.trait_func.0 as usize + 8]);
                
                cwrite!(f, "#m<t{}>.#m<f{}>", SymbolKey::from_bytes(buf).0, self.data.trait_func.1)
            }
            DataVariant::TypeTableIdx => {
                cwrite!(f, "#m<{}>", types[self.data.ty])
            }
            DataVariant::UnOp => write_ref(f, self.data.un_op),
            DataVariant::BinOp => {
                write_ref(f, self.data.bin_op.0)?;
                write!(f, ", ")?;
                write_ref(f, self.data.bin_op.1)
            }
            DataVariant::Branch => {
                let i = self.data.branch.1 as usize;
                let mut bytes = [0; 4];
                bytes.copy_from_slice(&extra[i..i+4]);
                let a = u32::from_le_bytes(bytes);
                bytes.copy_from_slice(&extra[i+4..i+8]);
                let b = u32::from_le_bytes(bytes);
                write_ref(f, self.data.branch.0)?;
                cwrite!(f, ", #b!<b{}> #m<or> #b!<b{}>", a, b)
            }
            DataVariant::Asm => {
                let Data { asm: (extra_idx, str_len, arg_count) } = self.data;
                let str_bytes = &extra[extra_idx as usize .. extra_idx as usize + str_len as usize];
                cwrite!(f, "#y<\"{}\">", std::str::from_utf8_unchecked(str_bytes))?;
                let expr_base = extra_idx as usize + str_len as usize;
                for i in 0..arg_count as usize {
                    write!(f, ", ")?;
                    let mut arg_bytes = [0; 4];
                    arg_bytes.copy_from_slice(&extra[expr_base + 4*i .. expr_base + 4*(i+1) ]);
                    write_ref(f, Ref::from_bytes(arg_bytes))?;
                }
                Ok(())
            }
            DataVariant::Global => cwrite!(f, "#c<##{}>", self.data.symbol.0),
            DataVariant::None => Ok(())
        }}
    }
}
impl<'a> fmt::Display for InstructionDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let InstructionDisplay { inst, extra, types } = self;
        write!(f, "{} ", inst.tag)?;
        inst.display_data(f, extra, self.types)?;
        if inst.ty.is_present() {
            match inst.tag {
                Tag::Cast => cwrite!(f, "#m!< as >")?,
                _ => cwrite!(f, " :: ")?
            };
            cwrite!(f, "#m!<{}>", types.get(inst.ty))?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Tag {
    BlockBegin,
    Ret,
    RetUndef,
    Param,

    Uninit,

    Int,
    LargeInt,
    Float,
    EnumLit,

    Func,
    TraitFunc,
    Type,
    Trait,
    LocalType,
    Module,

    Decl,
    Load,
    Store,
    String,
    Call,
    Neg,
    Not,

    Global,

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

    Member,
    Cast,

    Goto,
    Branch,
    Phi,

    Asm,
}
impl Tag {
    fn union_data_type(self) -> DataVariant {
        use DataVariant::*;
        match self {
            Tag::BlockBegin | Tag::Param => Int32,
            Tag::Uninit => None,
            Tag::Ret | Tag::Load | Tag::Neg | Tag::Not | Tag::Cast => UnOp,
            Tag::Int => Int,
            Tag::LargeInt => LargeInt,
            Tag::Float => Float,
            Tag::EnumLit | Tag::String => String,
            
            Tag::Func | Tag::Type | Tag::Trait => Symbol,
            Tag::TraitFunc => TraitFunc,
            Tag::LocalType | Tag::Decl => TypeTableIdx,
            Tag::Module => Int,

            Tag::RetUndef => None,
            Tag::Call => Call,
            Tag::Global => Global,
            Tag::Store | Tag::Add | Tag::Sub | Tag::Mul | Tag::Div | Tag::Mod
            | Tag::Or | Tag::And    
            | Tag::Eq | Tag::NE | Tag::LT | Tag::GT | Tag::LE | Tag::GE | Tag::Member => BinOp,
            Tag::Goto => Block,
            Tag::Branch => Branch,
            Tag::Phi => ExtraBranchRefs,
            Tag::Asm => Asm,
        }
    }

    pub fn is_untyped(self) -> bool {
        matches!(self,
            Tag::BlockBegin | Tag::Ret | Tag::RetUndef
            | Tag::Store | Tag::Goto | Tag::Branch | Tag::Asm
        )
    }
    pub fn is_usable(self) -> bool {
        !matches!(self,
            Tag::BlockBegin | Tag::Ret | Tag::RetUndef
            | Tag::Store | Tag::Goto | Tag::Branch | Tag::Asm
        )
    }
    pub fn is_terminator(self) -> bool {
        matches!(self, Tag::Goto | Tag::Branch | Tag::Ret | Tag::RetUndef)
    }
}
impl fmt::Display for Tag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        cwrite!(f, "#b!<{:?}>", self)
    }
}

/// forces size of data to be 8 bytes
const _FORCE_DATA_SIZE: u64 = unsafe { std::mem::transmute(Data { int: 0 }) };

#[derive(Clone, Copy)]
pub union Data {
    pub int32: u32,
    pub int: u64,
    pub extra: u32,
    pub extra_len: (u32, u32),
    pub ty: TypeTableIndex,
    pub float: f64,
    pub un_op: Ref,
    pub bin_op: (Ref, Ref),
    pub branch: (Ref, u32),
    pub asm: (u32, u16, u16), // extra_index, length of string, amount of arguments
    pub symbol: SymbolKey,
    pub trait_func: (u32, u32), // extra_index for SymbolKey, func index in trait
    pub none: (),
    pub block: BlockIndex
}
impl fmt::Debug for Data {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", unsafe { self.int })
    }
}

#[derive(Clone, Copy)]
enum DataVariant {
    Int,
    Int32,
    LargeInt,
    TypeTableIdx,
    Symbol,
    TraitFunc,
    Block,
    Branch,
    String,
    Call,
    ExtraBranchRefs,
    Float,
    UnOp,
    BinOp,
    Asm,
    Global,
    None,
}
