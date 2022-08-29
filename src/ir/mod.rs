use std::fmt;
use color_format::*;
use crate::dmap::DHashMap;
use crate::help::{write_delimited, write_delimited_with};
use crate::types::{Primitive, IntType, FloatType};
use typing::{TypeTable, TypeInfo, FinalTypeTable};

mod gen;
mod typing;
mod eval;

pub use gen::Symbol;
pub use gen::reduce;
pub use gen::IrBuilder;
use self::gen::ConstSymbol;
pub use self::typing::TypeTableIndex;
use self::typing::TypeTableIndices;


#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Prim(Primitive),
    Id(SymbolKey, Vec<Type>),
    Pointer(Box<Type>),
    Array(Box<(Type, u32)>),
    //TODO: takes up 24 bytes and heap allocates, maybe find a more generic solution to store all types.
    Enum(Vec<String>),
    Tuple(Vec<Type>),
    Symbol,
    /// A generic type (commonly T) that will be replaced by a concrete type in generic instantiations.
    Generic(u8),
    Invalid
}
impl Type {
    pub fn layout(&self, ctx: &gen::TypingCtx, generics: &[Type]) -> Layout {
        match self {
            Type::Prim(p) => p.layout(),
            Type::Id(key, generics) => ctx.get_type(*key).layout(ctx, generics),
            Type::Pointer(_) => Layout::PTR,
            Type::Array(b) => {
                let (ty, size) = &**b;
                ty.layout(ctx, generics).mul_size(*size as u64)
            }
            Type::Enum(variants) => Enum::layout_from_variant_count(variants.len()),
            Type::Tuple(tuple) => {
                tuple.iter().fold(Layout::ZERO, |l, ty| l.accumulate(ty.layout(ctx, generics)))
            }
            Type::Generic(idx) => generics[*idx as usize].layout(ctx, generics),
            Type::Symbol | Type::Invalid => Layout::ZERO,
        }
    }
    pub fn is_zero_sized(&self, types: &[(String, TypeDef)], generics: &[Type]) -> bool {
        match self {
            Type::Prim(p) => p.layout().size == 0,
            Type::Id(key, generics) => types[key.idx()].1.is_zero_sized(types, generics),
            Type::Pointer(_) => false,
            Type::Array(array) => {
                let (inner, size) = &**array;
                *size == 0 || inner.is_zero_sized(types, generics)
            }
            Type::Enum(variants) => variants.len() < 2,
            Type::Tuple(elems) => elems.iter().all(|ty| ty.is_zero_sized(types, generics)),
            Type::Symbol => true,
            Type::Generic(idx) => generics[*idx as usize].is_zero_sized(types, generics),
            Type::Invalid => true,
        }
    }
}

#[derive(Clone, Copy)]
pub enum TypeInfoOrIndex {
    Info(TypeInfo),
    Index(TypeTableIndex)
}
impl From<TypeInfo> for TypeInfoOrIndex {
    fn from(info: TypeInfo) -> Self {
        Self::Info(info)
    }
}
impl TypeInfoOrIndex {
    pub fn into_info(self, types: &TypeTable) -> TypeInfo {
        match self {
            TypeInfoOrIndex::Info(info) => info,
            TypeInfoOrIndex::Index(idx) => types.get_type(idx),
        }
    }
}
impl Type {
    pub fn as_info(&self, types: &mut TypeTable) -> TypeInfo {
        self.as_info_generic(types, TypeTableIndices::EMPTY).into_info(types)
    }

    pub fn as_info_generic(&self, types: &mut TypeTable, generics: TypeTableIndices) -> TypeInfoOrIndex {
        TypeInfoOrIndex::Info(match self {
            Self::Prim(p) => TypeInfo::Primitive(*p),
            Self::Id(id, ty_generics) => {
                // unfortunately this has to be allocated for borrowing reasons
                let generics = types.add_multiple(ty_generics.iter().map(|_| TypeInfo::Unknown));
                for (generic, ty) in generics.iter().zip(ty_generics) {
                    match ty.as_info_generic(types, generics) {
                        TypeInfoOrIndex::Info(info) => types.update_type(generic, info), //TODO: this might need a proper merge?
                        TypeInfoOrIndex::Index(idx) => types.point_to(generic, idx),
                    }
                }
                let generics = ty_generics.iter()
                    .map(|ty| ty.as_info_generic(types, generics))
                    .collect::<Vec<_>>();
                TypeInfo::Resolved(*id, types.add_multiple_info_or_index(generics))
            }
            Self::Pointer(inner) => {
                let inner = inner.as_info_generic(types, generics);
                TypeInfo::Pointer(types.add_info_or_idx(inner))
            }
            Self::Array(array) => {
                let (ty, count) = &**array;
                let inner = ty.as_info_generic(types, generics);
                TypeInfo::Array(Some(*count), types.add_info_or_idx(inner))
            }
            Self::Enum(variants) =>
                TypeInfo::Enum(types.add_names(variants.as_slice().iter().cloned())),
            Self::Tuple(elems) => {
                let infos = elems.iter().map(|ty| ty.as_info_generic(types, generics)).collect::<Vec<_>>();
                TypeInfo::Tuple(types.add_multiple_info_or_index(infos))
            }
            Self::Generic(idx) => {
                assert!(
                    *idx < generics.len() as u8,
                    "Not enough generics provided: index {} >= provided {}", idx, generics.len()
                );
                return TypeInfoOrIndex::Index(generics.nth(*idx as usize));
            }
            Self::Symbol => TypeInfo::Symbol,
            Self::Invalid => TypeInfo::Invalid
        })
    }
}
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Prim(p) => write!(f, "{p}"),
            Self::Id(id, generics) => {
                write!(f, "t{}", id.idx())?;
                if !generics.is_empty() {
                    write!(f, "[")?;
                    write_delimited(f, generics, ", ")?;
                    write!(f, "]")?;
                }
                Ok(())
            }
            Self::Pointer(inner) => write!(f, "*{inner}"),
            Self::Array(array) => {
                let (ty, count) = &**array;
                write!(f, "[{}; {}]", ty, count)
            }
            Self::Enum(variants) => {
                write_delimited(f, variants, " | ")?;
                Ok(())
            }
            Self::Tuple(elems) => {
                write!(f, "(")?;
                write_delimited(f, elems, ", ")?;
                write!(f, ")")
            }
            Self::Generic(idx) => write!(f, "Generic #{idx}"),
            Self::Symbol => write!(f, "[symbol]"),
            Self::Invalid => write!(f, "[invalid]"),
        }
    }
}


#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct SymbolKey(u64);
impl SymbolKey {
    pub fn idx(self) -> usize { self.0 as usize }
    pub fn bytes(self) -> [u8; 8] { self.0.to_le_bytes() }
    pub fn from_bytes(bytes: [u8; 8]) -> Self { Self(u64::from_le_bytes(bytes)) }
}

pub struct Function {
    pub name: String,
    pub header: FunctionHeader,
    pub ir: Option<FunctionIr>
}
impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        write_delimited_with(f, &self.header.params,
            |f, (name, param)| cwrite!(f, "#g<{}> #m<{}>", name, param), ", ")?;
        cwriteln!(f, ") -#> #m<{}>", self.header.return_type)?;

        if let Some(ir) = &self.ir {
            write!(f, "{ir}")?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct FunctionIr {
    pub inst: Vec<Instruction>,
    pub extra: Vec<u8>,
    pub types: FinalTypeTable,
    pub blocks: Vec<u32>,
}
impl fmt::Display for FunctionIr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, inst) in self.inst.iter().enumerate() {
            if inst.tag == Tag::BlockBegin {
                //TODO: make this purple
                cwriteln!(f, "  #m<block> #b!<b{}>:", unsafe { inst.data.int32 })?;
                continue;
            }
            if inst.used {
                cwrite!(f, "    #c<{:>4}> = ", format!("%{i}"))?;
            } else {
                write!(f, "           ")?;
            }
            cwriteln!(f, "{}", inst.display(&self.extra, &self.types))?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct FunctionHeader {
    pub params: Vec<(String, Type)>,
    pub varargs: bool,
    pub return_type: Type
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layout {
    pub size: u64,
    pub alignment: u64,
}
impl Layout {
    pub const ZERO: Self = Self { size: 0, alignment: 1 };
    pub const PTR: Self = Self { size: 8, alignment: 8 };

    pub fn align(offset: u64, alignment: u64) -> u64 {
        let misalignment = offset % alignment;
        if misalignment > 0 {
            offset + alignment - misalignment
        } else {
            offset
        }
    }
    #[must_use]
    pub fn accumulate(self, other: Self) -> Self {
        Self {
            size: Self::align(self.size, other.alignment),
            alignment: self.alignment.max(other.alignment),
        }
    }
    #[must_use]
    pub fn mul_size(self, factor: u64) -> Self {
        Self {
            size: self.size * factor,
            alignment: self.alignment,
        }
    }
}

#[derive(Debug)]
pub enum TypeDef {
    Struct(Struct),
    Enum(Enum),
    NotGenerated { generic_count: u8, generating: bool },
}
impl TypeDef {
    pub fn generic_count(&self) -> u8 {
        match self {
            TypeDef::Struct(struct_) => struct_.generic_count,
            TypeDef::Enum(enum_) => enum_.generic_count,
            Self::NotGenerated { generic_count, .. } => *generic_count
        }
    }
    pub fn layout(&self, ctx: &gen::TypingCtx, generics: &[Type]) -> Layout {
        match self {
            TypeDef::Struct(struct_) => {
                let mut alignment = 1;
                let size = struct_.members.iter()
                    .map(|(_, ty)| {
                        let layout = ty.layout(ctx, generics);
                        alignment = alignment.max(layout.alignment);
                        layout.size
                    })
                    .sum();

                Layout { size, alignment }
            }
            TypeDef::Enum(enum_) => {
                enum_.layout()
            }
            TypeDef::NotGenerated { .. }
                => panic!("layout of NotGenerated types should not be requested"),
        }
    }
    pub fn is_zero_sized(&self, types: &[(String, TypeDef)], generics: &[Type]) -> bool {
        match self {
            Self::Struct(def) => def.members.iter().all(|(_, member)| member.is_zero_sized(types, generics)),
            Self::Enum(def) => def.variants.len() < 2,
            Self::NotGenerated { .. } => unreachable!()
        }
    }
}
impl fmt::Display for TypeDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeDef::Struct(s) => write!(f, "{s}"),
            TypeDef::Enum(e) => write!(f, "{e}"),
            Self::NotGenerated { .. } => write!(f, "not generated")
        }
    }
}
#[derive(Debug, Clone)]
pub struct Struct {
    pub members: Vec<(String, Type)>,
    pub methods: DHashMap<String, SymbolKey>,
    pub generic_count: u8,
}
impl fmt::Display for Struct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (name, member) in &self.members {
            cwriteln!(f, "  #g<{}> #m<{}>", name, member)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Enum {
    pub variants: DHashMap<String, u32>,
    pub generic_count: u8,
}
impl Enum {
    pub fn layout_from_variant_count(count: usize) -> Layout {
        let size = ((count as u64 - 1).ilog2() as u64 + 1).div_ceil(8);
        let alignment = match size {
            0 | 1 => 1,
            2 => 2,
            3..=4 => 4,
            5.. => 8,
        };
        Layout { size, alignment }
    }
    pub fn layout(&self) -> Layout {
        Self::layout_from_variant_count(self.variants.len())
    }
    pub fn _bit_size(&self) -> u64 {
        (self.variants.len() as u64 - 1).ilog2() as u64 + 1
    }
    pub fn _size(&self) -> u64 {
        self._bit_size().div_ceil(8)
    }
}
impl fmt::Display for Enum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (variant, variant_val) in &self.variants {
            cwriteln!(f, "  #m<{}> = #c<{}>", variant, variant_val)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct TraitDef {
    pub functions: DHashMap<String, (u32, FunctionHeader)>
}

#[derive(Debug, Clone)]
pub enum ConstVal {
    Invalid,
    Unit,
    // FIXME: storing the value as an i128 is a problem for large values
    Int(Option<IntType>, i128),
    Float(Option<FloatType>, f64),
    String(Vec<u8>),
    EnumVariant(String),
    Bool(bool),
    Symbol(ConstSymbol),
    NotGenerated,
}
impl ConstVal {
    pub fn type_info(&self, types: &mut TypeTable) -> TypeInfo {
        match self {
            ConstVal::Invalid => TypeInfo::Invalid,
            ConstVal::Unit => TypeInfo::Primitive(Primitive::Unit),
            ConstVal::Int(ty, _) => ty.map_or(TypeInfo::Int, |ty| TypeInfo::Primitive(ty.into())),
            ConstVal::Float(ty, _) => ty.map_or(TypeInfo::Float, |ty| TypeInfo::Primitive(ty.into())),
            ConstVal::String(_) => TypeInfo::Pointer(types.add(TypeInfo::Primitive(Primitive::I8))),
            ConstVal::EnumVariant(name) => TypeInfo::Enum(types.add_names(std::iter::once(name.clone()))),
            ConstVal::Bool(_) => TypeInfo::Primitive(Primitive::Bool),
            ConstVal::Symbol(_) => TypeInfo::Primitive(Primitive::Type),
            ConstVal::NotGenerated { .. } => panic!()
        }
    }

    fn equal_to(&self, other: &Self, types: &TypeTable) -> bool {
        match (self, other) {
            (Self::Unit, Self::Unit) => true,
            (Self::Int(_, l0), Self::Int(_, r0)) => l0 == r0,
            (Self::Float(_, l0), Self::Float(_, r0)) => l0 == r0,
            (Self::String(l0), Self::String(r0)) => l0 == r0,
            (Self::EnumVariant(l0), Self::EnumVariant(r0)) => l0 == r0,
            (Self::Bool(l0), Self::Bool(r0)) => l0 == r0,
            (Self::Symbol(l), Self::Symbol(r)) => l.equal_to(r, types),
            (Self::NotGenerated { .. }, Self::NotGenerated { .. }) => panic!(),
            _ => false
        }
    }
}
impl fmt::Display for ConstVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstVal::Invalid => write!(f, "[invalid]"),
            ConstVal::Unit => write!(f, "()"),
            ConstVal::Int(_, int) => write!(f, "{int}"),
            ConstVal::Float(_, float) => write!(f, "{float}"),
            ConstVal::String(s) => write!(f, "{}", String::from_utf8_lossy(s)),
            ConstVal::EnumVariant(variant) => write!(f, ".{variant}"),
            ConstVal::Bool(b) => write!(f, "{b}"),
            ConstVal::Symbol(symbol) => write!(f, "{symbol:?}"),
            ConstVal::NotGenerated => write!(f, "[not generated]"),
        }
    }
}

pub struct Module {
    pub name: String,
    pub funcs: Vec<Function>,
    pub globals: Vec<(String, Type, Option<ConstVal>)>,
    pub types: Vec<(String, TypeDef)>,
}
impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (name, ty) in &self.types {
            cwriteln!(f, "#b<begin> #r<{name}>\n{}#b<end> #r<{name}>\n",
                ty,
                name = name,
            )?;
        }
        for (name, ty, val) in &self.globals {
            cwriteln!(f, "#b<global> #r<{}> : #m<{}>\n", name, ty)?;
            if let Some(val) = val {
                cwriteln!(f, " = {}", val)?;
            }
        }
        for func in &self.funcs {
            if func.ir.is_none() {
                cwriteln!(f, "#m<extern> #r<{}>{}", func.name, func)?;
            } else {
                cwriteln!(f, "#b<begin> #r<{name}>{}#b<end> #r<{name}>\n",
                    func,
                    name = func.name
                )?;
            }
        }
        Ok(())
    }
}

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

const INDEX_OFFSET: u32 = std::mem::variant_count::<RefVal>() as u32;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Ref(u32);
impl Ref {
    pub const UNDEF: Self = Self::val(RefVal::Undef);
    pub const UNIT: Self = Self::val(RefVal::Unit);

    pub const fn val(val: RefVal) -> Self {
        Self(val as u32)
    }
    pub fn index(idx: u32) -> Self {
        Self(INDEX_OFFSET + idx)
    }
    pub fn is_val(self) -> bool { self.0 < INDEX_OFFSET }
    pub fn into_val(self) -> Option<RefVal> {
        self.is_val().then(|| unsafe { std::mem::transmute(self.0 as u8) })
    }
    pub fn is_ref(self) -> bool { !self.is_val() }
    pub fn into_ref(self) -> Option<u32> {
        self.is_ref().then_some(self.0 - INDEX_OFFSET)
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
    Undef
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


#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BlockIndex(u32);
impl BlockIndex {
    pub fn bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }
}
impl fmt::Display for BlockIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        cwrite!(f, "#b<b{}>", self.0)
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
