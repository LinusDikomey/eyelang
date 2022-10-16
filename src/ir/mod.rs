use std::fmt;
use color_format::*;
use crate::dmap::DHashMap;
use crate::help::{write_delimited, write_delimited_with};
use crate::types::Primitive;
use builder::IrBuilder;

pub mod builder;
pub mod eval;
pub mod exhaust;

mod const_val;
pub use const_val::{ConstVal, ConstSymbol};

mod instruction;
pub use instruction::{Instruction, Tag, Data};

mod typing;
pub use typing::{TypeTable, FinalTypeTable, TypeInfo, TypeTableIndex, TypeTableIndices};


pub struct TypingCtx {
    pub funcs: Vec<FunctionOrHeader>,
    pub types: Vec<(String, TypeDef)>,
    pub traits: Vec<TraitDef>,
    pub consts: Vec<ConstVal>,
    pub globals: Vec<(Type, Option<ConstVal>)>,
}
impl TypingCtx {
    pub fn new() -> Self {
        Self {
            funcs: Vec::new(),
            types: Vec::new(),
            traits: Vec::new(),
            consts: Vec::new(),
            globals: Vec::new(),
        }
    }
    pub fn add_func(&mut self, func: FunctionOrHeader) -> SymbolKey {
        let key = SymbolKey(self.funcs.len() as u64);
        self.funcs.push(func);
        key
    }
    pub fn add_type(&mut self, name: String, ty: TypeDef) -> SymbolKey {
        let key = SymbolKey(self.types.len() as u64);
        self.types.push((name, ty));
        key
    }
    pub fn add_proto_ty(&mut self, name: String, generic_count: u8) -> SymbolKey {
        self.add_type(name.clone(), TypeDef::NotGenerated { name, generic_count, generating: false })
    }
    pub fn add_trait(&mut self, t: TraitDef) -> SymbolKey {
        let key = SymbolKey(self.traits.len() as u64);
        self.traits.push(t);
        key
    }
    pub fn add_const(&mut self, c: ConstVal) -> SymbolKey {
        let key = SymbolKey(self.consts.len() as u64);
        self.consts.push(c);
        key
    }
    pub fn add_global(&mut self, ty: Type, val: Option<ConstVal>) -> SymbolKey {
        let key = SymbolKey(self.globals.len() as u64);
        self.globals.push((ty, val));
        key
    }
    pub fn get_func(&self, key: SymbolKey) -> &FunctionOrHeader { &self.funcs[key.idx()] }
    pub fn get_type(&self, key: SymbolKey) -> &TypeDef { &self.types[key.idx()].1 }
    pub fn get_type_mut(&mut self, key: SymbolKey) -> &mut TypeDef { &mut self.types[key.idx()].1 }
    //pub fn get_func(&self, key: SymbolKey) -> &FunctionOrHeader { &self.funcs[key.idx()] }
    //pub fn get_func_mut(&mut self, key: SymbolKey) -> &mut FunctionOrHeader { &mut self.funcs[key.idx()] }
    pub fn get_trait(&self, key: SymbolKey) -> &TraitDef { &self.traits[key.idx()] }
    pub fn get_const(&self, key: SymbolKey) -> &ConstVal { &self.consts[key.idx()] }
    pub fn get_global(&self, key: SymbolKey) -> &(Type, Option<ConstVal>) { &self.globals[key.idx()] }
    pub fn get_const_mut(&mut self, key: SymbolKey) -> &mut ConstVal { &mut self.consts[key.idx()] }
}

pub enum FunctionOrHeader {
    Func(Function),
    Header(FunctionHeader),
}
impl FunctionOrHeader {
    pub fn header(&self) -> &FunctionHeader {
        match self {
            Self::Func(f) => &f.header,
            Self::Header(h) => h,
        }
    }
}

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
    pub fn layout(&self, ctx: &TypingCtx, generics: &[Type]) -> Layout {
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

    pub fn as_info(&self, types: &mut TypeTable) -> TypeInfo {
        self.as_info_generic(types, TypeTableIndices::EMPTY).into_info(types)
    }

    pub fn as_info_generic(&self, types: &mut TypeTable, generics: TypeTableIndices) -> TypeInfoOrIndex {
        TypeInfoOrIndex::Type(match self {
            Self::Prim(p) => TypeInfo::Primitive(*p),
            Self::Id(id, ty_generics) => {
                // unfortunately this has to be allocated for borrowing reasons
                let generics = types.add_multiple(ty_generics.iter().map(|_| TypeInfo::Unknown));
                for (generic, ty) in generics.iter().zip(ty_generics) {
                    match ty.as_info_generic(types, generics) {
                        TypeInfoOrIndex::Type(info) => types.update_type(generic, info), //TODO: this might need a proper merge?
                        TypeInfoOrIndex::Idx(idx) => types.point_to(generic, idx),
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
                return TypeInfoOrIndex::Idx(generics.nth(*idx as usize));
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

    
#[derive(Clone, Copy, Debug)]
pub enum TypeInfoOrIndex {
    Type(TypeInfo),
    Idx(TypeTableIndex),
}
impl TypeInfoOrIndex {
    pub fn into_info(self, types: &TypeTable) -> TypeInfo {
        match self {
            TypeInfoOrIndex::Type(info) => info,
            TypeInfoOrIndex::Idx(idx) => types.get_type(idx),
        }
    }
}
impl From<TypeInfo> for TypeInfoOrIndex {
    fn from(info: TypeInfo) -> Self {
        Self::Type(info)
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
    NotGenerated { name: String, generic_count: u8, generating: bool },
}
impl TypeDef {
    pub fn name(&self) -> &str {
        match self {
            TypeDef::Struct(s) => &s.name,
            TypeDef::Enum(e) => &e.name,
            TypeDef::NotGenerated { name, .. } => &name,
        }
    }
    pub fn generic_count(&self) -> u8 {
        match self {
            TypeDef::Struct(struct_) => struct_.generic_count,
            TypeDef::Enum(enum_) => enum_.generic_count,
            Self::NotGenerated { generic_count, .. } => *generic_count
        }
    }
    pub fn layout(&self, ctx: &TypingCtx, generics: &[Type]) -> Layout {
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
    pub name: String,
    pub members: Vec<(String, Type)>,
    pub functions: DHashMap<String, SymbolKey>,
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
    pub name: String,
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
