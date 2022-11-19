use core::fmt;
use color_format::cwriteln;

use crate::{
    types::{Primitive, Layout},
    dmap::DHashMap, ast::{ModuleId, FunctionId, TypeId, TypeDef, ExprRef, CallId, TraitId, GlobalId}
};

use super::{const_val::{ConstVal, ConstSymbol}, type_info::{TypeInfo, TypeTable, TypeInfoOrIndex, TypeTableIndex, TypeTableIndices}, Ident, Var, ResolvedCall};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Prim(Primitive),
    Id(TypeId, Vec<Type>),
    Pointer(Box<Type>),
    Array(Box<(Type, u32)>),
    //TODO: takes up 24 bytes and heap allocates, maybe find a more generic solution to store all types.
    Enum(Vec<String>),
    Tuple(Vec<Type>),
    /// A generic type (commonly T) that will be replaced by a concrete type in generic instantiations.
    Generic(u8),
    Invalid
}
impl Type {
    pub fn layout(&self, ctx: &SymbolTable, generics: &[Type]) -> Layout {
        match self {
            Type::Prim(p) => p.layout(),
            Type::Id(key, generics) => ctx.get_type(*key).layout(ctx, generics),
            Type::Pointer(_) => Layout::PTR,
            Type::Array(b) => {
                let (ty, size) = &**b;
                ty.layout(ctx, generics).mul_size(*size as u64)
            }
            Type::Enum(variants) => Enum::_layout_from_variant_count(variants.len()),
            Type::Tuple(tuple) => {
                tuple.iter().fold(Layout::ZERO, |l, ty| l.accumulate(ty.layout(ctx, generics)))
            }
            Type::Generic(idx) => generics[*idx as usize].layout(ctx, generics),
            Type::Invalid => Layout::ZERO,
        }
    }
    pub fn is_zero_sized(&self, types: &[(String, ResolvedTypeDef)], generics: &[Type]) -> bool {
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
            Type::Generic(idx) => generics[*idx as usize].is_zero_sized(types, generics),
            Type::Invalid => true,
        }
    }

    pub fn as_info(&self, types: &mut TypeTable, on_generic: impl Fn(u8) -> TypeInfoOrIndex + Copy) -> TypeInfoOrIndex {
        TypeInfoOrIndex::Type(match self {
            Self::Prim(p) => TypeInfo::Primitive(*p),
            Self::Id(id, ty_generics) => {
                /*let generics = types.add_multiple_unknown(ty_generics.len() as _);
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
                */
                let ty_generics: Vec<_> = ty_generics
                    .iter()
                    .map(|ty| ty.as_info(types, on_generic))
                    .collect();
                let ty_generics = types.add_multiple_info_or_index(ty_generics);
                TypeInfo::Resolved(*id, ty_generics)
            }
            Self::Pointer(inner) => {
                let inner = inner.as_info(types, on_generic);
                TypeInfo::Pointer(types.add_info_or_idx(inner))
            }
            Self::Array(array) => {
                let (ty, count) = &**array;
                let inner = ty.as_info(types, on_generic);
                TypeInfo::Array(Some(*count), types.add_info_or_idx(inner))
            }
            Self::Enum(variants) =>
                TypeInfo::Enum(types.add_names(variants.as_slice().iter().cloned())),
            Self::Tuple(elems) => {
                let infos = elems.iter().map(|ty| ty.as_info(types, on_generic)).collect::<Vec<_>>();
                TypeInfo::Tuple(types.add_multiple_info_or_index(infos), TupleCountMode::Exact)
            }
            Self::Generic(idx) => {
                return on_generic(*idx);
            }
            Self::Invalid => TypeInfo::Invalid
        })
    }

    pub fn instantiate_generics(&self, generics: &[Type]) -> Self {
        match self {
            Type::Prim(p) => Type::Prim(*p),
            Type::Id(key, ty_generics) => Type::Id(
                *key,
                ty_generics.iter().map(|ty| ty.instantiate_generics(generics)).collect()
            ),
            Type::Pointer(inner) => Type::Pointer(Box::new(inner.instantiate_generics(generics))),
            Type::Array(b) => {
                let (inner, count) = &**b;
                Type::Array(Box::new((inner.instantiate_generics(generics), *count)))
            }
            Type::Enum(variants) => Type::Enum(variants.clone()),
            Type::Tuple(types) => Type::Tuple(
                types
                    .iter()
                    .map(|ty| ty.instantiate_generics(generics))
                    .collect()
            ),
            Type::Generic(idx) => generics[*idx as usize].clone(),
            Type::Invalid => Type::Invalid,
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct SymbolKey(u64);
impl SymbolKey {
    pub const MISSING: Self = Self(u64::MAX);

    pub fn idx(self) -> usize { self.0 as usize }
    pub fn bytes(self) -> [u8; 8] { self.0.to_le_bytes() }
    pub fn from_bytes(bytes: [u8; 8]) -> Self { Self(u64::from_le_bytes(bytes)) }
}

#[derive(Debug)]
pub enum MaybeTypeDef {
    Some(ResolvedTypeDef),
    NotGenerated {
        generic_count: u8,
    }
}

#[derive(Debug)]
pub struct SymbolTable {
    pub funcs: Vec<Option<FunctionHeader>>,
    pub types: Vec<(String, MaybeTypeDef)>,
    pub traits: Vec<Option<TraitDef>>,
    pub consts: Vec<ConstVal>,
    pub globals: Vec<(String, Type, Option<ConstVal>)>,
    pub expr_types: Vec<TypeTableIndex>,
    pub calls: Vec<Option<ResolvedCall>>,
}
impl SymbolTable {
    pub fn new(func_count: usize, expr_count: usize, types: &[TypeDef], trait_count: usize, call_count: usize) -> Self {
        Self {
            funcs: (0..func_count).map(|_| None).collect(),
            types: types
                .iter()
                .map(|ty| (ty.name().to_owned(), MaybeTypeDef::NotGenerated { generic_count: ty.generic_count() }))
                .collect(),
            traits: (0..trait_count).map(|_| None).collect(),
            consts: Vec::new(),
            globals: Vec::new(),
            expr_types: vec![TypeTableIndex::NONE; expr_count],
            calls: vec![None; call_count],
        }
    }   
    pub fn place_func(&mut self, id: FunctionId, func: FunctionHeader) {
        self.funcs[id.idx()] = Some(func);
    }
    /*
    pub fn add_func(&mut self) -> FunctionId {
        let key = FunctionId(self.funcs.len() as u64);
        self.funcs.push(None);
        key
    }
    
    pub fn add_type(&mut self, name: String, generic_count: u8) -> TypeId {
        let key = TypeId(self.types.len() as u64);
        self.types.push((name, MaybeTypeDef::NotGenerated { generic_count }));
        key
    }*/
    pub fn generic_count(&self, ty: TypeId) -> u8 {
        match &self.types[ty.idx()].1 {
            MaybeTypeDef::Some(def) => def.generic_count(),
            MaybeTypeDef::NotGenerated { generic_count } => *generic_count,
        }
    }
    pub fn place_type(&mut self, id: TypeId, ty: ResolvedTypeDef) {
        self.types[id.idx()].1 = MaybeTypeDef::Some(ty);
    }
    /*
    pub fn add_trait(&mut self, t: TraitDef) -> SymbolKey {
        let key = SymbolKey(self.traits.len() as u64);
        self.traits.push(t);
        key
    }
    */
    pub fn add_const(&mut self, c: ConstVal) -> SymbolKey {
        let key = SymbolKey(self.consts.len() as u64);
        self.consts.push(c);
        key
    }
    pub fn add_global(&mut self, name: String, ty: Type, val: Option<ConstVal>) -> SymbolKey {
        let key = SymbolKey(self.globals.len() as u64);
        self.globals.push((name, ty, val));
        key
    }

    pub fn get_func(&self, key: FunctionId) -> &FunctionHeader { self.funcs[key.idx()].as_ref().unwrap() }
    pub fn get_func_mut(&mut self, key: FunctionId) -> &mut FunctionHeader { self.funcs[key.idx()].as_mut().unwrap() }

    pub fn place_call(&mut self, id: CallId, call: ResolvedCall) {
        self.calls[id.idx()] = Some(call);
    }

    pub fn get_type(&self, id: TypeId) -> &ResolvedTypeDef {
        let MaybeTypeDef::Some(def) = &self.types[id.idx()].1 else {
            panic!("tried to retrieve unfinished type")
        };
        def
    }
    //pub fn get_func(&self, key: SymbolKey) -> &FunctionOrHeader { &self.funcs[key.idx()] }
    //pub fn get_func_mut(&mut self, key: SymbolKey) -> &mut FunctionOrHeader { &mut self.funcs[key.idx()] }
    pub fn get_const(&self, key: SymbolKey) -> &ConstVal { &self.consts[key.idx()] }
    pub fn get_global(&self, key: SymbolKey) -> &(String, Type, Option<ConstVal>) { &self.globals[key.idx()] }
    pub fn get_const_mut(&mut self, key: SymbolKey) -> &mut ConstVal { &mut self.consts[key.idx()] }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DefId {
    Function(FunctionId),
    Type(TypeId),
    Trait(TraitId),
    Module(ModuleId),
    Global(GlobalId),
    Generic(u8),
    Invalid,
    Unresolved { resolving: bool }
}
impl From<DefId> for ConstSymbol {
    fn from(value: DefId) -> Self {
        match value {
            DefId::Function(id) => Self::Func(id),
            DefId::Type(id) => Self::Type(id),
            DefId::Trait(id) => Self::Trait(id),
            DefId::Module(id) => Self::Module(id),
            DefId::Global(id) => todo!(),
            DefId::Generic(i) => todo!(),
            DefId::Invalid => todo!(),
            DefId::Unresolved { .. } => unreachable!()
        }
    }
}

#[derive(Debug)]
pub enum ResolvedTypeDef {
    Struct(Struct),
    Enum(Enum),
    NotGenerated { name: String, generic_count: u8, generating: bool },
}
impl ResolvedTypeDef {
    pub fn name(&self) -> &str {
        match self {
            Self::Struct(s) => &s.name,
            Self::Enum(e) => &e.name,
            Self::NotGenerated { name, .. } => &name,
        }
    }
    pub fn generic_count(&self) -> u8 {
        match self {
            Self::Struct(struct_) => struct_.generic_count,
            Self::Enum(enum_) => enum_.generic_count,
            Self::NotGenerated { generic_count, .. } => *generic_count
        }
    }
    pub fn layout(&self, ctx: &SymbolTable, generics: &[Type]) -> Layout {
        match self {
            Self::Struct(struct_) => {
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
            Self::Enum(enum_) => {
                enum_._layout()
            }
            Self::NotGenerated { .. }
                => panic!("layout of NotGenerated types should not be requested"),
        }
    }
    pub fn is_zero_sized(&self, types: &[(String, ResolvedTypeDef)], generics: &[Type]) -> bool {
        match self {
            Self::Struct(def) => def.members.iter().all(|(_, member)| member.is_zero_sized(types, generics)),
            Self::Enum(def) => def.variants.len() < 2,
            Self::NotGenerated { .. } => unreachable!()
        }
    }
}


#[derive(Debug, Clone)]
pub struct FunctionHeader {
    pub name: String,
    pub generics: Vec<String>,
    pub params: Vec<(String, Type)>,
    pub varargs: bool,
    pub return_type: Type,
    pub resolved_body: Option<ResolvedFunc>,
    pub module: ModuleId,
}
impl FunctionHeader {
    pub fn generic_count(&self) -> u8 {
        self.generics.len() as u8
    }
}

#[derive(Debug, Clone)]
pub struct ResolvedFunc {
    pub body: ExprRef,
    pub idents: Vec<Ident>,
    pub vars: Vec<Var>,
    pub types: TypeTable,
    pub generics: TypeTableIndices,
}

#[derive(Debug)]
pub struct GenericFunc {

}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TupleCountMode {
    Exact,
    AtLeast,
}

#[derive(Debug, Clone)]
pub struct Struct {
    pub name: String,
    pub members: Vec<(String, Type)>,
    pub methods: DHashMap<String, FunctionId>,
    pub generic_count: u8,
}

#[derive(Debug, Clone, Copy)]
pub enum StructMemberSymbol {
    Func(FunctionId),
}

#[derive(Debug, Clone)]
pub struct TraitDef {
    pub functions: DHashMap<String, (u32, FunctionHeader)>
}

#[derive(Debug, Clone)]
pub struct Enum {
    pub name: String,
    pub variants: DHashMap<String, u32>,
    pub generic_count: u8,
}
impl Enum {
    pub fn _layout_from_variant_count(count: usize) -> Layout {
        let size = ((count as u64 - 1).ilog2() as u64 + 1).div_ceil(8);
        let alignment = match size {
            0 | 1 => 1,
            2 => 2,
            3..=4 => 4,
            5.. => 8,
        };
        Layout { size, alignment }
    }
    pub fn _layout(&self) -> Layout {
        Self::_layout_from_variant_count(self.variants.len())
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