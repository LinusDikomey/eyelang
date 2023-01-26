use core::fmt;
use color_format::{cwriteln, cwrite};

use crate::{
    types::{Primitive, Layout, IntType},
    dmap::DHashMap, ast::{ModuleId, FunctionId, TypeId, TypeDef, ExprRef, CallId, TraitId, GlobalId, ConstId, VariantId}, ir::types::TypeRef
};

use super::{
    const_val::{ConstVal, ConstSymbol},
    type_info::{TypeInfo, TypeTable, TypeInfoOrIndex, EnumVariants},
    Ident,
    Var,
    ResolvedCall,
    MemberAccess,
    std_builtins::Builtins
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Prim(Primitive),
    Id(TypeId, Vec<Type>),
    Pointer(Box<Type>),
    Array(Box<(Type, u32)>),
    Tuple(Vec<Type>),
    /// A generic type (commonly T) that will be replaced by a concrete type in generic instantiations.
    Generic(u8),

    // a local enum that will only be created from inference
    LocalEnum(Vec<Vec<Type>>),
    Invalid
}
impl Type {
    pub fn layout<'a>(&self, ctx: impl Fn(TypeId) -> &'a ResolvedTypeDef + Copy, generics: &[Type]) -> Layout {
        match self {
            Type::Prim(p) => p.layout(),
            Type::Id(key, generics) => ctx(*key).layout(
                ctx,
                generics
                    .iter()
                    .map(|ty| ty.instantiate_generics(generics))
                    .collect::<Vec<_>>()
                    .as_slice()
                ),
            Type::Pointer(_) => Layout::PTR,
            Type::Array(b) => {
                let (ty, size) = &**b;
                Layout::array(ty.layout(ctx, generics), *size)
            }
            Type::Tuple(tuple) => {
                let mut l = Layout::EMPTY;
                for ty in tuple {
                    l.accumulate(ty.layout(ctx, generics));
                }
                l
            }
            Type::Generic(idx) => generics[*idx as usize].layout(ctx, generics),
            Type::LocalEnum(variants) => {
                let tag_layout = Enum::int_ty_from_variant_count(variants.len() as _)
                    .map_or(Layout::EMPTY, |int_ty| Primitive::from(int_ty).layout());
                let mut layout = tag_layout;
                for variant in variants {
                    let mut variant_layout = tag_layout;
                    for arg in variant {
                        variant_layout.accumulate(arg.layout(ctx, generics));
                    }
                    layout.add_variant(variant_layout);
                }
                layout
            }
            Type::Invalid => Layout::EMPTY,
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
            Self::Tuple(elems) => {
                let infos = elems.iter().map(|ty| ty.as_info(types, on_generic)).collect::<Vec<_>>();
                TypeInfo::Tuple(types.add_multiple_info_or_index(infos), TupleCountMode::Exact)
            }
            Self::Generic(idx) => {
                return on_generic(*idx);
            }
            Self::LocalEnum(variants) => unreachable!(), // this shouldn't happen as LocalEnum
                                                         // can't be created with a type annotation
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
            Type::Tuple(types) => Type::Tuple(
                types
                    .iter()
                    .map(|ty| ty.instantiate_generics(generics))
                    .collect()
            ),
            Type::Generic(idx) => generics[*idx as usize].clone(),
            Type::LocalEnum(variants) => Type::LocalEnum(variants
                .iter()
                .map(|variant| variant
                     .iter()
                     .map(|ty| ty.instantiate_generics(generics))
                     .collect()
                )
                .collect()
            ),
            Type::Invalid => Type::Invalid,
        }
    }
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
    pub builtins: Builtins,
    pub funcs: Vec<Option<FunctionHeader>>,
    pub types: Vec<(String, MaybeTypeDef)>,
    pub traits: Vec<Option<TraitDef>>,
    pub consts: Vec<ConstVal>,
    pub globals: Vec<Option<(String, Type, Option<ConstVal>)>>,
    pub expr_types: Vec<TypeRef>,
    pub calls: Vec<Option<ResolvedCall>>,
    pub member_accesses: Vec<MemberAccess>,
}
impl SymbolTable {
    pub fn new(
        builtins: Builtins,
        func_count: usize,
        expr_count: usize,
        types: &[TypeDef],
        trait_count: usize,
        call_count: usize,
        global_count: usize,
        member_access_count: usize
    ) -> Self {
        Self {
            builtins,
            funcs: (0..func_count).map(|_| None).collect(),
            types: types
                .iter()
                .map(|ty| (ty.name().to_owned(), MaybeTypeDef::NotGenerated { generic_count: ty.generic_count() }))
                .collect(),
            traits: (0..trait_count).map(|_| None).collect(),
            consts: Vec::new(),
            globals: vec![None; global_count],
            expr_types: vec![TypeRef::NONE; expr_count],
            calls: vec![None; call_count],
            member_accesses: vec![MemberAccess::Invalid; member_access_count],
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
    pub fn add_const(&mut self, c: ConstVal) -> ConstId {
        self.consts.push(c);
        ConstId::new((self.consts.len() - 1) as u64)
    }
    pub fn place_global(&mut self, id: GlobalId, name: String, ty: Type, val: Option<ConstVal>) {
        self.globals[id.idx()] = Some((name, ty, val));
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
    pub fn get_global(&self, key: GlobalId) -> &(String, Type, Option<ConstVal>) {
        &self.globals[key.idx()].as_ref().unwrap()
    }

    pub fn get_const(&self, id: ConstId) -> &ConstVal {
        &self.consts[id.idx()]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DefId {
    Function(FunctionId),
    Type(TypeId),
    Trait(TraitId),
    TraitFunc(TraitId, u32),
    Module(ModuleId),
    Global(GlobalId),
    Const(ConstId),
    Generic(u8),
    Invalid,
}
impl From<DefId> for ConstSymbol {
    fn from(value: DefId) -> Self {
        match value {
            DefId::Function(id) => Self::Func(id),
            DefId::Type(id) => Self::Type(id),
            DefId::Trait(id) => Self::Trait(id),
            DefId::TraitFunc(id, idx) => Self::TraitFunc(id, idx),
            DefId::Module(id) => Self::Module(id),
            DefId::Global(_id) => todo!(),
            DefId::Const(_id) => todo!(),
            DefId::Generic(_id) => todo!(),
            DefId::Invalid => todo!(),
        }
    }
}

#[derive(Debug)]
pub enum ResolvedTypeDef {
    Struct(Struct),
    Enum(Enum),
}
impl ResolvedTypeDef {
    pub fn name(&self) -> &str {
        match self {
            Self::Struct(s) => &s.name,
            Self::Enum(e) => &e.name,
        }
    }
    pub fn generic_count(&self) -> u8 {
        match self {
            Self::Struct(struct_) => struct_.generic_count(),
            Self::Enum(enum_) => enum_.generic_count,
        }
    }
    pub fn layout<'a>(&self, ctx: impl Fn(TypeId) -> &'a ResolvedTypeDef + Copy, generics: &[Type]) -> Layout {
        match self {
            Self::Struct(struct_) => {
                let mut layout = Layout::EMPTY;
                for (_, ty) in struct_.members.iter() {
                    layout.accumulate(ty.layout(ctx, generics));
                }
                layout
            }
            Self::Enum(enum_) => {
                enum_.layout(ctx, generics)
            }
        }
    }
}


#[derive(Debug, Clone)]
pub struct FunctionHeader {
    pub name: String,
    pub inherited_generic_count: u8,
    pub generics: Vec<String>,
    pub params: Vec<(String, Type)>,
    pub varargs: bool,
    pub return_type: Type,
    pub resolved_body: Option<ResolvedFunc>,
    pub module: ModuleId,
}
impl FunctionHeader {
    pub fn generic_count(&self) -> u8 {
        self.inherited_generic_count + self.generics.len() as u8
    }
}

#[derive(Debug, Clone)]
pub struct ResolvedFunc {
    pub body: ExprRef,
    pub idents: Vec<Ident>,
    pub vars: Vec<Var>,
    pub types: TypeTable,
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
    pub generics: Vec<String>,
}
impl Struct {
    pub fn generic_count(&self) -> u8 {
        self.generics.len() as u8
    }
}

#[derive(Debug, Clone)]
pub struct TraitDef {
    pub functions: DHashMap<String, (u32, FunctionHeader)>
}

#[derive(Debug, Clone)]
pub struct Enum {
    pub name: String,
    pub variants: DHashMap<String, (VariantId, u32, Vec<Type>)>,
    pub generic_count: u8,
}
impl Enum {
    pub fn layout<'a>(&self, ctx: impl Fn(TypeId) -> &'a ResolvedTypeDef + Copy, generics: &[Type]) -> Layout {
        let tag_layout = Self::int_ty_from_variant_count(self.variants.len() as u32)
            .map_or(Layout::EMPTY, |ty| Primitive::from(ty).layout());
        let mut layout = tag_layout;
        for (_, _, args) in self.variants.values() {
            let mut variant_layout = tag_layout;
            for arg in args {
                variant_layout.accumulate(arg.layout(ctx, generics));
            }
            layout.add_variant(variant_layout);
        }
        layout
    }
    pub fn int_ty(&self) -> Option<IntType> {
        Self::int_ty_from_variant_count(self.variants.len() as u32)
    }

    pub fn int_ty_from_variant_count(variant_count: u32) -> Option<IntType> {
        if variant_count < 2 { return None }
        Some(match ((variant_count - 1).ilog2() as u64 + 1).div_ceil(8) {
            1 => IntType::U8,
            2 => IntType::U16,
            3 | 4 => IntType::U32,
            5..=8 => IntType::U64,
            _ => unreachable!()
        })
    }
    
}
impl fmt::Display for Enum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (variant, (_, variant_val, variant_types)) in &self.variants {
            if variant_types.is_empty() {
                cwriteln!(f, "  #m<{}> = #c<{}>", variant, variant_val)?;
            } else {
                cwrite!(f, "  #m<{}>", variant)?;

                for ty in variant_types {
                    write!(f, "TODO: render types here")?;
                }

                cwriteln!(f, " = #c<{}>", variant_val)?;
            }
        }
        Ok(())
    }
}
