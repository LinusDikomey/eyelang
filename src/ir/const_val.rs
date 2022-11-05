use std::fmt;

use crate::{types::{IntType, FloatType, Primitive}, irgen::IrBuilder, ast::ModuleId, span::{TSpan, Span}, error::Errors};

use super::{TypeTable, TypeInfo, SymbolKey, TypeTableIndex, TypingCtx, Ref, Type};

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

    pub fn equal_to(&self, other: &Self, types: &TypeTable) -> bool {
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

#[derive(Debug, Clone)]
pub enum ConstSymbol {
    Func(SymbolKey),
    GenericFunc(u32),
    TraitFunc(SymbolKey, u32),
    Type(SymbolKey),
    TypeValue(Type),
    Trait(SymbolKey),
    LocalType(TypeTableIndex),
    Module(ModuleId),
}
impl ConstSymbol {
    pub fn add_instruction(&self, ir: &mut IrBuilder, ctx: &TypingCtx, ty: TypeTableIndex, errors: &mut Errors, span: Span) -> Ref {
        ir.specify(ty, TypeInfo::Symbol, errors, TSpan::new(span.start, span.end), ctx);
        match self {
            &ConstSymbol::Func(symbol) => ir.build_func(symbol, ty),
            ConstSymbol::GenericFunc(_) => todo!(),
            &ConstSymbol::TraitFunc(trait_symbol, func_idx) => {
                ir.build_trait_func(trait_symbol, func_idx, ty)
            }
            &ConstSymbol::Type(symbol) => ir.build_type(symbol, ty),
            ConstSymbol::TypeValue(_ty) => todo!(),
            &ConstSymbol::Trait(symbol) => ir.build_trait(symbol, ty),
            &ConstSymbol::LocalType(idx) => ir.build_local_type(idx, ty),
            &ConstSymbol::Module(module_id) => ir.build_module(module_id, ty),
        }
    }
    pub fn equal_to(&self, other: &ConstSymbol, types: &TypeTable) -> bool {
        match (self, other) {
            (Self::Func(l), Self::Func(r))
            | (Self::Type(l), Self::Type(r))
            | (Self::Trait(l), Self::Trait(r)) => l == r,
            (Self::TraitFunc(l_key, l_idx), Self::TraitFunc(r_key, r_idx)) => l_key == r_key && l_idx == r_idx,
            (Self::LocalType(l), Self::LocalType(r)) => {
                let TypeInfo::Resolved(_l_id, _l_generics) = types[*l] else { unreachable!() };
                let TypeInfo::Resolved(_r_id, _r_generics) = types[*r] else { unreachable!() };
                todo!()
            }
            (Self::Module(l), Self::Module(r)) => l == r,
            _ => false,
        }
    }
}
