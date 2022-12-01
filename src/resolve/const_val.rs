use std::fmt;

use crate::{
    types::{IntType, FloatType, Primitive},
    ast::{ModuleId, FunctionId, TraitId, TypeId, ExprRef, UnresolvedType, Ast},
    error::Errors,
    parser::Counts,
    irgen, ir::{builder::IrBuilder, Ref, self, eval::ConstIrTypes}, dmap,
};

use super::{
    type_info::{TypeTable, TypeInfo, TypeTableIndex},
    types::{Type, DefId, SymbolTable},
    scope::{ExprInfo, ScopeId, Scopes},
    Ctx,
    Ident,
};

#[derive(Debug, Clone)]
pub enum ConstItem {
    Val(ConstVal),
    Symbol(ConstSymbol),
}
impl ConstItem {
    pub fn equal_to(&self, other: &Self, types: &TypeTable) -> bool {
        match (self, other) {
            (ConstItem::Val(a), ConstItem::Val(b)) => a.equal_to(b),
            (ConstItem::Symbol(a), ConstItem::Symbol(b)) => a.equal_to(b, types),
            _ => false,
        }
    }
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
        }
    }

    pub fn equal_to(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unit, Self::Unit) => true,
            (Self::Int(_, l0), Self::Int(_, r0)) => l0 == r0,
            (Self::Float(_, l0), Self::Float(_, r0)) => l0 == r0,
            (Self::String(l0), Self::String(r0)) => l0 == r0,
            (Self::EnumVariant(l0), Self::EnumVariant(r0)) => l0 == r0,
            (Self::Bool(l0), Self::Bool(r0)) => l0 == r0,
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
        }
    }
}

#[derive(Debug, Clone)]
pub enum ConstSymbol {
    Func(FunctionId),
    //GenericFunc(u32),
    Type(TypeId),
    TypeValue(Type),
    Trait(TraitId),
    TraitFunc(TraitId, u32),
    LocalType(TypeTableIndex),
    Module(ModuleId),
}
impl ConstSymbol {
    pub fn equal_to(&self, other: &ConstSymbol, types: &TypeTable) -> bool {
        match (self, other) {
            (Self::Func(l), Self::Func(r)) => l == r,
            (Self::Type(l), Self::Type(r)) => l == r,
            (Self::Trait(l), Self::Trait(r)) => l == r,
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
    pub fn as_def_id(&self) -> DefId {
        match self {
            &ConstSymbol::Func(id) => DefId::Function(id),
            &ConstSymbol::Type(id) => DefId::Type(id),
            ConstSymbol::TypeValue(_) => todo!(),
            &ConstSymbol::Trait(id) => DefId::Trait(id),
            &ConstSymbol::TraitFunc(id, idx) => DefId::TraitFunc(id, idx),
            ConstSymbol::LocalType(_) => todo!(),
            &ConstSymbol::Module(id) => DefId::Module(id),
        }
    }
}

pub fn eval(
    expr: ExprRef,
    ty: &UnresolvedType,
    counts: Counts,
    scopes: &mut Scopes,
    scope: ScopeId,
    errors: &mut Errors,
    ast: &Ast,
    symbols: &mut SymbolTable,
    ir: &mut irgen::Functions,
) -> ConstItem {
    let scope = scopes.child(scope, dmap::new(), dmap::new(), false);
    
    let mut types = TypeTable::new(0);

    let ty = scopes.resolve_type_info(scope, ty, &mut types, errors, symbols, ast, ir);
    let ty = types.add_info_or_idx(ty);

    let mut idents = vec![Ident::Invalid; counts.idents as usize];
    let mut vars = vec![];

    let before_error_count = errors.error_count();

    let ctx = Ctx {
        scopes,
        scope,
        ast,
        symbols,
        types: &mut types,
        idents: &mut idents,
        vars: &mut vars,
        errors,
        ir,
    };
    let mut noreturn = false;
    _ = super::expr::check_expr(expr, ExprInfo { expected: ty, ret: ty, noreturn: &mut noreturn }, ctx, false);
    
    if before_error_count < errors.error_count() {
        // this is not a perfect solution but right now expressions with errors can result in crashed during irgen.
        // For this reason, just return Invalid here.
        
        return ConstItem::Val(ConstVal::Invalid);
    }


    let mut var_refs = vec![Ref::UNDEF; vars.len()];

    let mut builder = IrBuilder::new(types, ConstIrTypes::new());
    let res = irgen::gen_expr(&mut builder, expr, &mut irgen::Ctx {
        ast,
        symbols: &symbols,
        var_refs: &mut var_refs,
        idents: &idents,
        module: scopes[scope].module.id,
        functions: ir,
        function_generics: &[],
        member_accesses: &symbols.member_accesses,
    }, &mut noreturn);
    let val = res.val(&mut builder, ty);

    if !noreturn {
        builder.build_ret(val);
    }

    match ir::eval::eval(&builder, &[]) {
        Ok(val) => val,
        Err(err) => {
            errors.emit_span(err, ast[expr].span_in(ast, scopes[scope].module.id));
            ConstItem::Val(ConstVal::Invalid)
        }
    }

}
