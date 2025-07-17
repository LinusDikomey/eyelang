use std::rc::Rc;

use id::TypeId;
use types::Type;

use crate::{
    Compiler,
    compiler::ResolvedTypeContent,
    types::{LocalTypeIds, TypeInfo, TypeTable},
};

#[derive(Clone, Copy, Debug)]
pub enum Generics<'a> {
    Empty,
    Types(&'a [Type], &'a Generics<'a>),
    Local(&'a TypeTable, LocalTypeIds, &'a Generics<'a>),
}
impl<'a> Generics<'a> {
    pub fn function_instance(instance_generics: &'a [Type]) -> Self {
        Self::Types(instance_generics, &Self::Empty)
    }
    fn get(&self, i: u8, compiler: &mut Compiler, ir_types: &mut ir::Types) -> Option<ir::Type> {
        match self {
            Self::Empty => unreachable!(),
            Self::Types(generics, outer) => get(compiler, ir_types, &generics[i as usize], **outer),
            Self::Local(type_table, generics, outer) => get_from_info(
                compiler,
                type_table,
                ir_types,
                type_table[generics.nth(i.into()).unwrap()],
                **outer,
            ),
        }
    }
}

pub fn get(
    compiler: &mut Compiler,
    ir_types: &mut ir::Types,
    ty: &Type,
    generics: Generics,
) -> Option<ir::Type> {
    Some(match ty {
        &Type::Primitive(p) => get_primitive(p).into(),
        &Type::Generic(i) => return generics.get(i, compiler, ir_types),
        Type::Invalid => return None,
        Type::Pointer(_) => ir::Primitive::Ptr.into(),
        Type::Array(b) => {
            let (elem, size) = &**b;
            let elem = get(compiler, ir_types, elem, generics)?;
            let elem = ir_types.add(elem);
            ir::Type::Array(elem, *size)
        }
        Type::Tuple(elems) => ir::Type::Tuple(get_multiple(compiler, ir_types, elems, generics)?),
        Type::DefId {
            id,
            generics: def_generics,
        } => get_def(
            compiler,
            ir_types,
            *id,
            Generics::Types(def_generics, &generics),
        )?,
        Type::LocalEnum(_) => todo!("local enums"),
        Type::Function(_) => ir::Primitive::Ptr.into(),
    })
}

pub fn get_multiple(
    compiler: &mut Compiler,
    ir_types: &mut ir::Types,
    types: &[Type],
    generics: Generics,
) -> Option<ir::TypeIds> {
    let refs = ir_types.add_multiple(types.iter().map(|_| ir::Primitive::Unit.into()));
    for (elem, ty) in types.iter().zip(refs.iter()) {
        let elem = get(compiler, ir_types, elem, generics)?;
        ir_types[ty] = elem;
    }
    Some(refs)
}

pub fn get_def(
    compiler: &mut Compiler,
    ir_types: &mut ir::Types,
    def: TypeId,
    generics: Generics,
) -> Option<ir::Type> {
    let resolved = Rc::clone(compiler.get_resolved_type_def(def));
    Some(match &resolved.def {
        ResolvedTypeContent::Struct(def) => {
            let elems =
                ir_types.add_multiple((0..def.field_count()).map(|_| ir::Primitive::Unit.into()));
            for ((_, field), r) in def.all_fields().zip(elems.iter()) {
                let ty = get(compiler, ir_types, field, generics)?;
                ir_types[r] = ty;
            }
            ir::Type::Tuple(elems)
        }
        ResolvedTypeContent::Enum(def) => {
            let mut accumulated_layout = ir::Layout::EMPTY;
            // TODO: reduce number of variants if reduced by never types in variants
            let ordinal_type = int_from_variant_count(def.variants.len() as u32);
            let mut has_content = false;
            'variants: for (_variant_name, args) in &*def.variants {
                if !args.is_empty() {
                    has_content = true;
                }
                let elems =
                    ir_types.add_multiple((0..args.len() + 1).map(|_| ir::Primitive::Unit.into()));
                let mut elem_iter = elems.iter();
                ir_types[elem_iter.next().unwrap()] = ordinal_type.into();
                for (arg, r) in args.iter().zip(elem_iter) {
                    let Some(elem) = get(compiler, ir_types, arg, generics) else {
                        continue 'variants;
                    };
                    ir_types[r] = elem;
                }
                let variant_layout =
                    ir::type_layout(ir::Type::Tuple(elems), ir_types, compiler.ir.primitives());
                accumulated_layout.accumulate_variant(variant_layout);
            }
            if has_content {
                type_from_layout(ir_types, accumulated_layout)
            } else {
                ordinal_type.into()
            }
        }
    })
}

/// returns None on invalid type, should always be handled correctly
pub fn get_from_info(
    compiler: &mut Compiler,
    types: &TypeTable,
    ir_types: &mut ir::Types,
    ty: TypeInfo,
    generics: Generics,
) -> Option<ir::Type> {
    Some(match ty {
        TypeInfo::Primitive(p) => get_primitive(p).into(),
        TypeInfo::Integer => ir::Primitive::I32.into(),
        TypeInfo::Float => ir::Primitive::F32.into(),
        TypeInfo::TypeDef(id, def_generics) => {
            return get_def(
                compiler,
                ir_types,
                id,
                Generics::Local(types, def_generics, &generics),
            );
        }
        TypeInfo::Pointer(_) | TypeInfo::Function { .. } => ir::Primitive::Ptr.into(),
        TypeInfo::Array {
            element,
            count: Some(count),
        } => {
            let element = get_from_info(compiler, types, ir_types, types[element], generics)?;
            ir::Type::Array(ir_types.add(element), count)
        }
        TypeInfo::Enum(id) => {
            let mut accumulated_layout = ir::Layout::EMPTY;
            let variants = types.get_enum_variants(id);
            let mut inhabited_variants: usize = 0;
            'variants: for &variant in variants {
                let variant = &types[variant];
                let Some(args) =
                    get_multiple_infos(compiler, types, ir_types, variant.args, generics)
                else {
                    continue 'variants;
                };
                inhabited_variants += 1;
                let variant_layout =
                    ir::type_layout(ir::Type::Tuple(args), ir_types, compiler.ir.primitives());
                accumulated_layout.accumulate_variant(variant_layout);
            }
            if inhabited_variants == 0 {
                return None;
            }
            type_from_layout(ir_types, accumulated_layout)
        }
        TypeInfo::Tuple(members) => {
            let member_refs =
                ir_types.add_multiple((0..members.count).map(|_| ir::Primitive::Unit.into()));
            for (ty, r) in members.iter().zip(member_refs.iter()) {
                let ty = get_from_info(compiler, types, ir_types, types[ty], generics)?;
                ir_types[r] = ty;
            }
            ir::Type::Tuple(member_refs)
        }
        TypeInfo::Generic(i) => return generics.get(i, compiler, ir_types),
        TypeInfo::FunctionItem { .. } => ir::Primitive::Unit.into(),
        TypeInfo::Unknown
        | TypeInfo::UnknownSatisfying { .. }
        | TypeInfo::TypeItem { .. }
        | TypeInfo::TraitItem { .. }
        | TypeInfo::Array {
            element: _,
            count: None,
        }
        | TypeInfo::ModuleItem(_)
        | TypeInfo::MethodItem { .. }
        | TypeInfo::TraitMethodItem { .. }
        | TypeInfo::EnumVariantItem { .. }
        | TypeInfo::Invalid => return None,
    })
}

pub fn get_multiple_infos(
    compiler: &mut Compiler,
    types: &TypeTable,
    ir_types: &mut ir::Types,
    ids: LocalTypeIds,
    generics: Generics,
) -> Option<ir::TypeIds> {
    let refs = ir_types.add_multiple((0..ids.count).map(|_| ir::Primitive::Unit.into()));
    for (ty, r) in ids.iter().zip(refs.iter()) {
        let ty = get_from_info(compiler, types, ir_types, types[ty], generics)?;
        ir_types[r] = ty;
    }
    Some(refs)
}

pub fn int_from_variant_count(count: u32) -> ir::Primitive {
    match count {
        0 | 1 => ir::Primitive::Unit,
        2 => ir::Primitive::I1,
        3..256 => ir::Primitive::U8,
        256..=0xFF_FF => ir::Primitive::U16,
        _ => ir::Primitive::U32,
    }
}

pub fn get_primitive(p: types::Primitive) -> ir::Primitive {
    use ir::Primitive as I;
    use types::Primitive as P;
    match p {
        P::I8 => I::I8,
        P::I16 => I::I16,
        P::I32 => I::I32,
        P::I64 => I::I64,
        P::I128 => I::I128,
        P::U8 => I::U8,
        P::U16 => I::U16,
        P::U32 => I::U32,
        P::U64 => I::U64,
        P::U128 => I::U128,
        P::F32 => I::F32,
        P::F64 => I::F64,
        P::Type => I::U64, // TODO
    }
}

pub fn type_from_layout(ir_types: &mut ir::Types, layout: ir::Layout) -> ir::Type {
    if layout.size == 0 {
        debug_assert_eq!(layout.align.get(), 1);
        return ir::Primitive::Unit.into();
    }
    let base_type = match layout.align.get() {
        1 => ir::Primitive::U8.into(),
        2 => ir::Primitive::U16.into(),
        4 => ir::Primitive::U32.into(),
        8 => ir::Primitive::U64.into(),
        16 => ir::Primitive::U128.into(),
        _ => unreachable!(),
    };
    let base_type_count = layout.size / layout.align.get();
    let u8_count = layout.size % layout.align.get();
    debug_assert!(
        base_type_count > 0,
        "can't represent a type with larger align than size"
    );
    let final_layout = ir_types.add_multiple(
        std::iter::repeat(base_type)
            .take(base_type_count as usize)
            .chain(std::iter::repeat(ir::Primitive::U8.into()).take(u8_count as usize)),
    );
    ir::Type::Tuple(final_layout)
}
