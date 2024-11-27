use std::rc::Rc;

use id::TypeId;
use ir::{IrType, IrTypes, TypeRefs};
use types::Type;

use crate::{
    compiler::ResolvedTypeDef,
    types::{LocalTypeIds, TypeInfo, TypeTable},
    Compiler,
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
    fn get(&self, i: u8, compiler: &mut Compiler, ir_types: &mut IrTypes) -> Option<IrType> {
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
    ir_types: &mut IrTypes,
    ty: &Type,
    generics: Generics,
) -> Option<IrType> {
    Some(match ty {
        &Type::Primitive(p) => get_primitive(p),
        &Type::Generic(i) => return generics.get(i, compiler, ir_types),
        Type::Invalid => return None,
        Type::Pointer(_) => IrType::Ptr,
        Type::Array(b) => {
            let (elem, size) = &**b;
            let elem = get(compiler, ir_types, elem, generics)?;
            let elem = ir_types.add(elem);
            IrType::Array(elem, *size)
        }
        Type::Tuple(elems) => IrType::Tuple(get_multiple(compiler, ir_types, elems, generics)?),
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
        Type::Function(_) => IrType::Ptr,
    })
}

pub fn get_multiple(
    compiler: &mut Compiler,
    ir_types: &mut IrTypes,
    types: &[Type],
    generics: Generics,
) -> Option<ir::TypeRefs> {
    let refs = ir_types.add_multiple(types.iter().map(|_| IrType::Unit));
    for (elem, ty) in types.iter().zip(refs.iter()) {
        let elem = get(compiler, ir_types, elem, generics)?;
        ir_types.replace(ty, elem);
    }
    Some(refs)
}

pub fn get_def(
    compiler: &mut Compiler,
    ir_types: &mut IrTypes,
    def: TypeId,
    generics: Generics,
) -> Option<IrType> {
    let resolved = compiler.get_resolved_type_def(def);
    let def = Rc::clone(&resolved.def);
    Some(match &*def {
        ResolvedTypeDef::Struct(def) => {
            let elems = ir_types.add_multiple((0..def.field_count()).map(|_| IrType::Unit));
            for ((_, field), r) in def.all_fields().zip(elems.iter()) {
                let ty = get(compiler, ir_types, field, generics)?;
                ir_types.replace(r, ty)
            }
            IrType::Tuple(elems)
        }
        ResolvedTypeDef::Enum(def) => {
            let mut accumulated_layout = ir::Layout::EMPTY;
            // TODO: reduce number of variants if reduced by never types in variants
            let ordinal_type = int_from_variant_count(def.variants.len() as u32);
            'variants: for (_variant_name, args) in &*def.variants {
                let elems = ir_types.add_multiple((0..args.len() + 1).map(|_| IrType::Unit));
                let mut elem_iter = elems.iter();
                ir_types.replace(elem_iter.next().unwrap(), ordinal_type);
                for (arg, r) in args.iter().zip(elem_iter) {
                    let Some(elem) = get(compiler, ir_types, arg, generics) else {
                        continue 'variants;
                    };
                    ir_types.replace(r, elem);
                }
                let variant_layout = ir::type_layout(IrType::Tuple(elems), ir_types);
                accumulated_layout.accumulate_variant(variant_layout);
            }
            type_from_layout(ir_types, accumulated_layout)
        }
    })
}

/// returns None on invalid type, should always be handled correctly
pub fn get_from_info(
    compiler: &mut Compiler,
    types: &TypeTable,
    ir_types: &mut IrTypes,
    ty: TypeInfo,
    generics: Generics,
) -> Option<IrType> {
    Some(match ty {
        TypeInfo::Primitive(p) => get_primitive(p),
        TypeInfo::Integer => IrType::I32,
        TypeInfo::Float => IrType::F32,
        TypeInfo::TypeDef(id, def_generics) => {
            return get_def(
                compiler,
                ir_types,
                id,
                Generics::Local(types, def_generics, &generics),
            );
        }
        TypeInfo::Pointer(_) => IrType::Ptr,
        TypeInfo::Array {
            element,
            count: Some(count),
        } => {
            let element = get_from_info(compiler, types, ir_types, types[element], generics)?;
            IrType::Array(ir_types.add(element), count)
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
                let variant_layout = ir::type_layout(IrType::Tuple(args), ir_types);
                accumulated_layout.accumulate_variant(variant_layout);
            }
            if inhabited_variants == 0 {
                return None;
            }
            type_from_layout(ir_types, accumulated_layout)
        }
        TypeInfo::Tuple(members) => {
            let member_refs = ir_types.add_multiple((0..members.count).map(|_| IrType::Unit));
            for (ty, r) in members.iter().zip(member_refs.iter()) {
                let ty = get_from_info(compiler, types, ir_types, types[ty], generics)?;
                ir_types.replace(r, ty);
            }
            IrType::Tuple(member_refs)
        }
        TypeInfo::Generic(i) => return generics.get(i, compiler, ir_types),
        TypeInfo::FunctionItem { .. } => IrType::Unit,
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
    ir_types: &mut IrTypes,
    ids: LocalTypeIds,
    generics: Generics,
) -> Option<TypeRefs> {
    let refs = ir_types.add_multiple((0..ids.count).map(|_| IrType::Unit));
    for (ty, r) in ids.iter().zip(refs.iter()) {
        let ty = get_from_info(compiler, types, ir_types, types[ty], generics)?;
        ir_types.replace(r, ty);
    }
    Some(refs)
}

pub fn int_from_variant_count(count: u32) -> IrType {
    match count {
        0 | 1 => IrType::Unit,
        2 => IrType::U1,
        3..256 => IrType::U8,
        256..=0xFF_FF => IrType::U16,
        _ => IrType::U32,
    }
}

pub fn get_primitive(p: types::Primitive) -> IrType {
    use types::Primitive as P;
    match p {
        P::I8 => IrType::I8,
        P::I16 => IrType::I16,
        P::I32 => IrType::I32,
        P::I64 => IrType::I64,
        P::I128 => IrType::I128,
        P::U8 => IrType::U8,
        P::U16 => IrType::U16,
        P::U32 => IrType::U32,
        P::U64 => IrType::U64,
        P::U128 => IrType::U128,
        P::F32 => IrType::F32,
        P::F64 => IrType::F64,
        P::Bool => IrType::U1,
        // TODO: is mapping never to unit correct?
        P::Unit | P::Never => IrType::Unit,
        P::Type => IrType::U64, // TODO
    }
}

pub fn type_from_layout(ir_types: &mut IrTypes, layout: ir::Layout) -> IrType {
    if layout.size == 0 {
        debug_assert_eq!(layout.align.get(), 1);
        return IrType::Unit;
    }
    let base_type = match layout.align.get() {
        1 => IrType::U8,
        2 => IrType::U16,
        4 => IrType::U32,
        8 => IrType::U64,
        16 => IrType::U128,
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
            .chain(std::iter::repeat(IrType::U8).take(u8_count as usize)),
    );
    IrType::Tuple(final_layout)
}
