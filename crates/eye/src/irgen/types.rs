use std::rc::Rc;

use id::TypeId;
use ir::{IrType, IrTypes, TypeRefs};
use types::Type;

use crate::{
    compiler::ResolvedTypeDef,
    type_table::{LocalTypeIds, TypeInfo, TypeTable},
    Compiler,
};

pub fn get(
    compiler: &mut Compiler,
    ir_types: &mut IrTypes,
    ty: &Type,
    generics: TypeRefs,
) -> IrType {
    match ty {
        Type::Primitive(p) => get_primitive(*p),
        &Type::Generic(i) => ir_types[generics.nth(i.into())],
        Type::Invalid => todo!("whole function is invalid"),
        Type::Pointer(_) => IrType::Ptr,
        Type::Array(b) => {
            let (elem, size) = &**b;
            let elem = get(compiler, ir_types, elem, generics);
            let elem = ir_types.add(elem);
            IrType::Array(elem, *size)
        }
        Type::TraitSelf => todo!(),
        Type::Tuple(elems) => IrType::Tuple(get_multiple(compiler, ir_types, elems, generics)),
        Type::DefId {
            id,
            generics: def_generics,
        } => {
            let def_generics = def_generics
                .as_ref()
                .expect("TODO: handle missing generics"); // TODO
            let def_generics = get_multiple(compiler, ir_types, def_generics, generics);
            get_def(compiler, ir_types, *id, def_generics)
        }
        Type::LocalEnum(_) => todo!("local enums"),
    }
}

pub fn get_multiple(
    compiler: &mut Compiler,
    ir_types: &mut IrTypes,
    types: &[Type],
    generics: TypeRefs,
) -> ir::TypeRefs {
    let refs = ir_types.add_multiple(types.iter().map(|_| IrType::Unit));
    for (elem, ty) in types.iter().zip(refs.iter()) {
        let elem = get(compiler, ir_types, elem, generics);
        ir_types.replace(ty, elem);
    }
    refs
}

pub fn get_def(
    compiler: &mut Compiler,
    ir_types: &mut IrTypes,
    def: TypeId,
    generics: TypeRefs,
) -> IrType {
    let resolved = compiler.get_resolved_type_def(def);
    let def = Rc::clone(&resolved.def);
    match &*def {
        ResolvedTypeDef::Struct(def) => {
            let elems = ir_types.add_multiple((0..def.fields.len()).map(|_| IrType::Unit));
            for ((_, field), r) in def.fields.iter().zip(elems.iter()) {
                let ty = get(compiler, ir_types, field, generics);
                ir_types.replace(r, ty)
            }
            IrType::Tuple(elems)
        }
        ResolvedTypeDef::Enum(def) => {
            let mut accumulated_layout = ir::Layout::EMPTY;
            let ordinal_type = int_from_variant_count(def.variants.len() as u32);
            for (_variant_name, args) in &*def.variants {
                let elems = ir_types.add_multiple((0..args.len() + 1).map(|_| IrType::Unit));
                let mut elem_iter = elems.iter();
                ir_types.replace(elem_iter.next().unwrap(), ordinal_type);
                for (arg, r) in args.iter().zip(elem_iter) {
                    let elem = get(compiler, ir_types, arg, generics);
                    ir_types.replace(r, elem);
                }
                let variant_layout = ir::type_layout(IrType::Tuple(elems), ir_types);
                accumulated_layout.accumulate_variant(variant_layout);
            }
            type_from_layout(ir_types, accumulated_layout)
        }
    }
}

pub fn get_from_info(
    compiler: &mut Compiler,
    types: &TypeTable,
    ir_types: &mut IrTypes,
    ty: TypeInfo,
    generics: TypeRefs,
) -> IrType {
    match ty {
        TypeInfo::Primitive(p) => get_primitive(p),
        TypeInfo::Integer => IrType::I32,
        TypeInfo::Float => IrType::F32,
        TypeInfo::TypeDef(id, inner_generics) => {
            let inner_generics =
                get_multiple_infos(compiler, types, ir_types, inner_generics, generics);
            get_def(compiler, ir_types, id, inner_generics)
        }
        TypeInfo::Pointer(_) => IrType::Ptr,
        TypeInfo::Array {
            element,
            count: Some(count),
        } => {
            let element = get_from_info(compiler, types, ir_types, types[element], generics);
            IrType::Array(ir_types.add(element), count)
        }
        TypeInfo::Enum(id) => {
            let mut accumulated_layout = ir::Layout::EMPTY;
            let variants = types.get_enum_variants(id);
            for &variant in variants {
                let variant = &types[variant];
                let args =
                    get_multiple_infos(compiler, types, ir_types, variant.args, TypeRefs::EMPTY);
                let variant_layout = ir::type_layout(IrType::Tuple(args), ir_types);
                accumulated_layout.accumulate_variant(variant_layout);
            }
            type_from_layout(ir_types, accumulated_layout)
        }
        TypeInfo::Tuple(members) => {
            let member_refs = ir_types.add_multiple((0..members.count).map(|_| IrType::Unit));
            for (ty, r) in members.iter().zip(member_refs.iter()) {
                let ty = get_from_info(compiler, types, ir_types, types[ty], generics);
                ir_types.replace(r, ty);
            }
            IrType::Tuple(member_refs)
        }
        TypeInfo::Generic(id) => ir_types[generics.nth(id.into())],
        TypeInfo::Unknown
        | TypeInfo::TypeItem { .. }
        | TypeInfo::Array {
            element: _,
            count: None,
        }
        | TypeInfo::FunctionItem { .. }
        | TypeInfo::ModuleItem(_)
        | TypeInfo::MethodItem { .. }
        | TypeInfo::EnumVariantItem { .. }
        | TypeInfo::Invalid => panic!("incomplete type during lowering to ir: {ty:?}"),
    }
}

pub fn get_multiple_infos(
    compiler: &mut Compiler,
    types: &TypeTable,
    ir_types: &mut IrTypes,
    ids: LocalTypeIds,
    generics: TypeRefs,
) -> TypeRefs {
    let refs = ir_types.add_multiple((0..ids.count).map(|_| IrType::Unit));
    for (ty, r) in ids.iter().zip(refs.iter()) {
        let ty = get_from_info(compiler, types, ir_types, types[ty], generics);
        ir_types.replace(r, ty);
    }
    refs
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
