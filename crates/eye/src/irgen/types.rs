use id::TypeId;
use ir::{IrType, IrTypes, TypeRefs};
use types::Type;

use crate::{type_table::{TypeTable, TypeInfo, LocalTypeIds}, Compiler, compiler::ResolvedTypeDef};


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
        Type::Tuple(elems) => {
            IrType::Tuple(get_multiple(compiler, ir_types, elems, generics))
        }
        Type::DefId { id, generics: def_generics } => {
            let def_generics = def_generics.as_ref().expect("TODO: handle missing generics"); // TODO
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

pub fn get_def(compiler: &mut Compiler, ir_types: &mut IrTypes, def: TypeId, generics: TypeRefs) -> IrType {
    let resolved = compiler.get_resolved_type_def(def);
    match &resolved.def {
        ResolvedTypeDef::Struct(def) => {
            // PERF: cloning struct def
            let def = def.clone();
            let elems = ir_types.add_multiple((0..def.fields.len()).map(|_| IrType::Unit));
            for ((_, field), r) in def.fields.iter().zip(elems.iter()) {
                let ty = get(compiler, ir_types, field, generics);
                ir_types.replace(r, ty)
            }
            IrType::Tuple(elems)
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
            let inner_generics = get_multiple_infos(compiler, types, ir_types, inner_generics, generics);
            get_def(compiler, ir_types, id, inner_generics)
        }
        TypeInfo::Pointer(_) => IrType::Ptr,
        TypeInfo::Array { element, count: Some(count) } => {
            let element = get_from_info(compiler, types, ir_types, types[element], generics);
            IrType::Array(ir_types.add(element), count)
        }
        TypeInfo::Enum { .. } => todo!(),
        TypeInfo::Tuple(members) => {
            let member_refs = ir_types.add_multiple(
                (0..members.count).map(|_| IrType::Unit)
            );
            for (ty, r) in members.iter().zip(member_refs.iter()) {
                let ty = get_from_info(compiler, types, ir_types, types[ty], generics);
                ir_types.replace(r, ty);
            }
            IrType::Tuple(member_refs)
        }
        TypeInfo::Generic(id) => ir_types[generics.nth(id.into())],
        TypeInfo::Unknown
        | TypeInfo::TypeItem { .. }
        | TypeInfo::Array { element: _, count: None }
        | TypeInfo::FunctionItem { .. }
        | TypeInfo::ModuleItem(_)
        | TypeInfo::MethodItem { .. }
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
        P::Bool => IrType::I8,
        // TODO: is mapping never to unit correct?
        P::Unit | P::Never => IrType::Unit,
        P::Type => IrType::U64, // TODO
    }
}
