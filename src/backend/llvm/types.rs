use llvm_sys::{
    prelude::{LLVMContextRef, LLVMTypeRef},
    core::*,
};

use crate::{
    types::{Primitive, Layout},
    resolve::{types::{Type, Enum, ResolvedTypeDef, Struct}, self},
    ir::{self, types::{IrTypes, TypeRefs, IrType}},
    ast::TypeId
};

use super::TypeInstance;


#[derive(Clone, Copy, Debug)]
pub enum Numeric { Float(u32), Int(bool, u32) }
impl Numeric {
    pub fn float(self) -> bool { matches!(self, Numeric::Float(_)) }
    pub fn int(self) -> bool { matches!(self, Numeric::Int(_, _)) }
}
impl From<Primitive> for Numeric {
    fn from(value: Primitive) -> Self {
        if let Some(p) = value.as_int() {
            Numeric::Int(p.is_signed(), p.bit_count())
        } else if let Some(p) = value.as_float() {
            Numeric::Float(p.bit_count())
        } else {
            panic!("Invalid type for int/float operation: {value}")
        }
    }
}

pub(super) unsafe fn llvm_global_ty(
    ctx: LLVMContextRef,
    ty: &Type,
    module: &ir::Module,
    type_instances: &mut [TypeInstance]
) -> LLVMTypeRef {
    llvm_global_ty_instanced(ctx, ty, module, type_instances, &[])
}

pub(super) unsafe fn llvm_global_ty_instanced(
    ctx: LLVMContextRef,
    ty: &Type,
    module: &ir::Module,
    instances: &mut [TypeInstance],
    generics: &[Type]
) -> LLVMTypeRef {
    match ty {
        resolve::types::Type::Prim(p) => llvm_primitive_ty(ctx, *p),
        resolve::types::Type::Id(id, generics) => get_id_ty(*id, generics, ctx, module, instances).0,
        resolve::types::Type::Pointer(_) => LLVMPointerTypeInContext(ctx, 0),
        resolve::types::Type::Array(inner) => {
            let (inner, size) = &**inner;
            LLVMArrayType(llvm_global_ty(ctx, inner, module, instances), *size)
        }
        resolve::types::Type::Enum(variants) => int_from_variant_count(ctx, variants.len()),
        resolve::types::Type::Tuple(elems) => {
            let mut layout = Layout::EMPTY;
            for elem in elems {
                layout.accumulate(elem.layout(|id| &module.types[id.idx()].1, generics))
            }
            LLVMArrayType(LLVMInt8TypeInContext(ctx), layout.size as _)
        }
        resolve::types::Type::Generic(i) => llvm_global_ty_instanced(ctx, &generics[*i as usize], module, instances, generics),
        resolve::types::Type::Invalid => unreachable!(),
    }
}

pub(super) unsafe fn llvm_ty(
    ctx: LLVMContextRef,
    module: &ir::Module,
    types: &IrTypes,
    type_instances: &mut [TypeInstance],
    ty: IrType
) -> LLVMTypeRef {
    llvm_ty_recursive(ctx, module, types, type_instances, ty, false, TypeRefs::EMPTY)
}

pub(super) unsafe fn int_from_variant_count(ctx: LLVMContextRef, count: usize) -> LLVMTypeRef {
    if count < 2 {
        LLVMVoidTypeInContext(ctx)
    } else {
        llvm_primitive_ty(
            ctx,
            Enum::int_ty_from_variant_count(count as _).map_or(Primitive::Unit, |ty| ty.into())
        )
    }
}

pub unsafe fn llvm_primitive_ty(ctx: LLVMContextRef, p: Primitive) -> LLVMTypeRef {
    use crate::types::Primitive::*;
    match p {
        I8 | U8 => LLVMInt8TypeInContext(ctx),
        I16 | U16 => LLVMInt16TypeInContext(ctx),
        I32 | U32 => LLVMInt32TypeInContext(ctx),
        I64 | U64 => LLVMInt64TypeInContext(ctx),
        I128 | U128 => LLVMInt128TypeInContext(ctx),
        F32 => LLVMFloatTypeInContext(ctx),
        F64 => LLVMDoubleTypeInContext(ctx),
        Bool => LLVMInt1TypeInContext(ctx),
        Unit | Never | Type => LLVMVoidTypeInContext(ctx),
    }
}

pub(super) unsafe fn get_id_ty<'a>(
    id: TypeId,
    generics: &[Type],
    ctx: LLVMContextRef,
    module: &ir::Module,
    instances: &'a mut [TypeInstance]
) -> (LLVMTypeRef, &'a [u32]) {
    match &instances[id.idx()] {
        TypeInstance::Simple(simple, _) => {
            debug_assert_eq!(generics.len(), 0);
            // getting the value here again to prevent an ownership error
            let TypeInstance::Simple(_, offsets) = &instances[id.idx()] else { unreachable!() };
            (*simple, offsets)
        }
        TypeInstance::Generic(map) => {
            if let Some((ty, _)) = map.get(generics) {
                // getting the value here again to prevent an ownership error
                let TypeInstance::Generic(map) = &instances[id.idx()] else { unreachable!() };
                (*ty, &map[generics].1)
            } else {
                /*
                let mut name = format!("t{}[", id.idx());

                for (i, ty) in generics.iter().enumerate() {
                    use std::fmt::Write;
                    if i != 0 {
                        name.push_str(",");
                    }
                    name.write_fmt(format_args!("{ty:?}")).unwrap();
                }
                name.push(']');
                let name = ffi::CString::new(name).unwrap();
                */

                let (ty, offsets) = match &module.types[id.idx()].1 {
                    ResolvedTypeDef::Struct(def) => {
                        struct_ty(ctx, def, module, generics)
                    }
                    ResolvedTypeDef::Enum(def) => {
                        (int_from_variant_count(ctx, def.variants.len()), vec![])
                    }
                };

                let TypeInstance::Generic(map) = &mut instances[id.idx()] else { unreachable!() };
                map.insert(generics.to_vec(), (ty, offsets));
                (ty, &map[generics].1)
            }
        }
    }
}

pub fn struct_ty(ctx: LLVMContextRef, def: &Struct, module: &ir::Module, generics: &[Type]) -> (LLVMTypeRef, Vec<u32>) {
    let mut layout = Layout::EMPTY;
    let member_offsets = def.members.iter()
        .map(|(_, ty)| {
            let offset = layout.size;
            layout.accumulate(ty.layout(|id| &module.types[id.idx()].1, generics));

            offset as _
        }).collect::<Vec<_>>();
    (unsafe { LLVMArrayType(LLVMInt8TypeInContext(ctx), layout.size as _) }, member_offsets)
}

unsafe fn llvm_ty_recursive(
    ctx: LLVMContextRef,
    module: &ir::Module,
    types: &IrTypes,
    type_instances: &mut [TypeInstance],
    ty: IrType,
    pointee: bool,
    generics: TypeRefs,
) -> LLVMTypeRef {
    match ty {
        IrType::Primitive(Primitive::Unit) if pointee => llvm_primitive_ty(ctx, Primitive::I8),
        IrType::Primitive(p) => llvm_primitive_ty(ctx, p),
        IrType::Id(id, generics) => {
            // PERF: alllocating a Vec here each time
            let generics: Vec<_> = generics.iter().map(|ty| types[ty].as_resolved_type(types)).collect();
            get_id_ty(id, &generics, ctx, module, type_instances).0
        }
        IrType::Ptr(_) => LLVMPointerTypeInContext(ctx, 0),
        IrType::Array(inner, count) => {
            let elem_ty = llvm_ty_recursive(ctx, module, types, type_instances, types[inner], false, generics);
            LLVMArrayType(elem_ty, count)
        }
        IrType::Tuple(elems) => {
            let mut layout = Layout::EMPTY;
            for elem in elems.iter() {
                layout.accumulate(types[elem].layout(types, |id| &module.types[id.idx()].1));
            }
            LLVMArrayType(LLVMInt8TypeInContext(ctx), layout.size as _)
        }
        IrType::Ref(idx) => llvm_ty_recursive(ctx, module, types, type_instances, types[idx], pointee, generics),
    }
}
