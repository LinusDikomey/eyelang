use llvm_sys::{
    prelude::{LLVMContextRef, LLVMTypeRef},
    core::*,
};

use crate::{
    types::{Primitive, Layout},
    resolve::{types::{Type, Enum, Struct, ResolvedTypeBody}, self},
    ir::{self, types::{IrTypes, TypeRefs, IrType}},
    ast::{TypeId, VariantId}
};

use super::{TypeInstance, EnumLayout};


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
        Type::Prim(p) => llvm_primitive_ty(ctx, *p),
        Type::Id(id, generics) => get_id_ty(*id, generics, ctx, module, instances).0,
        Type::Pointer(_) => LLVMPointerTypeInContext(ctx, 0),
        Type::Array(inner) => {
            let (inner, size) = &**inner;
            LLVMArrayType(llvm_global_ty(ctx, inner, module, instances), *size)
        }
        Type::Tuple(elems) => {
            let mut layout = Layout::EMPTY;
            for elem in elems {
                layout.accumulate(elem.layout(|id| &module.types[id.idx()].1, generics));
            }
            LLVMArrayType(LLVMInt8TypeInContext(ctx), layout.size as _)
        }
        Type::Generic(i) => llvm_global_ty_instanced(ctx, &generics[*i as usize], module, instances, generics),
        Type::LocalEnum(variants) => {
            let int_ty = Enum::int_ty_from_variant_count(variants.len() as _);
            let tag_layout = int_ty
                .map_or(Layout::EMPTY, |ty| Primitive::from(ty).layout());
            let mut layout = tag_layout;

            for variant in variants {
                let mut variant_layout = tag_layout;
                for arg in variant {
                    variant_layout.accumulate(arg.layout(|id| &module.types[id.idx()].1, generics));
                }
                layout.add_variant(variant_layout);
            }

            if layout == tag_layout {
                int_ty.map_or_else(|| LLVMVoidTypeInContext(ctx), |ty| llvm_primitive_ty(ctx, Primitive::from(ty)))
            } else {
                LLVMArrayType(LLVMInt8TypeInContext(ctx), layout.size as _)
            }
        }
        Type::TraitSelf => unreachable!(),
        Type::Invalid => unreachable!(),
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

pub(super) enum OffsetsRef<'a> {
    Struct(&'a [u32]),
    Enum(&'a EnumLayout),
}

pub(super) unsafe fn get_id_ty<'a>(
    id: TypeId,
    generics: &[Type],
    ctx: LLVMContextRef,
    module: &ir::Module,
    instances: &'a mut [TypeInstance]
) -> (LLVMTypeRef, OffsetsRef<'a>) {
    match &instances[id.idx()] {
        TypeInstance::Simple(simple, _) => {
            debug_assert_eq!(generics.len(), 0);
            // getting the value here again to prevent an ownership error
            let TypeInstance::Simple(_, offsets) = &instances[id.idx()] else { unreachable!() };
            (*simple, OffsetsRef::Struct(offsets))
        }
        TypeInstance::SimpleEnum(simple, _) => {
            debug_assert_eq!(generics.len(), 0);
            let TypeInstance::SimpleEnum(_, offsets) = &instances[id.idx()] else { unreachable!() };
            (*simple, OffsetsRef::Enum(offsets))
        }
        TypeInstance::Generic(map) => {
            if let Some((ty, _)) = map.get(generics) {
                // getting the value here again to prevent an ownership error
                let TypeInstance::Generic(map) = &instances[id.idx()] else { unreachable!() };
                (*ty, OffsetsRef::Struct(&map[generics].1))
            } else {
                let ResolvedTypeBody::Struct(def) = &module.types[id.idx()].1.body else { unreachable!() };
                let (ty, offsets) = struct_ty(ctx, def, module, generics);

                let TypeInstance::Generic(map) = &mut instances[id.idx()] else { unreachable!() };
                map.insert(generics.to_vec(), (ty, offsets));
                (ty, OffsetsRef::Struct(&map[generics].1))
            }
        }
        TypeInstance::GenericEnum(map) => {
            if let Some((ty, _)) = map.get(generics) {
                // getting the value here again to prevent an ownership error
                let TypeInstance::GenericEnum(map) = &instances[id.idx()] else { unreachable!() };
                (*ty, OffsetsRef::Enum(&map[generics].1))
            } else {
                let ResolvedTypeBody::Enum(def) = &module.types[id.idx()].1.body else { unreachable!() };
                let (ty, offsets) = enum_ty(ctx, def, module, generics);
                let TypeInstance::GenericEnum(map) = &mut instances[id.idx()] else { unreachable!() };
                map.insert(generics.to_vec(), (ty, offsets));
                (ty, OffsetsRef::Enum(&map[generics].1))
            }
        }
    }
}

pub fn struct_ty(ctx: LLVMContextRef, def: &Struct, module: &ir::Module, generics: &[Type]) -> (LLVMTypeRef, Vec<u32>) {
    let mut layout = Layout::EMPTY;
    let member_offsets = def.members.iter()
        .map(|(_, ty)| {
            layout.accumulate(ty.layout(|id| &module.types[id.idx()].1, generics))
        }).collect::<Vec<_>>();
    (unsafe { LLVMArrayType(LLVMInt8TypeInContext(ctx), layout.size as _) }, member_offsets)
}

pub fn enum_ty(ctx: LLVMContextRef, def: &Enum, module: &ir::Module, generics: &[Type]) -> (LLVMTypeRef, EnumLayout) {
    enum_ty_with_fn(ctx, def.variants.len() as _, |variant_idx, layout| {
        // PERF: searching for the variant id is suboptimal, maybe provide a Vec and A
        // HashMap<String, VariantId>
        let (_, (_, _, args)) = def.variants.iter()
            .find(|(_, (id, _, _))| *id == variant_idx)
            .unwrap();
        args.iter().map(|arg| {
            layout.accumulate(arg.layout(|id| &module.types[id.idx()].1, generics))
        }).collect()
    })
}

fn enum_ty_with_fn(ctx: LLVMContextRef, variant_count: u16, variant: impl Fn(VariantId, &mut Layout) -> Vec<u32>)
-> (LLVMTypeRef, EnumLayout) {
    let int_ty = Enum::int_ty_from_variant_count(variant_count as _);
    let tag_layout = int_ty.map_or(Layout::EMPTY, |ty| Primitive::from(ty).layout());
    let mut layout = tag_layout;
    let mut offsets = vec![Vec::new(); variant_count as usize];
    for i in 0..variant_count {
        let mut variant_layout = tag_layout;
        let variant_offsets = variant(VariantId::new(i), &mut variant_layout);
        offsets[i as usize] = variant_offsets;
        layout.add_variant(variant_layout);
    }

    if layout == tag_layout {
        let ty = unsafe {
            int_ty.map_or_else(|| LLVMVoidTypeInContext(ctx), |ty| llvm_primitive_ty(ctx, Primitive::from(ty)))
        };
        (ty, EnumLayout::TransparentTag)
    } else {
        let ty = unsafe { LLVMArrayType(LLVMInt8TypeInContext(ctx), layout.size as _) };
        (ty, EnumLayout::Variants { tag_offset: 0, arg_offsets: offsets })
    }
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
        IrType::Tuple(_) => {
            let layout = ty.layout(types, |id| &module.types[id.idx()].1);
            LLVMArrayType(LLVMInt8TypeInContext(ctx), layout.size as _)
        }
        IrType::Enum(variants) => {
            enum_ty_with_fn(ctx, variants.count as _, |variant_id, layout| {
                let IrType::Tuple(args) = types[variants.nth(variant_id.idx() as _)] else {
                    panic!("invalid type");
                };
                args.iter().map(|arg| {
                    layout.accumulate(types[arg].layout(types, |i| &module.types[i.idx()].1))
                }).collect()
            }).0
        }
        IrType::Const(_) => panic!("Invalid const type in LLVM backend"),
        IrType::Ref(idx) => llvm_ty_recursive(ctx, module, types, type_instances, types[idx], pointee, generics),
    }
}
