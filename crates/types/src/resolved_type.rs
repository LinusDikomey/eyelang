use crate::Primitive;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Primitive(Primitive),
    DefId { id: id::TypeId, generics: Box<[Type]> },
    Pointer(Box<Type>),
    Array(Box<(Type, u32)>),
    Tuple(Box<[Type]>),
    /// A generic type that will be replaced by a concrete type in generic instantiations.
    Generic(u8),
    /// a local enum that will only be created from inference
    LocalEnum(Box<[Box<[Type]>]>),
    /// Self type (only used in trait definitions)
    #[allow(dead_code)] // FIXME: remove this allow when it's used
    TraitSelf,
    Invalid,
}
impl Type {
    /*
    pub fn layout<'a>(&self, ctx: impl Fn(TypeDefId) -> &'a ResolvedTypeDef + Copy, generics: &[Type]) -> Layout {
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
            Type::TraitSelf => unreachable!("TraitSelf should always be replaced in concrete instances"),
            Type::Invalid => Layout::EMPTY,
        }
    } 
    */

    pub fn instantiate_generics(&self, generics: &[Type]) -> Self {
        match self {
            Type::Primitive(p) => Type::Primitive(*p),
            Type::DefId { id, generics: ty_generics } => Type::DefId {
                id: *id,
                generics: ty_generics
                    .iter()
                    .map(|ty| ty.instantiate_generics(generics))
                    .collect()
            },
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
            Type::TraitSelf => unreachable!(),
            Type::Invalid => Type::Invalid,
        }
    }
}
