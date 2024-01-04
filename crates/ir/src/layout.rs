use std::num::NonZeroU64;

use crate::{ir_types::{IrTypes, IrType}, Primitive};

#[derive(Clone, Copy)]
pub struct Layout {
    pub size: u64,
    pub align: NonZeroU64,
}
/// can't have shit
const fn fucking_unwrap(option: Option<NonZeroU64>) -> NonZeroU64 {
    match option {
        Some(value) => value,
        None => loop { } // fuck you
    }
}
impl Layout {
    // TODO: architecture dependent
    pub const PTR: Self = Self { size: 8, align: fucking_unwrap(NonZeroU64::new(8)) };
    pub const EMPTY: Self = Self { size: 0, align: fucking_unwrap(NonZeroU64::new(1)) };

    pub fn stride(&self) -> u64 {
        self.size.div_ceil(self.align.get()) * self.align.get()
    }

    pub fn accumulate(&mut self, other: Self) {
        self.align = self.align.max(other.align); // TODO: max is not sufficient
        self.size = self.size.div_ceil(other.align.get()) * other.align.get() + other.size;
    }

    pub fn accumulate_variant(&mut self, variant: Layout) {
        self.align = self.align.max(variant.align) // TODO: max is not sufficient
    }

    pub fn array(element: Self, size: u64) -> Self {
        Self {
            size: element.stride() * size,
            align: element.align,
        }
    }
}

pub fn type_layout<'a>(ty: IrType, types: &IrTypes) -> Layout {
    match ty {
        IrType::Primitive(p) => primitive_layout(p),
        IrType::Array(elem_ty, count) => Layout::array(type_layout(types[elem_ty], types), count as u64),
        IrType::Tuple(elems) => {
            let mut layout = Layout::EMPTY;
            for ty in elems.iter() {
                layout.accumulate(type_layout(types[ty], types));
            }
            layout
        }
        IrType::Enum(variants) => {
            let tag_layout = layout_from_variant_count(variants.len());
            let mut layout = tag_layout;

            for variant in variants.iter() {
                let IrType::Tuple(args) = types[variant] else { panic!("invalid IrType found") };
                let mut variant_layout = tag_layout;
                for arg in args.iter() {
                    variant_layout.accumulate(type_layout(types[arg], types));
                }
                layout.accumulate_variant(variant_layout);
            }
            layout
        }
        IrType::Const(_) => todo!("const IrType layout"),
        IrType::Ref(r) => type_layout(types[r], types),
    }
}

pub fn primitive_layout(ty: Primitive) -> Layout {
    use Primitive as P;
    match ty {
        P::I8 | P::U8 | P::U1 => Layout { size: 1, align: 1.try_into().unwrap() },
        P::I16 | P::U16 => Layout { size: 2, align: 2.try_into().unwrap() },
        P::I32 | P::U32 | P::F32 => Layout { size: 4, align: 4.try_into().unwrap() },
        P::I64 | P::U64 | P::F64 => Layout { size: 8, align: 8.try_into().unwrap() },
        P::I128 | P::U128 => Layout { size: 16, align: 16.try_into().unwrap() },
        P::Unit => Layout::EMPTY,
        P::Ptr => Layout::PTR, // TODO: architecture dependent pointer sizes
    }
}

fn layout_from_variant_count(count: usize) -> Layout {
    if count == 0 { return Layout::EMPTY }
    let bytes = match ((count - 1).ilog2() as u64 + 1).div_ceil(8) {
        1 => 1,
        2 => 2,
        3 | 4 => 4,
        5..=8 => 8,
        _ => unreachable!()
    };
    Layout { size: bytes, align: bytes.try_into().unwrap() }
}
