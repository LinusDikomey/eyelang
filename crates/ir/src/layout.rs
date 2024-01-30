use std::num::NonZeroU64;

use crate::{ir_types::{IrTypes, IrType}, TypeRefs};

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

    pub fn align_for(&mut self, align: NonZeroU64) {
        self.align = self.align.max(align);
        self.size = self.size.div_ceil(align.get()) * align.get();
    }

    pub fn accumulate(&mut self, other: Self) {
        self.align = self.align.max(other.align);
        self.size = self.size.div_ceil(other.align.get()) * other.align.get() + other.size;
    }

    pub fn accumulate_variant(&mut self, variant: Layout) {
        self.align = self.align.max(variant.align)
    }

    pub fn array(element: Self, size: u64) -> Self {
        Self {
            size: element.stride() * size,
            align: element.align,
        }
    }
}

pub fn type_layout<'a>(ty: IrType, types: &IrTypes) -> Layout {
    use IrType as T;
    match ty {
        T::I8 | T::U8 | T::U1 => Layout { size: 1, align: 1.try_into().unwrap() },
        T::I16 | T::U16 => Layout { size: 2, align: 2.try_into().unwrap() },
        T::I32 | T::U32 | T::F32 => Layout { size: 4, align: 4.try_into().unwrap() },
        T::I64 | T::U64 | T::F64 => Layout { size: 8, align: 8.try_into().unwrap() },
        T::I128 | T::U128 => Layout { size: 16, align: 16.try_into().unwrap() },
        T::Unit => Layout::EMPTY,
        T::Ptr => Layout::PTR, // TODO: architecture dependent pointer sizes
        IrType::Array(elem_ty, count) => Layout::array(type_layout(types[elem_ty], types), count as u64),
        IrType::Tuple(elems) => {
            let mut layout = Layout::EMPTY;
            for ty in elems.iter() {
                layout.accumulate(type_layout(types[ty], types));
            }
            layout
        }
        IrType::Const(_) => todo!("const IrType layout"),
    }
}

pub fn offset_in_tuple(elem_types: TypeRefs, elem_idx: u32, types: &IrTypes) -> u64 {
    let mut layout = Layout::EMPTY;
    for ty in elem_types.iter().take(elem_idx as usize) {
        layout.accumulate(type_layout(types[ty], types));
    }
    let elem_ty = elem_types.nth(elem_idx);
    let elem_layout = type_layout(types[elem_ty], types);
    layout.align_for(elem_layout.align);
    layout.size
}
