use std::num::NonZeroU64;

use crate::{PrimitiveInfo, Type, TypeIds, Types};

#[derive(Debug, Clone, Copy)]
pub struct Layout {
    pub size: u64,
    pub align: NonZeroU64,
}

impl Layout {
    // TODO: architecture dependent
    pub const PTR: Self = Self {
        size: 8,
        align: NonZeroU64::new(8).unwrap(),
    };
    pub const EMPTY: Self = Self {
        size: 0,
        align: NonZeroU64::new(1).unwrap(),
    };

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
        self.size = self.size.max(variant.size);
        self.align = self.align.max(variant.align);
    }

    pub fn array(element: Self, size: u64) -> Self {
        Self {
            size: element.stride() * size,
            align: element.align,
        }
    }
}

pub fn type_layout(ty: Type, types: &Types, primitives: &[PrimitiveInfo]) -> Layout {
    match ty {
        Type::Primitive(id) => primitives[id.0 as usize].layout(),
        Type::Array(elem, len) => {
            Layout::array(type_layout(types[elem], types, primitives), len.into())
        }
        Type::Tuple(items) => {
            let mut layout = Layout::EMPTY;
            for item in items.iter() {
                layout.accumulate(type_layout(types[item], types, primitives));
            }
            layout
        }
    }
}

pub fn offset_in_tuple(
    elem_types: TypeIds,
    elem_idx: u32,
    types: &Types,
    primitives: &[PrimitiveInfo],
) -> u64 {
    let mut layout = Layout::EMPTY;
    for ty in elem_types.iter().take(elem_idx as usize) {
        layout.accumulate(type_layout(types[ty], types, primitives));
    }
    let elem_ty = elem_types.nth(elem_idx);
    let elem_layout = type_layout(types[elem_ty], types, primitives);
    layout.align_for(elem_layout.align);
    layout.size
}
