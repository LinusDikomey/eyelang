use parser::ast::Primitive;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layout {
    pub size: u64,
    pub alignment: u64,
}
impl Layout {
    pub const EMPTY: Self = Self {
        size: 0,
        alignment: 1,
    };
    // TODO: configure based on target
    pub const PTR: Self = Self {
        size: 8,
        alignment: 8,
    };

    pub fn array(elem: Layout, count: u32) -> Layout {
        Layout {
            size: elem.stride() * count as u64,
            alignment: elem.alignment,
        }
    }

    pub fn primitive(p: Primitive) -> Layout {
        let size_and_align = match p {
            Primitive::Type => 0,
            Primitive::I8 | Primitive::U8 => 1,
            Primitive::I16 | Primitive::U16 => 2,
            Primitive::I32 | Primitive::U32 | Primitive::F32 => 4,
            Primitive::I64 | Primitive::U64 | Primitive::F64 => 8,
            Primitive::I128 | Primitive::U128 => 16,
        };
        Layout {
            size: size_and_align,
            alignment: size_and_align.max(1),
        }
    }

    pub fn align(offset: u64, alignment: u64) -> u64 {
        let misalignment = offset % alignment;
        if misalignment > 0 {
            offset + alignment - misalignment
        } else {
            offset
        }
    }
    pub fn stride(&self) -> u64 {
        Self::align(self.size, self.alignment)
    }

    /// adds a member layout to the current layout while respecting alignment. Returns the start
    /// offset of the member that was just added.
    pub fn accumulate(&mut self, other: Self) -> u32 {
        let start = Self::align(self.size, other.alignment);
        *self = Self {
            size: start + other.size,
            alignment: self.alignment.max(other.alignment),
        };
        start as u32
    }
    pub fn add_variant(&mut self, variant: Self) {
        self.size = self.size.max(variant.size);
        self.alignment = self.alignment.max(variant.alignment);
    }
}

#[cfg(test)]
mod tests {
    use parser::ast::{IntType, Primitive};

    use super::*;

    fn layout(items: impl IntoIterator<Item = IntType>) -> Layout {
        let mut l = Layout::EMPTY;
        for item in items {
            l.accumulate(Layout::primitive(Primitive::from(item)));
        }
        l
    }

    #[test]
    fn basic() {
        use IntType as I;

        assert_eq!(
            layout([I::I16, I::I32]),
            Layout {
                size: 8,
                alignment: 4
            }
        );
        assert_eq!(
            layout([I::I32, I::I16]),
            Layout {
                size: 6,
                alignment: 4
            }
        );
        assert_eq!(
            layout([I::I32, I::I16, I::I32]),
            Layout {
                size: 12,
                alignment: 4
            }
        );
    }

    #[test]
    fn nested() {
        use IntType as I;

        let a = layout([I::I32, I::I16]); // 6, 4
        let mut b = Layout::EMPTY;
        b.accumulate(a);
        b.accumulate(Layout::primitive(Primitive::I32));
        assert_eq!(
            b,
            Layout {
                size: 12,
                alignment: 4
            }
        );
    }
}
