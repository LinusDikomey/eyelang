
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layout {
    pub size: u64,
    pub alignment: u64,
}
impl Layout {
    pub const EMPTY: Self = Self { size: 0, alignment: 1 };
    pub const PTR: Self = Self { size: 8, alignment: 8 };

    pub fn align(offset: u64, alignment: u64) -> u64 {
        let misalignment = offset % alignment;
        if misalignment > 0 {
            offset + alignment - misalignment
        } else {
            offset
        }
    }
    pub fn accumulate(&mut self, other: Self) {
        *self = Self {
            size: Self::align(self.size, other.alignment) + other.size,
            alignment: self.alignment.max(other.alignment),
        };
    }
    #[must_use]
    pub fn mul_size(self, factor: u64) -> Self {
        Self {
            size: self.size * factor,
            alignment: self.alignment,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::types::{IntType, Primitive};

    use super::*;

    #[test]
    fn basic() {
        let mut l = Layout::EMPTY;
        l.accumulate(Primitive::from(IntType::I16).layout());
        l.accumulate(Primitive::from(IntType::I32).layout());

        assert_eq!(l, Layout { size: 8, alignment: 4 });
    }
}