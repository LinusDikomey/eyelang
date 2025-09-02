#[derive(Clone)]
pub struct Bitmap {
    bits: Vec<u8>,
}
impl Bitmap {
    pub fn new(size: usize) -> Self {
        Self {
            bits: vec![0; size.div_ceil(8)],
        }
    }

    pub fn new_with_ones(size: usize) -> Self {
        Self {
            bits: vec![u8::MAX; size.div_ceil(8)],
        }
    }

    pub fn get(&self, index: usize) -> bool {
        self.bits[index / 8] & (1 << (index % 8)) != 0
    }

    pub fn set(&mut self, index: usize, value: bool) {
        if value {
            self.bits[index / 8] |= 1 << (index % 8);
        } else {
            self.bits[index / 8] &= !(1 << (index % 8));
        }
    }

    pub fn visit_set_bits(&self, mut on_set: impl FnMut(usize)) {
        for (i, &byte) in self.bits.iter().enumerate() {
            for bi in 0..8 {
                if byte & (1 << bi) != 0 {
                    on_set(i * 8 + bi);
                }
            }
        }
    }

    pub fn visit_unset_bits(&self, mut on_unset: impl FnMut(usize)) {
        for (i, &byte) in self.bits.iter().enumerate() {
            for bi in 0..8 {
                if byte & (1 << bi) == 0 {
                    on_unset(i * 8 + bi);
                }
            }
        }
    }

    /// performs an in-place union operation with another bitmap (assumed to be of the same size)
    /// and returns if any bits where changed
    pub fn union_with(&mut self, other: &Bitmap) -> bool {
        assert_eq!(self.bits.len(), other.bits.len());
        let mut changed = false;
        for (a, &b) in self.bits.iter_mut().zip(&other.bits) {
            if *a != b {
                changed = true;
            }
            *a |= b;
        }
        changed
    }

    pub fn clear(&mut self) {
        self.bits.fill(0);
    }
}
