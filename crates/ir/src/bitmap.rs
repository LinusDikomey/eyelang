pub struct Bitmap {
    bits: Vec<u8>,
}
impl Bitmap {
    pub fn new(size: usize) -> Self {
        Self {
            bits: vec![0; size.div_ceil(8)],
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
}
