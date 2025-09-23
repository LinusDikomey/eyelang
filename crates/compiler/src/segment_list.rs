use std::{
    cell::{Cell, OnceCell, UnsafeCell},
    mem::MaybeUninit,
};

/// An append-only List with interior mutability.
/// Provides constant-time append/index and will be able to be extended to concurrent access easily
/// later.
pub struct SegmentList<T> {
    echelons: [OnceCell<Box<[UnsafeCell<MaybeUninit<T>>]>>; 31],
    offset: Cell<u32>,
}
impl<T> Default for SegmentList<T> {
    fn default() -> Self {
        Self::new()
    }
}
impl<T> SegmentList<T> {
    pub fn new() -> Self {
        let echelons = std::array::from_fn(|_| OnceCell::new());
        Self {
            echelons,
            offset: Cell::new(0),
        }
    }

    pub fn get(&self, index: u32) -> &T {
        assert!(
            index < self.offset.get(),
            "Index out of bounds of SegmentList"
        );
        let e = Self::get_echelon(index);
        let i = index - ((1 << e) - 1);
        let ptr: *const MaybeUninit<T> = self.echelons[e as usize].get().unwrap()[i as usize]
            .get()
            .cast_const();
        // SAFETY: the index is in-bounds of our SegmentList so the value is guaranteed to be initialized
        unsafe { MaybeUninit::assume_init_ref(&*ptr) }
    }

    pub fn add(&self, value: T) -> u32 {
        let offset = self.offset.get();
        let e = Self::get_echelon(offset);
        let i = offset - u32::from(e);
        if i == 0 {
            // if we are the first item in the echelon, we have to create the echelon first
            self.echelons[usize::from(e)]
                .set(
                    (0..(1 << e))
                        .map(|_| UnsafeCell::new(MaybeUninit::uninit()))
                        .collect(),
                )
                .unwrap_or_else(|_| panic!("echelon should not be initialized yet"));
        }
        let ptr: *mut MaybeUninit<T> = self.echelons[e as usize].get().unwrap()[i as usize].get();
        // SAFETY: no other access to this element is possible since all accesses are bounds-checked
        unsafe {
            let r: &mut MaybeUninit<T> = &mut *ptr;
            r.write(value);
        }
        // also do overflow check in release mode since a wrapping offset would invalidate the
        // safety invariants
        self.offset
            .set(offset.checked_add(1).expect("SegmentList full"));
        offset
    }

    fn get_echelon(index: u32) -> u8 {
        (index + 1).ilog2() as u8
    }
}
