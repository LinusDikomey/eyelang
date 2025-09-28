use std::{
    cell::{Cell, OnceCell, UnsafeCell},
    mem::MaybeUninit,
    ops::{Index, IndexMut},
};

/// An append-only List with interior mutability.
/// Provides constant-time append/index and will be able to be extended to concurrent access easily
/// later.
pub struct SegmentList<T> {
    echelons: [OnceCell<Box<[UnsafeCell<MaybeUninit<T>>]>>; 31],
    len: Cell<u32>,
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
            len: Cell::new(0),
        }
    }

    #[track_caller]
    fn get_raw(&self, index: u32) -> *mut MaybeUninit<T> {
        assert!(index < self.len.get(), "Index out of bounds of SegmentList");
        let e = Self::get_echelon(index);
        let i = index - ((1 << e) - 1);
        self.echelons[e as usize].get().unwrap()[i as usize].get()
    }

    #[track_caller]
    pub fn get(&self, index: u32) -> &T {
        let ptr = self.get_raw(index).cast_const();
        // SAFETY: the index is in-bounds of our SegmentList so the value is guaranteed to be initialized
        unsafe { MaybeUninit::assume_init_ref(&*ptr) }
    }

    #[track_caller]
    pub fn get_mut(&mut self, index: u32) -> &mut T {
        let ptr = self.get_raw(index);
        // SAFETY: the index is in-bounds of our SegmentList so the value is guaranteed to be initialized
        unsafe { MaybeUninit::assume_init_mut(&mut *ptr) }
    }

    pub fn add(&self, value: T) -> u32 {
        let offset = self.len.get();
        let (e, i) = Self::get_echelon_and_local_index(offset);
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
        self.len
            .set(offset.checked_add(1).expect("SegmentList full"));
        offset
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            list: self,
            index: 0,
            end: self.len.get(),
        }
    }

    fn get_echelon(index: u32) -> u8 {
        (index + 1).ilog2() as u8
    }

    fn get_echelon_and_local_index(index: u32) -> (u8, u32) {
        let e = (index + 1).ilog2();
        let local = index - ((1 << e) - 1);
        (e as u8, local)
    }

    pub fn is_empty(&self) -> bool {
        self.len.get() == 0
    }

    pub fn len(&self) -> u32 {
        self.len.get()
    }
}
impl<T> Index<u32> for SegmentList<T> {
    type Output = T;

    #[track_caller]
    fn index(&self, index: u32) -> &Self::Output {
        self.get(index)
    }
}
impl<T> IndexMut<u32> for SegmentList<T> {
    #[track_caller]
    fn index_mut(&mut self, index: u32) -> &mut Self::Output {
        self.get_mut(index)
    }
}
impl<T> Index<usize> for SegmentList<T> {
    type Output = T;

    #[track_caller]
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index.try_into().expect("Index out of range for u32"))
    }
}
impl<T> IndexMut<usize> for SegmentList<T> {
    #[track_caller]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_mut(index.try_into().expect("Index out of range for u32"))
    }
}

pub struct Iter<'a, T> {
    list: &'a SegmentList<T>,
    index: u32,
    end: u32,
}
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        // PERF: could implement iteration manually so that bound checks are always prevented
        let i = self.index;
        (i < self.end).then(|| {
            self.index += 1;
            self.list.get(i)
        })
    }
}

impl<A> FromIterator<A> for SegmentList<A> {
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        // PERF: special implementation here in the future might be better with preallocating echelons
        let s = SegmentList::new();
        for item in iter {
            s.add(item);
        }
        s
    }
}
