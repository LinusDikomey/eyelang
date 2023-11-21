#![allow(clippy::disallowed_types)]

use std::collections::HashMap;

/// Use to make `HashMaps` and `HashSets` across the compiler deterministic.
pub type DHashMap<K, V> = HashMap<K, V, DeterministicState>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct DeterministicState;
impl std::hash::BuildHasher for DeterministicState {
    type Hasher = std::collections::hash_map::DefaultHasher;

    fn build_hasher(&self) -> Self::Hasher {
        std::collections::hash_map::DefaultHasher::new()
    }
}

pub fn new<K, V>() -> DHashMap<K, V> {
    DHashMap::with_hasher(DeterministicState)
}
pub fn with_capacity<K, V>(capacity: usize) -> DHashMap<K, V> {
    DHashMap::with_capacity_and_hasher(capacity, DeterministicState)
}

