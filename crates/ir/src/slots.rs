use crate::{FunctionIr, Primitive, Ref, Type, Types};

pub struct Slots<V> {
    pub slots: Vec<V>,
    pub slot_map: Vec<u32>,
}
impl<V: Copy> Slots<V> {
    pub fn with_default(ir: &FunctionIr, types: &Types, default: V) -> Self {
        let mut slots = Vec::new();
        let slot_map = ir
            .insts
            .iter()
            .enumerate()
            .map(|(i, inst)| {
                let count = slot_count(types[inst.ty], types);
                let idx = slots.len() as u32;
                slots.extend(std::iter::repeat_n(default, count as usize));
                tracing::debug!(target: "slots", "%{i} = {inst:?} -> @{idx}..+{count}");
                idx
            })
            .collect();
        Self { slots, slot_map }
    }

    pub fn get(&self, r: Ref) -> &[V] {
        let r = r.into_ref().expect("Can't get slots for value ref") as usize;
        let start = self.slot_map[r] as usize;
        let end = self
            .slot_map
            .get(r + 1)
            .map(|i| *i as usize)
            .unwrap_or(self.slots.len());
        tracing::debug!(target: "slots", "getting {r} -> {start}..{end} with {} slots", self.slot_map.len());
        &self.slots[start..end]
    }

    // gets an exclusive range of values
    pub fn get_range(&self, start: Ref, end: Ref) -> &[V] {
        let start = self.slot_map[start.into_ref().expect("Can't get slots for value ref") as usize]
            as usize;
        let end = self
            .slot_map
            .get(end.into_ref().expect("Can't get slots for value ref") as usize)
            .map(|i| *i as usize)
            .unwrap_or(self.slots.len());
        &self.slots[start..end]
    }
}
impl<V: Copy + Default> Slots<V> {
    pub fn new(ir: &FunctionIr, types: &Types) -> Self {
        Self::with_default(ir, types, V::default())
    }
}

pub fn slot_count(ty: Type, types: &Types) -> u32 {
    match ty {
        Type::Primitive(p) => match Primitive::try_from(p).unwrap() {
            Primitive::Unit => 0,
            Primitive::I128 | Primitive::U128 => 2,
            _ => 1,
        },
        Type::Array(type_ref, count) => slot_count(types[type_ref], types) * count,
        Type::Tuple(type_refs) => type_refs
            .iter()
            .map(|ty| slot_count(types[ty], types))
            .sum(),
    }
}
