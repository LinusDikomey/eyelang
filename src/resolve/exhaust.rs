use std::collections::HashSet;

use crate::dmap;

use super::types::{SymbolTable, Type, TypeDef};

#[derive(Clone, Copy)]
pub struct SignedInt(pub u128, pub bool);
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Exhaustion {
    None, // no values exhausted
    Full, // all values exhausted
    UnsignedInt(Vec<Range>),
    SignedInt {
        neg: Vec<Range>,
        pos: Vec<Range>,
    },
    Bool {
        true_: bool,
        false_: bool,
    },
    Enum(HashSet<String, dmap::DeterministicState>),
    Tuple(Vec<Exhaustion>),
    Invalid,
}
impl Default for Exhaustion {
    fn default() -> Self { Self::None }
}
impl Exhaustion {
    pub fn is_exhausted(&self, ty: Option<&Type>, symbols: &SymbolTable) -> Option<bool> {
        Some(match self {
            Exhaustion::None => false,
            Exhaustion::Full => true,
            Exhaustion::UnsignedInt(ranges) => {
                match ty {
                    Some(Type::Prim(p)) if p.is_int() => {
                        let int = p.as_int().unwrap();
                        if int.is_signed() { return Some(false) }

                        ranges.first().map_or(false, |r| r.start == 0 && r.end >= int.max())
                    }
                    _ => return None
                }
            },
            Exhaustion::SignedInt { neg, pos } => {
                match ty {
                    Some(Type::Prim(p)) if p.is_int() => {
                        let int = p.as_int().unwrap();

                        pos.first().map_or(false, |r| r.start == 0 && r.end >= int.max()) &&
                        neg.first().map_or(false, |r| r.start == 0 && r.end >= int.min())
                    }
                    _ => return None
                }
            }
            Exhaustion::Enum(exhausted_variants) => {
                match ty {
                    Some(Type::Enum(variants)) => variants.iter().all(|v| exhausted_variants.contains(v)),
                    Some(Type::Id(symbol, _generics)) => {
                        match &symbols.get_type(*symbol) {
                            TypeDef::Enum(enum_def) => {
                                enum_def.variants.iter().all(|(v, _)| exhausted_variants.contains(v))
                            }
                            _ => return None
                        }
                    }
                    _ => return None
                }
            }
            &Exhaustion::Bool { true_, false_ } => true_ && false_,
            Exhaustion::Tuple(members) => {
                let mut member_types = match ty {
                    Some(Type::Tuple(member_types)) => {
                        if member_types.len() != members.len() { return None };
                        Some(member_types.iter())
                    }
                    None => None,
                    _ => return None
                };
                
                let mut exhausted = true;
                for member in members {
                    let ty = match &mut member_types {
                        Some(member_types) => Some(member_types.next().unwrap()),
                        None => None
                    };
                    match member.is_exhausted(ty, symbols) {
                        Some(true) => {}
                        Some(false) => exhausted = false,
                        None => return None
                    }
                    
                }
                exhausted
            }
            Exhaustion::Invalid => return None,
        })
    }

    pub fn exhaust_full(&mut self) {
        *self = Exhaustion::Full;
    }

    /// exhaust an integer value and return true if it wasn't covered yet
    pub fn exhaust_int(&mut self, x: SignedInt) -> bool {
        self.exhaust_int_range(x, x)
    }

    /// exhaust an integer range and return true if it wasn't fully covered yet
    pub fn exhaust_int_range(&mut self, mut start: SignedInt, mut end: SignedInt) -> bool {
        fn exhaust(ranges: &mut Vec<Range>, start: u128, end: u128) -> bool {
            if ranges.is_empty() {
                ranges.push(Range { start, end });
                true
            } else {
                if end + 1 < ranges.first().unwrap().start {
                    ranges.insert(0, Range { start, end });
                    return true;
                }
                for i in 0..ranges.len()-1 {
                    let next_range = ranges[i+1];
                    let range = &mut ranges[i];
                    if let Some(merged) = merge_ranges(*range, Range { start, end }) {
                        if let Some(merged) = merge_ranges(merged, next_range) {
                            debug_assert!(merged.start < range.start || merged.end > range.end);
                            *range = merged;
                            ranges.remove(i+1);
                            return true;
                        }
                        debug_assert!(merged.start < range.start || merged.end > range.end);
                        *range = merged;
                        return true;
                    } else if end < next_range.start {
                        ranges.insert(i, Range { start, end });
                        return true;
                    }
                }
                let last = ranges.last_mut().unwrap();
                if let Some(merged) = merge_ranges(Range { start, end }, *last) {
                    debug_assert!(merged.start < last.start || merged.end > last.end || (merged == *last));
                    *last = merged;
                    true
                } else {
                    ranges.push(Range { start, end });
                    true
                }
            }
        }
        if start.1 && start.0 == 0 {
            start = SignedInt(0, false);
        }
        if end.1 && end.0 == 0 {
            end = SignedInt(0, false);
        }
        match self {
            Self::None => {
                *self = match (start.1, end.1) {
                    (false, false) => Self::UnsignedInt(vec![Range::new(start.0, end.0)]),
                    (true, false) => Self::SignedInt {
                        neg: vec![Range::new(0, start.0)],
                        pos: vec![Range::new(0, end.0)]
                    },
                    (true, true) => Self::SignedInt { neg: vec![Range::new(start.0, end.0)], pos: vec![] },
                    (false, true) => unreachable!()
                };
                true
            },
            Self::UnsignedInt(ranges) => {
                if start.1 {
                    let Self::UnsignedInt(mut ranges) = std::mem::take(self) else { unreachable!() };
                    *self = Self::SignedInt {
                        neg: vec![Range::new(if end.1 { end.0 } else { 0 }, start.0)],
                        pos: if end.1 { ranges } else {
                            exhaust(&mut ranges, 0, end.0);
                            ranges
                        }
                    };
                    true
                } else {
                    exhaust(ranges, start.0, end.0)
                }
            }
            Self::SignedInt { neg, pos } => {
                if start.1 {
                    let mut new_values = exhaust(neg, if end.1 { end.0 } else { 0 }, start.0);
                    if !end.1 {
                        new_values |= exhaust(pos, 0, end.0);
                    }
                    new_values
                } else {
                    exhaust(pos, start.0, end.0)
                }
            }
            Self::Full => false,
            _ => {
                *self = Self::Invalid;
                false
            }
        }
    }
    
    pub fn exhaust_bool(&mut self, b: bool) -> bool {
        match self {
            Self::None => {
                *self = Self::Bool { true_: b, false_: !b };
                true
            }
            Self::Bool { true_, false_ } => {
                if b {
                    let prev = *true_;
                    *true_ = true;
                    prev
                } else {
                    let prev = *false_;
                    *false_ = true;
                    prev
                }
            }
            Self::Full => false,
            _ => {
                *self = Self::Invalid;
                false
            }
        }
    }

    pub fn exhaust_enum_variant(&mut self, variant: String) -> bool {
        match self {
            Self::None => {
                let mut set = HashSet::with_capacity_and_hasher(1, dmap::DeterministicState);
                set.insert(variant);
                *self = Self::Enum(set);
                true
            }
            Self::Enum(variants) => variants.insert(variant),
            Self::Full => false,
            _ => {
                *self = Self::Invalid;
                false
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Range { pub start: u128, pub end: u128 }
impl Range {
    pub fn new(start: u128, end: u128) -> Self {
        Self { start, end }
    }
}
fn merge_ranges(a: Range, b: Range) -> Option<Range> {
    if a.start < b.start {
        if a.end < b.start.saturating_sub(1) {
            None
        } else {
            Some(Range::new(a.start, a.end.max(b.end)))
        }
    } else if b.end < a.start.saturating_sub(1) {
        None
    } else {
        Some(Range::new(b.start, b.end.max(a.end)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ranges() {
        let mut e = Exhaustion::None;
        e.exhaust_int(SignedInt(6, false));
        e.exhaust_int(SignedInt(1, false));
        e.exhaust_int(SignedInt(3, false));
        e.exhaust_int(SignedInt(2, false));
        e.exhaust_int(SignedInt(5, true));
        e.exhaust_int(SignedInt(8, true));
        e.exhaust_int_range(SignedInt(7, true), SignedInt(6, true));
        debug_assert_eq!(e, Exhaustion::SignedInt {
            neg: vec![Range::new(5, 8)],
            pos: vec![Range::new(1, 3), Range::new(6, 6)]
        });

        let mut e = Exhaustion::None;
        e.exhaust_int_range(SignedInt(3, true), SignedInt(5, false));
        debug_assert_eq!(e, Exhaustion::SignedInt {
            neg: vec![Range::new(0, 3)],
            pos: vec![Range::new(0, 5)]
        });
        e.exhaust_int_range(SignedInt(5, true), SignedInt(4, true));
        debug_assert_eq!(e, Exhaustion::SignedInt {
            neg: vec![Range::new(0, 5)],
            pos: vec![Range::new(0, 5)]
        });
    }
}
