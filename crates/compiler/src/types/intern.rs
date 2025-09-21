use std::hash::{Hash, Hasher};

use dmap::DHashMap;
use fxhash::FxHasher;
use hashbrown::HashTable;
use parser::ast::ModuleId;

use crate::{
    Type,
    compiler::{Generics, ResolvedTypeDef},
    types::{BaseType, BuiltinType, TypeFull},
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct InstanceId(u32);

pub struct SegmentList<T> {
    echelons: [Option<Box<[T]>>; 31],
    e: u8,
    i: u32,
}
impl<T: Default> SegmentList<T> {
    pub fn new() -> Self {
        let mut echelons = std::array::from_fn(|_| None);
        echelons[0] = Some(Box::new([T::default()]) as _);
        Self {
            echelons,
            e: 0,
            i: 0,
        }
    }

    pub fn get(&self, index: u32) -> &T {
        let e = Self::get_echelon(index);
        let i = index - ((1 << e) - 1);
        &self.echelons[e as usize].as_ref().unwrap()[i as usize]
    }

    pub fn add(&mut self, value: T) -> u32 {
        let cap = 1 << self.e;
        if self.i == cap {
            self.e += 1;
            self.i = 0;
            self.echelons[self.e as usize] =
                Some((0..(1 << self.e)).map(|_| T::default()).collect());
        }
        let i = self.i;
        self.echelons[self.e as usize].as_mut().unwrap()[i as usize] = value;
        self.i += 1;
        (1 << self.e) - 1 + i
    }

    fn get_echelon(index: u32) -> u8 {
        (index + 1).ilog2() as u8
    }
}

pub struct Types {
    tags: SegmentList<Tag>,
    indices: SegmentList<u32>,
    map: HashTable<Type>,

    instances: SegmentList<(BaseType, Box<[Type]>)>,
    local_enums: SegmentList<Box<[(u32, Box<[Type]>)]>>,
    bases: SegmentList<ResolvedTypeDef>,
    consts: SegmentList<u64>,
}
impl Types {
    pub fn new() -> Self {
        let mut tags = SegmentList::new();
        let mut indices = SegmentList::new();
        let mut instances = SegmentList::new();
        let mut bases = SegmentList::new();

        for (ty, i) in BuiltinType::VARIANTS.into_iter().zip(0..) {
            bases.add(ResolvedTypeDef {
                def: crate::compiler::ResolvedTypeContent::Builtin(ty),
                module: ModuleId::from_inner(0), // TODO: put something sensible here
                methods: DHashMap::default(),
                generics: Generics::EMPTY,
                inherent_trait_impls: DHashMap::default(),
            });
            let generics = ty.generics();
            if generics.count() == 0 {
                tags.add(Tag::Instance);
                indices.add(i);
                instances.add((BaseType(i), Box::new([]) as _));
            }
        }

        Self {
            tags,
            indices,
            map: HashTable::new(),

            instances,
            local_enums: SegmentList::new(),
            bases,
            consts: SegmentList::new(),
        }
    }

    pub fn intern(&mut self, ty: TypeFull) -> Type {
        let hash = hash_full(&ty);
        eprintln!("Intering {ty:?} #{hash}");
        self.map
            .find(hash, |&existing| {
                let existing_ty = self.lookup(existing);
                eprintln!("  -> candidate {existing_ty:?}");
                existing_ty == ty
            })
            .copied()
            .unwrap_or_else(|| {
                let (interned, idx) = match ty {
                    TypeFull::Instance(base, generics) => {
                        (Tag::Instance, self.instances.add((base, generics.into())))
                    }
                    TypeFull::Generic(i) => (Tag::Generic, i as u32),
                    TypeFull::LocalEnum(variants) => {
                        (Tag::LocalEnum, self.local_enums.add(variants.into()))
                    }
                };
                let ty = Type(self.tags.add(interned));
                let idx_idx = self.indices.add(idx);
                debug_assert_eq!(ty.0, idx_idx);
                eprintln!("  -> new: {ty:?} = {interned:?}");
                self.map.insert_unique(hash, ty, |&ty| {
                    hash_full(&Self::lookup_type(
                        &self.tags,
                        &self.indices,
                        &self.instances,
                        &self.local_enums,
                        ty,
                    ))
                });
                ty
            })
    }

    pub fn lookup<'a>(&'a self, ty: Type) -> TypeFull<'a> {
        Self::lookup_type(
            &self.tags,
            &self.indices,
            &self.instances,
            &self.local_enums,
            ty,
        )
    }

    fn lookup_type<'a>(
        tags: &'a SegmentList<Tag>,
        indices: &'a SegmentList<u32>,
        instances: &'a SegmentList<(BaseType, Box<[Type]>)>,
        local_enums: &'a SegmentList<Box<[(u32, Box<[Type]>)]>>,
        ty: Type,
    ) -> TypeFull<'a> {
        let idx = *indices.get(ty.0);
        match tags.get(ty.0) {
            Tag::Instance => {
                let (base, generics) = instances.get(idx);
                TypeFull::Instance(*base, generics)
            }
            Tag::Generic => TypeFull::Generic(idx as u8),
            Tag::LocalEnum => TypeFull::LocalEnum(local_enums.get(idx)),
        }
    }

    pub fn print(&self, ty: Type) {
        // match *self.types.get(ty.0) {
        //     InternedType::Nominal(s) => print!("{}", self.nominal.get(s.0)),
        //     InternedType::Tuple(elems) => {
        //         print!("(");
        //         for (i, &elem) in self.aggregates.get(elems.0).iter().enumerate() {
        //             if i != 0 {
        //                 print!(", ");
        //             }
        //             self.print(elem);
        //         }
        //         print!(")");
        //     }
        // }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Aggregate(u32);
impl Aggregate {
    pub const UNIT: Self = Self(0);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Tag {
    Instance,
    Generic,
    LocalEnum,
}
impl Default for Tag {
    fn default() -> Self {
        Self::Instance
    }
}

fn hash_full(full: &TypeFull) -> u64 {
    let mut hasher = FxHasher::default();
    Hash::hash(full, &mut hasher);
    hasher.finish()
}
