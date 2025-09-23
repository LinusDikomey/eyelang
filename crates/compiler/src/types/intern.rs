use std::{
    cell::RefCell,
    fmt,
    hash::{Hash, Hasher},
    rc::Rc,
};

use dmap::DHashMap;
use fxhash::FxHasher;
use hashbrown::HashTable;
use parser::ast::{self, ModuleId};

use crate::{
    Type,
    compiler::{Generics, Resolvable, ResolvableTypeDef, ResolvedTypeDef},
    segment_list::SegmentList,
    types::{BaseType, BuiltinType, TypeFull},
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct InstanceId(u32);

pub struct Types {
    tags: SegmentList<Tag>,
    indices: SegmentList<u32>,
    map: RefCell<HashTable<Type>>,

    instances: SegmentList<(BaseType, Box<[Type]>)>,
    local_enums: SegmentList<Box<[(u32, Box<[Type]>)]>>,
    bases: SegmentList<ResolvableTypeDef>,
    consts: SegmentList<u64>,
}
impl Types {
    pub fn new() -> Self {
        let tags = SegmentList::new();
        let indices = SegmentList::new();
        let instances = SegmentList::new();
        let bases = SegmentList::new();

        for (builtin, i) in BuiltinType::VARIANTS.into_iter().zip(0..) {
            let module = ModuleId::from_inner(0); // TODO: put something sensible here
            let generics = builtin.generics();
            bases.add(ResolvableTypeDef {
                module,
                id: ast::TypeId::from_inner(0),
                name: builtin.name().into(),
                generic_count: generics.count(),
                resolved: crate::compiler::Resolvable::resolved(Rc::new(ResolvedTypeDef {
                    def: crate::compiler::ResolvedTypeContent::Builtin(builtin),
                    module,
                    methods: DHashMap::default(),
                    generics: Generics::EMPTY,
                    inherent_trait_impls: DHashMap::default(),
                })),
            });
            if generics.count() == 0 {
                tags.add(Tag::Instance);
                indices.add(i);
                instances.add((
                    if builtin == BuiltinType::Unit {
                        BaseType::Tuple
                    } else {
                        BaseType(i)
                    },
                    Box::new([]) as _,
                ));
            }
        }

        Self {
            tags,
            indices,
            map: RefCell::new(HashTable::new()),

            instances,
            local_enums: SegmentList::new(),
            bases,
            consts: SegmentList::new(),
        }
    }

    pub fn intern(&self, ty: TypeFull) -> Type {
        let hash = hash_full(&ty);
        eprintln!("Intering {ty:?} #{hash}");
        let mut map = self.map.borrow_mut();
        map.find(hash, |&existing| {
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
                TypeFull::Const(value) => (Tag::Const, self.consts.add(value)),
            };
            let ty = Type(self.tags.add(interned));
            let idx_idx = self.indices.add(idx);
            debug_assert_eq!(ty.0, idx_idx);
            eprintln!("  -> new: {ty:?} = {interned:?}");
            map.insert_unique(hash, ty, |&ty| {
                hash_full(&Self::lookup_type(
                    &self.tags,
                    &self.indices,
                    &self.instances,
                    &self.local_enums,
                    &self.consts,
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
            &self.consts,
            ty,
        )
    }

    fn lookup_type<'a>(
        tags: &'a SegmentList<Tag>,
        indices: &'a SegmentList<u32>,
        instances: &'a SegmentList<(BaseType, Box<[Type]>)>,
        local_enums: &'a SegmentList<Box<[(u32, Box<[Type]>)]>>,
        consts: &'a SegmentList<u64>,
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
            Tag::Const => TypeFull::Const(*consts.get(idx)),
        }
    }

    pub fn add_base(
        &mut self,
        module: ModuleId,
        id: ast::TypeId,
        name: Box<str>,
        generic_count: u8,
    ) -> BaseType {
        BaseType(self.bases.add(ResolvableTypeDef {
            generic_count,
            module,
            id,
            name,
            resolved: Resolvable::new(),
        }))
    }

    pub fn get_base(&self, ty: BaseType) -> &ResolvableTypeDef {
        self.bases.get(ty.0)
    }

    pub fn instantiate(&mut self, ty: Type, generics: &[Type]) -> Type {
        // PERF: temporary Vec for storage of allocated types
        match self.lookup(ty) {
            TypeFull::Instance(base, instance_generics) => {
                let instance_generics: Box<[Type]> = instance_generics.into();
                let instance_generics: Box<[_]> = instance_generics
                    .clone()
                    .iter()
                    .map(|&ty| self.instantiate(ty, generics))
                    .collect();
                self.intern(TypeFull::Instance(base, &instance_generics))
            }
            TypeFull::Generic(i) => generics[usize::from(i)],
            TypeFull::LocalEnum(items) => {
                let items: Box<[_]> = items.into();
                let items: Box<[_]> = items
                    .iter()
                    .map(|(i, params)| {
                        let params: Box<[_]> = params
                            .iter()
                            .map(|&ty| self.instantiate(ty, generics))
                            .collect();
                        (*i, params)
                    })
                    .collect();
                self.intern(TypeFull::LocalEnum(&items))
            }
            TypeFull::Const(_) => ty,
        }
    }

    pub fn display(&self, ty: Type) -> TypeDisplay {
        TypeDisplay { types: self, ty }
    }
}

pub struct TypeDisplay<'a> {
    types: &'a Types,
    ty: Type,
}
impl<'a> fmt::Display for TypeDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.types.lookup(self.ty) {
            TypeFull::Instance(base, generics) => match base {
                BaseType::Invalid => write!(f, "<invalid>"),
                BaseType::Tuple => {
                    write!(f, "(")?;
                    let mut first = true;
                    for &item in generics {
                        if !first {
                            write!(f, ", ")?;
                        }
                        first = false;
                        write!(f, "{}", self.types.display(item))?;
                    }
                    write!(f, ")")
                }
                BaseType::Array => write!(
                    f,
                    "[{}; {}]",
                    self.types.display(generics[0]),
                    self.types.display(generics[1])
                ),
                BaseType::Pointer => write!(f, "*{}", self.types.display(generics[0])),
                BaseType::Function => {
                    write!(f, "fn(")?;
                    let mut first = true;
                    for &arg in &generics[1..] {
                        if !first {
                            write!(f, ", ")?;
                        }
                        first = false;
                        write!(f, "{}", self.types.display(arg))?;
                    }
                    write!(f, ") -> {}", self.types.display(generics[0]))
                }
                _ => {
                    let name = &self.types.get_base(base).name;
                    write!(f, "{name}")?;
                    if !generics.is_empty() {
                        write!(f, "[")?;
                        let mut first = true;
                        for &generic in generics {
                            if !first {
                                write!(f, ", ")?;
                            }
                            first = false;
                            write!(
                                f,
                                "{}",
                                TypeDisplay {
                                    types: self.types,
                                    ty: generic
                                }
                            )?;
                        }
                        write!(f, "]")?;
                    }
                    Ok(())
                }
            },
            TypeFull::Generic(_) => panic!("unhandled generic during type display"),
            TypeFull::LocalEnum(variants) => {
                write!(f, "enum {{")?;
                for (i, params) in variants {
                    write!(f, "{i}")?;
                    if !params.is_empty() {
                        write!(f, "(")?;
                        let mut first = true;
                        for &param in params {
                            if first {
                                first = false;
                            } else {
                                write!(f, ", ")?;
                            }
                            write!(f, "{}", self.types.display(param))?;
                        }
                        write!(f, ")")?;
                    }
                }
                write!(f, "}}")
            }
            TypeFull::Const(n) => write!(f, "{n}"),
        }
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
    Const,
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
