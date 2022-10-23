use std::{ops::Index, borrow::Cow};

use crate::{error::*, ast::ModuleId, span::{TSpan, Span}, types::Primitive, ir::TypeDef};

use super::{TypeInfoOrIndex, SymbolKey, TypingCtx, Type};


#[derive(Clone, Debug)]
pub struct TypeTable {
    types: Vec<TypeInfoOrIndex>,
    names: Vec<String>,
}
impl TypeTable {
    pub fn new() -> Self {
        let s =Self {
            types: Vec::new(),
            names: Vec::new(),
        };
        s.ty_dbg("Creating type table", ());
        s
    }

    pub fn get_type(&self, idx: TypeTableIndex) -> TypeInfo {
        let mut current = self.types[idx.idx()];
        loop {
            match current {
                TypeInfoOrIndex::Type(ty) => return ty,
                TypeInfoOrIndex::Idx(idx) => current = self.types[idx.idx()],
            }
        }
    }
    
    pub fn update_type(&mut self, idx: TypeTableIndex, info: TypeInfo) {
        let mut curr_idx = idx;
        while let TypeInfoOrIndex::Idx(idx) = self.types[curr_idx.idx()] {
            curr_idx = idx;
        }
        self.types[curr_idx.idx()] = TypeInfoOrIndex::Type(info);
    }

    // Points a to the index that b is pointing to
    pub fn point_to(&mut self, mut a: TypeTableIndex, b: TypeTableIndex) {
        if a.idx() == b.idx() { return; }
        while let TypeInfoOrIndex::Idx(new_idx) = self.types[a.idx()] {
            a = new_idx;
        }
        self.types[a.idx()] = TypeInfoOrIndex::Idx(b);
    }

    pub fn add(&mut self, info: TypeInfo) -> TypeTableIndex {
        let type_idx = TypeTableIndex(self.types.len() as u32);
        self.types.push(TypeInfoOrIndex::Type(info));
        self.ty_dbg("Adding", &(info, type_idx));
        type_idx
    }

    pub fn add_info_or_idx(&mut self, ty: TypeInfoOrIndex) -> TypeTableIndex {
        match ty {
            TypeInfoOrIndex::Type(info) => self.add(info),
            TypeInfoOrIndex::Idx(idx) => idx
        }
    }

    pub fn add_multiple(&mut self, infos: impl IntoIterator<Item = TypeInfo>) -> TypeTableIndices {
        let infos = infos.into_iter();
        let idx = self.types.len() as u32;
        self.types.extend(infos.map(TypeInfoOrIndex::Type));
        let count = (self.types.len() - idx as usize) as u32;
        self.ty_dbg("Adding multiple", TypeTableIndices { idx, count })
    }
    pub fn add_multiple_info_or_index(&mut self, types: impl IntoIterator<Item = TypeInfoOrIndex>)
    -> TypeTableIndices {
        let idx = self.types.len() as u32;
        let types = types.into_iter().map(|ty| {
            if let TypeInfoOrIndex::Idx(the_idx) = ty {
                debug_assert!(the_idx.idx() < idx as _);
            }
            ty
        });
        self.types.extend(types);
        let count = (self.types.len() - idx as usize) as u32;
        self.ty_dbg("adding multiple (info_or_idx)", TypeTableIndices { idx, count })
    }

    pub fn add_unknown(&mut self) -> TypeTableIndex {
        self.add(TypeInfo::Unknown)
    }

    pub fn add_multiple_unknown(&mut self, n: u32) -> TypeTableIndices {
        self.add_multiple((0..n).map(|_| TypeInfo::Unknown))
    }

    pub fn specify(&mut self, idx: TypeTableIndex, other: TypeInfo, errors: &mut Errors, span: Span, ctx: &TypingCtx) {
        let mut curr_idx = idx;
        let prev = loop {
            match self.types[curr_idx.idx()] {
                TypeInfoOrIndex::Type(ty) => break ty,
                TypeInfoOrIndex::Idx(idx) => curr_idx = idx,
            }
        };
        self.ty_dbg("Specifying", (prev, idx, other));
        let ty = merge_twosided(prev, other, self, ctx).unwrap_or_else(|| {
            errors.emit_span(Error::MismatchedType {
                expected: prev.as_string(self, ctx).into_owned(),
                found: other.as_string(self, ctx).into_owned()
            }, span);
            TypeInfo::Invalid
        });

        self.types[curr_idx.idx()] = TypeInfoOrIndex::Type(ty);
    }
    pub fn specify_or_merge(
        &mut self,
        idx: TypeTableIndex,
        other: TypeInfoOrIndex,
        errors: &mut Errors,
        module: ModuleId,
        span: TSpan,
        ctx: &TypingCtx,
    ) {
        match other {
            TypeInfoOrIndex::Type(info) => self.specify(idx, info, errors, span.in_mod(module), ctx),
            TypeInfoOrIndex::Idx(other_idx) => self.merge(idx, other_idx, errors, span.in_mod(module), ctx),
        }
    }

    pub fn merge(&mut self, a: TypeTableIndex, b: TypeTableIndex,
        errors: &mut Errors, span: Span, ctx: &TypingCtx
    ) {
        if a.idx() == b.idx() { return; }
        let mut curr_a_idx = a;
        let a_ty = loop {
            match self.types[curr_a_idx.idx()] {
                TypeInfoOrIndex::Type(ty) => break ty,
                TypeInfoOrIndex::Idx(new_idx) => curr_a_idx = new_idx,
            }
        };
        let b_ty = self.get_type(b);
        self.ty_dbg("Merging ...", ((a_ty, a), (b_ty, b)));


        // merge b's previous type into a
        let new_ty = match merge_twosided(a_ty, b_ty, self, ctx) {
            Some(ty) => self.ty_dbg("\t... merged", (ty, &self)).0,
            None => {
                self.ty_dbg("\t... failed to merge", span);
                errors.emit_span(Error::MismatchedType {
                    expected: a_ty.as_string(self, ctx).into_owned(),
                    found: b_ty.as_string(self, ctx).into_owned()
                }, span);
                TypeInfo::Invalid
            }
        };
        self.types[curr_a_idx.idx()] = TypeInfoOrIndex::Type(new_ty);

        // make b point to a
        debug_assert_ne!(b.idx(), curr_a_idx.idx());
        self.types[b.idx()] = TypeInfoOrIndex::Idx(curr_a_idx);

        // potentially shorten path of a
        if a.idx() != curr_a_idx.idx() {
            self.ty_dbg("shortening", (a, curr_a_idx));
            self.types[a.idx()] = TypeInfoOrIndex::Idx(curr_a_idx);
        }
    }

    pub fn add_names(&mut self, names: impl IntoIterator<Item = String>) -> TypeTableNames {
        let idx = self.names.len();
        self.names.extend(names);
        TypeTableNames { idx: idx as u32, count: (self.names.len() - idx) as u32 }
    }
    pub fn _remove_names(&mut self, names: TypeTableNames) {
        self.names.drain(names.idx as usize .. names.idx as usize + names.count as usize);
    }

    pub fn get_names(&self, names: TypeTableNames) -> &[String] {
        &self.names[names.idx as usize .. names.idx as usize + names.count as usize]
    }
    #[must_use = "Range should be used to update"]
    pub fn extend_names(&mut self, idx: TypeTableNames, names: impl IntoIterator<Item = String>) -> TypeTableNames {
        let prev_len = self.names.len();
        let insert_at = idx.idx as usize + idx.count as usize;
        self.names.splice(insert_at..insert_at, names);
        TypeTableNames { idx: idx.idx, count: idx.count + (self.names.len() - prev_len) as u32 }
    }

    pub fn finalize(self) -> FinalTypeTable {
        let types = self.types.iter()
            .map(|ty| match *ty {
                TypeInfoOrIndex::Type(ty) => ty,
                TypeInfoOrIndex::Idx(idx) => self.get_type(idx),
            }.finalize(&self))
            .collect();
        FinalTypeTable { types }
    }

    /// Type inference debugging
    fn ty_dbg<D: std::fmt::Debug>(&self, msg: &str, d: D) -> D {
        if crate::DEBUG_INFER.load(std::sync::atomic::Ordering::Relaxed) {
            println!("[TypeInfer] {msg}: {d:?}");
        }
        #[cfg(feature = "infer-graph")]
        {
            let mut graph = petgraph::graph::Graph::new();
            let mut nodes = vec![None; self.types.len()];

            fn get_node(
                graph: &mut petgraph::graph::Graph<String, String, petgraph::Directed, u32>,
                nodes: &mut [Option<petgraph::prelude::NodeIndex>],
                ty: TypeInfoOrIndex,
                i: usize
            ) -> petgraph::prelude::NodeIndex {
                if let Some(node) = nodes[i] {
                    node
                } else {
                    let node = match ty {
                        TypeInfoOrIndex::Type(ty) => {
                            graph.add_node(format!("{i}: {ty:?}"))
                        }
                        TypeInfoOrIndex::Idx(_) => {
                            graph.add_node(i.to_string())
                        }
                    };
                    nodes[i] = Some(node);

                    node
                }
            }

            for (i, ty) in self.types.iter().enumerate() {
                let node = get_node(&mut graph, &mut nodes, *ty, i);

                // add edges to parents
                match ty {
                    TypeInfoOrIndex::Type(ty) => {
                        let elems = match *ty {
                            TypeInfo::Tuple(elems, _) => Some(elems),
                            TypeInfo::Pointer(elem)
                            | TypeInfo::Array(_, elem)
                                => Some(TypeTableIndices { idx: elem.0, count: 1 }),
                            
                            _ => None
                        };
                        if let Some(elems) = elems {
                            for (i, elem) in elems.iter().enumerate() {
                                let elem = get_node(&mut graph, &mut nodes, self.types[elem.idx()], elem.idx());
                                graph.add_edge(node, elem, format!("elem {i}"));
                            }
                        }
                    }
                    TypeInfoOrIndex::Idx(idx) => {
                        let to = get_node(&mut graph, &mut nodes, self.types[idx.idx()], idx.idx());
                        graph.add_edge(node, to, "Idx".to_string());
                    }
                }
            }

            eprintln!("GRAPH: {}", petgraph::dot::Dot::new(&graph));
        }
        d
    }
}
impl Index<TypeTableIndex> for TypeTable {
    type Output = TypeInfo;

    fn index(&self, mut index: TypeTableIndex) -> &Self::Output {
        loop {
            match &self.types[index.idx()] {
                TypeInfoOrIndex::Type(ty) => return ty,
                TypeInfoOrIndex::Idx(new_idx) => index = *new_idx,
            }
        }
    }
}
impl Drop for TypeTable {
    fn drop(&mut self) {
        self.ty_dbg("Dropping Type Table: ", &*self);
    }
}

#[derive(Clone, Copy, Debug)]
pub struct TypeTableIndex(pub u32);
impl TypeTableIndex {
    pub const NONE: Self = Self(u32::MAX);
    pub fn idx(self) -> usize { self.0 as usize }
    pub fn is_present(self) -> bool { self.0 != u32::MAX }
}

#[derive(Clone, Copy, Debug)]
pub struct TypeTableIndices {
    idx: u32,
    count: u32
}
impl TypeTableIndices {
    pub const EMPTY: Self = Self { idx: 0, count: 0 };

    pub fn iter(self) -> impl Iterator<Item = TypeTableIndex> {
        (self.idx .. self.idx + self.count).map(TypeTableIndex)
    }
    pub fn nth(self, index: usize) -> TypeTableIndex {
        assert!(index < self.count as usize);
        TypeTableIndex(self.idx + index as u32)
    }
    pub fn len(self) -> usize { self.count as usize }
}

#[derive(Clone, Copy, Debug)]
pub struct TypeTableNames {
    idx: u32,
    count: u32
}

#[derive(Debug)]
pub struct FinalTypeTable {
    types: Vec<Type>
}
impl FinalTypeTable {
    pub fn get(&self, idx: TypeTableIndex) -> &Type {
        assert!(idx.0 != u32::MAX, "Tried to get none-type table index");
        // for generic types this will get a bit more complicated but the base
        // principle of indexing into the Vec should stay
        &self.types[idx.idx()]
    }
}
impl Index<TypeTableIndex> for FinalTypeTable {
    type Output = Type;

    fn index(&self, index: TypeTableIndex) -> &Self::Output {
        &self.types[index.idx()]
    }
}
impl Index<TypeTableIndices> for FinalTypeTable {
    type Output = [Type];

    fn index(&self, index: TypeTableIndices) -> &Self::Output {
        &self.types[index.idx as usize .. index.idx as usize + index.count as usize]
    }
}

/// A type that may not be (completely) known yet.
#[derive(Clone, Copy, Debug)]
pub enum TypeInfo {
    Unknown,
    Int,
    Float,
    Primitive(Primitive),
    Resolved(SymbolKey, TypeTableIndices),
    Pointer(TypeTableIndex),
    Array(Option<u32>, TypeTableIndex),
    Enum(TypeTableNames),
    Tuple(TypeTableIndices, TupleCountMode),
    Symbol, // compile time Symbol like a function, type or trait
    Generic(u8), // a type that is not instanciated to a specific type yet.
    Invalid,
}
impl TypeInfo {
    pub const UNIT: Self = Self::Primitive(Primitive::Unit);
    
    fn as_string(&self, types: &TypeTable, ctx: &TypingCtx) -> Cow<'static, str> {
        match *self {
            TypeInfo::Unknown => "<unknown>".into(),
            TypeInfo::Int => "<integer>".into(),
            TypeInfo::Float => "<float>".into(),
            TypeInfo::Primitive(p) => Into::<&'static str>::into(p).into(),
            TypeInfo::Resolved(id, generics) => {
                let mut generics_string = String::new();
                if generics.count > 0 {
                    generics_string.push('<');
                    for (i, generic) in generics.iter().enumerate() {
                        let generic = types[generic];
                        generics_string += &*generic.as_string(types, ctx);
                        if i != generics.len() - 1 {
                            generics_string += ", ";
                        }
                    }
                    generics_string.push('>');
                }
                format!("{}{}", ctx.get_type(id).name(), generics_string).into()
            }
            TypeInfo::Pointer(inner) => format!("*{}", types[inner].as_string(types, ctx)).into(),
            TypeInfo::Array(count, inner) => format!("[{}; {}]",
                types[inner].as_string(types, ctx),
                count.map_or("_".to_owned(), |c| c.to_string())
            ).into(),
            TypeInfo::Enum(variants) => {
                let mut s = "[".to_owned();
                for (i, t) in types.get_names(variants).iter().enumerate() {
                    s += t;
                    if i != variants.count as usize - 1 {
                        s += ", ";
                    }
                }
                s.push(']');
                s.into()
            }
            TypeInfo::Tuple(elems, mode)  => {
                let mut s = "(".to_owned();
                let mut first = true;
                for elem in elems.iter() {
                    if first {
                        first = false;
                    } else {
                        s.push_str(", ");
                    }
                    s.push_str(&types.get_type(elem).as_string(types, ctx));

                }
                match mode {
                    TupleCountMode::Exact => {}
                    TupleCountMode::AtLeast => {
                        if !first {
                            s.push_str(", ");
                        }
                        s.push_str("..");
                    }
                }
                s.push(')');
                s.into()
            }
            TypeInfo::Symbol =>  "symbol".into(),
            TypeInfo::Generic(_) => todo!(),
            TypeInfo::Invalid => "<invalid>".into(),
        }
    }
    pub fn is_invalid(&self) -> bool {
        matches!(self, TypeInfo::Invalid)
    }
    fn finalize(self, types: &TypeTable) -> Type {
        match self {
            Self::Unknown | Self::Invalid => Type::Prim(Primitive::Unit),
            Self::Int => Type::Prim(Primitive::I32),
            Self::Float => Type::Prim(Primitive::F32),
            Self::Primitive(p) => Type::Prim(p),
            Self::Resolved(id, generics) => {
                let generic_types = generics.iter()
                    .map(|ty| types.get_type(ty).finalize(types))
                    .collect();
                Type::Id(id, generic_types)
            }
            Self::Pointer(inner) => Type::Pointer(Box::new(types.get_type(inner).finalize(types))),
            Self::Array(size, inner) => {
                let inner = types.get_type(inner).finalize(types);
                size.map_or(
                    Type::Prim(Primitive::Unit),
                    |size| Type::Array(Box::new((inner, size)))
                )
            }
            Self::Enum(idx) => {
                Type::Enum(types.get_names(idx).to_vec())
            }
            Self::Tuple(inners, _) => {
                Type::Tuple(inners
                    .iter()
                    .map(|ty| types.get_type(ty).finalize(types))
                    .collect()
                )
            }
            Self::Symbol => {
                Type::Symbol
            }
            Self::Generic(i) => Type::Generic(i),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TupleCountMode { Exact, AtLeast }

fn merge_twosided(ty: TypeInfo, other: TypeInfo, types: &mut TypeTable, ctx: &TypingCtx) -> Option<TypeInfo> {
    match merge_onesided(ty, other, types, ctx) {
        Some(t) => Some(t),
        None => merge_onesided(other, ty, types, ctx)
    }
}

/// merge the types and return the merged type
fn merge_onesided(ty: TypeInfo, other: TypeInfo, types: &mut TypeTable, ctx: &TypingCtx) -> Option<TypeInfo> {
    use TypeInfo::*;
    match ty {
        Unknown => Some(other),
        Primitive(crate::types::Primitive::Never) => Some(other),
        Int => {
            match other {
                Int => Some(other),
                Primitive(p) if p.as_int().is_some() => Some(other),
                Unknown => Some(Int),
                _ => None
            }
        }
        Float => {
            match other {
                Float => Some(other),
                Primitive(p) if p.as_float().is_some() => Some(other),
                Unknown => Some(Float),
                _ => None
            }
        }
        Primitive(prim) => {
            if let Primitive(other) = other {
                prim == other
            } else { false }
                .then_some(ty)
        }
        Resolved(id, generics) => {
            if let Resolved(other, other_generics) = other {
                id == other && {
                    debug_assert_eq!(generics.count, other_generics.count);
                    generics.iter()
                        .zip(other_generics.iter())
                        .map(|(a, b)| {
                            let new = merge_onesided(types[a], types[b], types, ctx)?;
                            types.update_type(a, new);
                            types.point_to(b, a);
                            Some(())
                        })
                        .all(|v| v.is_some())
                }
            } else if let TypeDef::Enum(def) = ctx.get_type(id) {
                if let Enum(names) = other {
                    !types.get_names(names).iter()
                        .any(|name| !def.variants.contains_key(name))
                } else { false }
            } else { false }
                .then_some(ty)
        }
        Pointer(inner) => {
            let Pointer(other_inner) = other else { return None };
            let new_inner = merge_onesided(types.get_type(inner), types.get_type(other_inner), types, ctx)?;
            types.update_type(inner, new_inner);
            types.point_to(other_inner, inner);
            Some(Pointer(inner))
        }
        Array(size, inner) => {
            let Array(other_size, other_inner) = other else { return None };
    
            let new_inner = merge_onesided(types.get_type(inner), types.get_type(other_inner), types, ctx)?;
            types.update_type(inner, new_inner);
            types.point_to(other_inner, inner);
            
            let new_size = match (size, other_size) {
                (Some(a), Some(b)) if a == b => Some(a),
                (Some(size), None) | (None, Some(size)) => Some(size),
                (None, None) => None,
                _ => return None
            };
            Some(Array(new_size, inner))
                
        }
        Enum(names) => {
            let Enum(other_names) = other else { return None };
            let a = types.get_names(names);
            let b = types.get_names(other_names);
            let new_variants: Vec<_> = b.iter().filter(|s| !a.contains(s)).cloned().collect();
            types.ty_dbg("New variants after merging", (&new_variants, a, b));
            let merged_variants = types.extend_names(names, new_variants);
            Some(Enum(merged_variants))
        }
        Tuple(a_elems, a_count_mode) => {
            use TupleCountMode::{Exact, AtLeast};

            let Tuple(b_elems, b_count_mode) = other else { return None };
            let (res_ty, other_ty, mode) = match (a_count_mode, b_count_mode) {
                (Exact, Exact) =>
                    if a_elems.len() == b_elems.len() { (a_elems, b_elems, Exact) } else { return None },
                (Exact, AtLeast) =>
                    if a_elems.len() >= b_elems.len() { (a_elems, b_elems, Exact) } else { return None },
                (AtLeast, Exact) =>
                    if a_elems.len() <= b_elems.len() { (b_elems, a_elems, Exact) } else { return None }
                (AtLeast, AtLeast) => if a_elems.len() >= b_elems.len() {
                    (a_elems, b_elems, AtLeast)
                 } else {
                    (b_elems, a_elems, AtLeast)
                },
            };

            for (a, b) in res_ty.iter().zip(other_ty.iter()) {
                let new = merge_twosided(types.get_type(a), types.get_type(b), types, ctx)?;
                types.update_type(a, new);
                types.point_to(b, a);
            }
            Some(Tuple(res_ty, mode))
        
        }
        Symbol => if let Symbol = other {
            Some(ty)
        } else {
            None
        }
        Generic(i) => if let Generic(j) = other {
            if i == j {
                Some(ty)
            } else {
                None
            }
        } else {
            None
        }
        Invalid => Some(Invalid), // invalid type 'spreading'
    }
}
