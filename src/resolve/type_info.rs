use std::{ops::Index, borrow::Cow};

use crate::{
    resolve::types::{TupleCountMode, ResolvedTypeDef},
    error::{Errors, Error},
    span::Span,
    types::Primitive,
    ast::{TypeId, FunctionId},
    ir::{types::{IrTypes, IrType, TypeRefs, TypeRef},
    eval::{ConstIrType, ConstIrTypes}
}};

use super::types::{Type, SymbolTable, DefId, Enum};

#[derive(Clone, Debug)]
pub struct TypeTable {
    types: Vec<TypeInfoOrIndex>,
    enum_variants: Vec<(String, TypeRefs)>,
    generics: TypeRefs,
}
impl TypeTable {
    pub fn new(generic_count: u8) -> Self {

        let types = (0..generic_count).map(|i| TypeInfo::Generic(i).into()).collect();
        let generics = TypeRefs { idx: 0, count: generic_count as _ };
        let s = Self {
            types,
            enum_variants: Vec::new(),
            generics,
        };
        s.ty_dbg("Creating type table", ());
        s
    }

    pub fn generics(&self) -> TypeRefs { self.generics }

    pub fn find(&self, mut idx: TypeRef) -> (TypeRef, TypeInfo) {
        loop {
            match self.types[idx.idx()] {
                TypeInfoOrIndex::Type(ty) => return (idx, ty),
                TypeInfoOrIndex::Idx(new_idx) => idx = new_idx,
            }
        }
    }

    pub fn find_optimizing(&mut self, mut idx: TypeRef) -> (TypeRef, TypeInfo) {
        let initial = idx;
        let mut updated = false;
        let found = loop {
            match self.types[idx.idx()] {
                TypeInfoOrIndex::Type(ty) => break ty,
                TypeInfoOrIndex::Idx(new_idx) => {
                    idx = new_idx;
                    updated = true;
                }
            }
        };
        if updated {
            self.types[initial.idx()] = TypeInfoOrIndex::Idx(idx)
        }
        (idx, found)

    }

    pub fn get(&self, idx: TypeRef) -> TypeInfo {
        self.find(idx).1
    }

    pub fn update_type(&mut self, idx: TypeRef, ty: TypeInfo) {
        let idx = self.find(idx).0;
        self.types[idx.idx()] = TypeInfoOrIndex::Type(ty);
    }

    /// sets the type `ty` points to to `Invalid` and returns `true` if the type wasn't invalid before.
    pub fn invalidate(&mut self, ty: TypeRef) -> bool {
        let (idx, prev) = self.find(ty);
        self.types[idx.idx()] = TypeInfo::Invalid.into();
        !matches!(prev, TypeInfo::Invalid)
    }

    fn update_type_and_point(&mut self, idx: TypeRef, info: TypeInfo, b: TypeRef) {
        let idx = self.find(idx).0;

        self.types[idx.idx()] = TypeInfoOrIndex::Type(info);
        let b = self.find(b).0;
        if b.idx() != idx.idx() {
            self.types[b.idx()] = TypeInfoOrIndex::Idx(idx);
        }
    }

    pub fn add(&mut self, info: TypeInfo) -> TypeRef {
        let type_idx = TypeRef::new(self.types.len() as u32);
        self.types.push(TypeInfoOrIndex::Type(info));
        self.ty_dbg("Adding", &(info, type_idx));
        type_idx
    }

    pub fn add_info_or_idx(&mut self, ty: TypeInfoOrIndex) -> TypeRef {
        match ty {
            TypeInfoOrIndex::Type(info) => self.add(info),
            TypeInfoOrIndex::Idx(idx) => idx,
        }
    }

    pub fn add_multiple(&mut self, infos: impl IntoIterator<Item = TypeInfo>) -> TypeRefs {
        let infos = infos.into_iter();
        let idx = self.types.len() as u32;
        self.types.extend(infos.map(TypeInfoOrIndex::Type));
        let count = (self.types.len() - idx as usize) as u32;
        self.ty_dbg("Adding multiple", TypeRefs { idx, count })
    }
    pub fn add_multiple_info_or_index(
        &mut self,
        types: impl IntoIterator<Item = TypeInfoOrIndex>,
    ) -> TypeRefs {
        let idx = self.types.len() as u32;
        self.types.extend(types);
        let count = (self.types.len() - idx as usize) as u32;
        self.ty_dbg(
            "adding multiple (info_or_idx)",
            TypeRefs { idx, count },
        )
    }

    pub fn add_unknown(&mut self) -> TypeRef {
        self.add(TypeInfo::Unknown)
    }

    pub fn add_multiple_unknown(&mut self, n: u32) -> TypeRefs {
        self.add_multiple((0..n).map(|_| TypeInfo::Unknown))
    }

    pub fn specify(
        &mut self,
        idx: TypeRef,
        other: TypeInfo,
        errors: &mut Errors,
        span: Span,
        symbols: &SymbolTable,
    ) {
        let (curr_idx, prev) = self.find_optimizing(idx);

        self.ty_dbg("Specifying", (prev, idx, other));
        let ty = merge_infos(prev, other, self, symbols).unwrap_or_else(|| {
            errors.emit_span(
                Error::MismatchedType {
                    expected: prev.as_string(self, symbols).into_owned(),
                    found: other.as_string(self, symbols).into_owned(),
                },
                span,
            );
            TypeInfo::Invalid
        });

        self.types[curr_idx.idx()] = TypeInfoOrIndex::Type(ty);
    }
    pub fn specify_resolved_type(
        &mut self,
        idx: TypeRef,
        other: &Type,
        type_generics: TypeRefs,
        errors: &mut Errors,
        span: Span,
        symbols: &SymbolTable,
    ) {
        // PERF: this function converts Type to TypeInfo for now but making an explicit implementation for type
        // will save performance and won't add unnecessary entries to the type table.
        let other_info = match other.as_info(self, |i| type_generics.nth(i as u32).into()) {
            TypeInfoOrIndex::Type(ty) => ty,
            TypeInfoOrIndex::Idx(idx) => self.find(idx).1,
        };

        self.specify(idx, other_info, errors, span, symbols)
    }

    pub fn specify_or_merge(
        &mut self,
        idx: TypeRef,
        other: TypeInfoOrIndex,
        errors: &mut Errors,
        span: Span,
        symbols: &SymbolTable,
    ) {
        match other {
            TypeInfoOrIndex::Type(info) => self.specify(idx, info, errors, span, symbols),
            TypeInfoOrIndex::Idx(other_idx) => self.merge(idx, other_idx, errors, span, symbols),
        }
    }

    pub fn merge(
        &mut self,
        a: TypeRef,
        b: TypeRef,
        errors: &mut Errors,
        span: Span,
        ctx: &SymbolTable,
    ) {
        if let Err(err) = self.try_merge(a, b, ctx) {
            self.ty_dbg("\t... failed to merge", span);
            errors.emit_span(
                err,
                span,
            );
        }
    }

    fn try_merge(&mut self, a: TypeRef, b: TypeRef, ctx: &SymbolTable) -> Result<(), Error> {
        if a.idx() == b.idx() {
            return Ok(());
        }
        let (curr_a_idx, a_ty) = self.find_optimizing(a);
        let (curr_b_idx, b_ty) = self.find_optimizing(b);
        if curr_a_idx.idx() == curr_b_idx.idx() {
            return Ok(());
        }
        self.ty_dbg("Merging ...", ((a_ty, a), (b_ty, b)));

        // merge b's previous type into a
        let (res, new_ty) = match merge_infos(a_ty, b_ty, self, ctx) {
            Some(ty) => (Ok(()), self.ty_dbg("\t... merged", ty)),
            None => {
                let res = Err(Error::MismatchedType {
                    expected: a_ty.as_string(self, ctx).into_owned(),
                    found: b_ty.as_string(self, ctx).into_owned(),
                });
                (res, TypeInfo::Invalid)
            }
        };
        self.types[curr_a_idx.idx()] = TypeInfoOrIndex::Type(new_ty);

        // make b point to a
        debug_assert_ne!(b.idx(), curr_a_idx.idx());
        self.types[b.idx()] = TypeInfoOrIndex::Idx(curr_a_idx);
        debug_assert_ne!(curr_b_idx.idx(), curr_a_idx.idx());
        self.types[curr_b_idx.idx()] = TypeInfoOrIndex::Idx(curr_a_idx);

        // potentially shorten path of a
        if a.idx() != curr_a_idx.idx() {
            self.ty_dbg("shortening", (a, curr_a_idx));
            self.types[a.idx()] = TypeInfoOrIndex::Idx(curr_a_idx);
        }

        res
    }

    pub fn deref(&self, mut ty: TypeRef) -> TypeRef {
        loop {
            ty = match self.get(ty) {
                TypeInfo::Pointer(pointee) => pointee,
                _ => break ty
            }
        }
    }

    /// merges two type table indices while dereferencing pointers automatically to type check auto ref/deref.
    pub fn merge_dereffed(
        &mut self,
        a: TypeRef, b: TypeRef,
        errors: &mut Errors, span: Span, ctx: &SymbolTable
    ) {
        self.merge(self.deref(a), self.deref(b), errors, span, ctx)
    }

    // not for normal use, just to replace temporaries etc.
    pub fn replace_idx(&mut self, idx: TypeRef, entry: TypeInfoOrIndex) {
        self.types[idx.idx()] = entry;
    }

    pub fn reserve_enum_variants(&mut self, count: usize) -> EnumVariants {
        let idx = self.enum_variants.len() as u32;
        self.enum_variants.extend(std::iter::repeat((String::new(), TypeRefs::EMPTY)).take(count));
        EnumVariants { idx, count: count as _ }
    }
    pub fn replace_enum_variant(&mut self, idx: usize, name: String, args: TypeRefs) {
        self.enum_variants[idx] = (name, args);
    }

    pub fn add_enum_variants(&mut self, names: impl IntoIterator<Item = (String, TypeRefs)>) -> EnumVariants {
        let idx = self.enum_variants.len() as u32;
        self.enum_variants.extend(names);
        let count = self.enum_variants.len() as u32 - idx;
        EnumVariants { idx, count }
    }

    pub fn get_enum_variants(&self, variants: EnumVariants) -> &[(String, TypeRefs)] {
        &self.enum_variants[variants.idx as usize .. variants.idx as usize + variants.count as usize]
    }

    #[must_use = "Range should be used to update"]
    pub fn extend_enum_variants(
        &mut self,
        variants: EnumVariants,
        new_variants: impl IntoIterator<Item = (String, TypeRefs)>,
    ) -> EnumVariants {
        let prev_len = self.enum_variants.len();
        let insert_at = variants.idx as usize + variants.count as usize;
        self.enum_variants.splice(insert_at..insert_at, new_variants);
        EnumVariants {
            idx: variants.idx,
            count: variants.count + (self.enum_variants.len() - prev_len) as u32,
        }
    }

    pub fn finalize(&self) -> IrTypes {
        let mut ir_types = vec![IrType::Primitive(Primitive::Never); self.types.len()];
        for (i, ty) in self.types.iter().copied().enumerate() {
            let type_info = match ty {
                TypeInfoOrIndex::Type(ty) => ty,
                TypeInfoOrIndex::Idx(idx) => self.get(idx),
            };
            ir_types[i] = match type_info {
                TypeInfo::Unknown => IrType::Primitive(Primitive::Unit),
                TypeInfo::Int => IrType::Primitive(Primitive::I32),
                TypeInfo::Float => IrType::Primitive(Primitive::F32),
                TypeInfo::Primitive(p) => IrType::Primitive(p),
                TypeInfo::Resolved(id, generics) => IrType::Id(id, TypeRefs { idx: generics.idx, count: generics.count }),
                TypeInfo::Pointer(pointee) => IrType::Ptr(pointee),
                TypeInfo::Array(size, elem) => IrType::Array(elem, size.unwrap_or(0)),
                TypeInfo::Enum(variants) => {
                    let tag_ty = Enum::int_ty_from_variant_count(variants.count).map_or(
                        IrType::Primitive(Primitive::Unit),
                        |ty| IrType::Primitive(ty.into())
                    );
                    let variants_start = ir_types.len() as u32;
                    ir_types.extend((0..variants.count()).map(|_| IrType::Primitive(Primitive::Never)));

                    for (i, (_name, args)) in self.get_enum_variants(variants).iter().enumerate() {
                        ir_types[variants_start as usize + i] = IrType::Tuple(*args);
                    }
                    IrType::Enum(TypeRefs { idx: variants_start, count: variants.count() })
                }
                TypeInfo::Tuple(elems, _) => IrType::Tuple(TypeRefs { idx: elems.idx, count: elems.count }),

                // these types should never be encountered by runtime code (this probably isn't enforced properly)
                TypeInfo::SymbolItem(_)
                | TypeInfo::MethodItem { .. }
                | TypeInfo::LocalTypeItem(_) => IrType::Primitive(Primitive::Never),
                TypeInfo::Generic(i) => IrType::Ref(self.generics.nth(i as _)), // this gets replaced with the proper generic types
                TypeInfo::Invalid => panic!("Invalid types shouldn't reach type finalization"),
            };
        }

        IrTypes::new_with(ir_types, self.generics)
    }
    pub fn finalize_const(&self) -> ConstIrTypes {
        let mut ir_types = vec![ConstIrType::Ty(IrType::Primitive(Primitive::Never)); self.types.len()];
        for (i, ty) in self.types.iter().copied().enumerate() {
            let type_info = match ty {
                TypeInfoOrIndex::Type(ty) => ty,
                TypeInfoOrIndex::Idx(idx) => self.get(idx),
            };
            ir_types[i] = ConstIrType::Ty(match type_info {
                TypeInfo::Unknown => IrType::Primitive(Primitive::Unit),
                TypeInfo::Int => {
                    ir_types[i] = ConstIrType::Int;
                    continue;
                }
                TypeInfo::Float => {
                    ir_types[i] = ConstIrType::Float;
                    continue;
                }
                TypeInfo::Primitive(p) => IrType::Primitive(p),
                TypeInfo::Resolved(id, generics) => IrType::Id(id, TypeRefs { idx: generics.idx, count: generics.count }),
                TypeInfo::Pointer(pointee) => IrType::Ptr(pointee),
                TypeInfo::Array(size, elem) => IrType::Array(elem, size.unwrap_or(0)),
                TypeInfo::Enum(_) => {
                    ir_types[i] = ConstIrType::EnumVariant;
                    continue;
                }
                TypeInfo::Tuple(elems, _) => IrType::Tuple(TypeRefs { idx: elems.idx, count: elems.count }),
                TypeInfo::SymbolItem(_)
                | TypeInfo::MethodItem { .. } => todo!(),
                | TypeInfo::LocalTypeItem(_) => panic!("comptime type supplied when building ir"),
                TypeInfo::Generic(i) => IrType::Ref(self.generics.nth(i as u32)),
                TypeInfo::Invalid => panic!("Invalid types shouldn't reach type finalization"),
            });
        }

        ConstIrTypes::new(ir_types)
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
                i: usize,
            ) -> petgraph::prelude::NodeIndex {
                if let Some(node) = nodes[i] {
                    node
                } else {
                    let node = match ty {
                        TypeInfoOrIndex::Type(ty) => graph.add_node(format!("{i}: {ty:?}")),
                        TypeInfoOrIndex::Idx(_) => graph.add_node(i.to_string()),
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
                            TypeInfo::Pointer(elem) | TypeInfo::Array(_, elem) => {
                                Some(TypeRefs {
                                    idx: elem.0,
                                    count: 1,
                                })
                            }

                            _ => None,
                        };
                        if let Some(elems) = elems {
                            for (i, elem) in elems.iter().enumerate() {
                                let elem = get_node(
                                    &mut graph,
                                    &mut nodes,
                                    self.types[elem.idx()],
                                    elem.idx(),
                                );
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
impl Index<TypeRef> for TypeTable {
    type Output = TypeInfo;

    fn index(&self, mut index: TypeRef) -> &Self::Output {
        loop {
            match &self.types[index.idx()] {
                TypeInfoOrIndex::Type(ty) => return ty,
                TypeInfoOrIndex::Idx(new_idx) => {
                    debug_assert_ne!(new_idx.idx(), index.idx());
                    index = *new_idx;
                }
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
pub struct EnumVariants {
    idx: u32,
    count: u32,
}
impl EnumVariants {
    pub fn count(self) -> u32 {
        self.count
    }
}

/// A type that may not be (completely) known yet.
#[derive(Clone, Copy, Debug)]
pub enum TypeInfo {
    Unknown,
    Int,
    Float,
    Primitive(Primitive),
    Resolved(TypeId, TypeRefs),
    Pointer(TypeRef),
    Array(Option<u32>, TypeRef),
    Enum(EnumVariants),
    Tuple(TypeRefs, TupleCountMode),
    SymbolItem(DefId),
    MethodItem {
        function: FunctionId,
        this_ty: TypeRef,
    },
    LocalTypeItem(TypeRef),
    Generic(u8),
    Invalid,
}
impl TypeInfo {
    pub const UNIT: Self = Self::Primitive(Primitive::Unit);

    pub fn as_string(&self, types: &TypeTable, symbols: &SymbolTable) -> Cow<'static, str> {
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
                        generics_string += &*generic.as_string(types, symbols);
                        if i != generics.len() - 1 {
                            generics_string += ", ";
                        }
                    }
                    generics_string.push('>');
                }
                format!("{}{}", symbols.get_type(id).name(), generics_string).into()
            }
            TypeInfo::Pointer(inner) => format!("*{}", types[inner].as_string(types, symbols)).into(),
            TypeInfo::Array(count, inner) => format!(
                "[{}; {}]",
                types[inner].as_string(types, symbols),
                count.map_or("_".to_owned(), |c| c.to_string())
            )
            .into(),
            TypeInfo::Enum(variants) => {
                let mut s = "[".to_owned();
                for (i, (name, variant_types)) in types.get_enum_variants(variants).iter().enumerate() {
                    s += name;
                    if variant_types.len() > 0 {
                        s += "(";
                        let mut first = true;
                        for ty in variant_types.iter() {
                            if first {
                                first = false;
                            } else {
                                s += ",";
                            }
                            s += types[ty].as_string(types, symbols).as_ref();
                        }
                        s += ")";
                    }
                    if i != variants.count() as usize - 1 {
                        s += ",";
                    }
                }
                s.push(']');
                s.into()
            }
            TypeInfo::Tuple(elems, mode) => {
                let mut s = "(".to_owned();
                let mut first = true;
                for elem in elems.iter() {
                    if first {
                        first = false;
                    } else {
                        s.push_str(", ");
                    }
                    s.push_str(&types.get(elem).as_string(types, symbols));
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
            TypeInfo::SymbolItem(id) => format!("<symbol item: {id:?}?>").into(),
            TypeInfo::MethodItem { function, this_ty } => format!(
                "<method {} with {}>",
                symbols.get_func(function).name,
                types[this_ty].as_string(types, symbols)
            ).into(),
            TypeInfo::Generic(i) => format!("<generic #{i}>").into(),
            TypeInfo::LocalTypeItem(idx) => format!("<type {}>", types.get(idx).as_string(types, symbols)).into(),
            TypeInfo::Invalid => "<invalid>".into(),
        }
    }
}

/// merge the types and return the merged type
fn merge_infos(
    ty: TypeInfo,
    other: TypeInfo,
    types: &mut TypeTable,
    symbols: &SymbolTable,
) -> Option<TypeInfo> {
    match other {
        Unknown | Primitive(crate::types::Primitive::Never) => return Some(ty),
        Invalid => return Some(Invalid),
        Int => match ty {
            Int => return Some(Int),
            Primitive(p) if p.as_int().is_some() => return Some(ty),
            _ => {}
        },
        Float => match ty {
            Float => return Some(Float),
            Primitive(p) if p.as_float().is_some() => return Some(ty),
            _ => {}
        },
        _ => {}
    }
    use TypeInfo::*;
    match ty {
        Unknown => Some(other),
        Primitive(crate::types::Primitive::Never) => Some(other),
        Int => match other {
            Int => Some(Int),
            Primitive(p) if p.as_int().is_some() => Some(other),
            _ => None,
        },
        Float => match other {
            Float => Some(Float),
            Primitive(p) if p.as_float().is_some() => Some(other),
            _ => None,
        },
        Primitive(prim) => if let Primitive(other) = other {
            prim == other
        } else {
            false
        }.then_some(ty),
        Resolved(id, generics) => if let Resolved(other, other_generics) = other {
            id == other && {
                debug_assert_eq!(generics.count, other_generics.count);
                generics
                    .iter()
                    .zip(other_generics.iter())
                    .all(|(a, b)|types.try_merge(a, b, symbols).is_ok())
            }
        } else if let ResolvedTypeDef::Enum(def) = symbols.get_type(id) {
            if let Enum(variants) = other {
                merge_implicit_and_explicit_enum(def, generics, variants, types, symbols)
            } else {
                false
            }
        } else {
            false
        }
        .then_some(ty),
        Pointer(inner) => {
            let Pointer(other_inner) = other else { return None };
            let new_inner = merge_infos(
                types.get(inner),
                types.get(other_inner),
                types,
                symbols,
            )?;
            types.update_type_and_point(inner, new_inner, other_inner);
            Some(Pointer(inner))
        }
        Array(size, inner) => {
            let Array(other_size, other_inner) = other else { return None };

            let new_inner = merge_infos(
                types.get(inner),
                types.get(other_inner),
                types,
                symbols,
            )?;
            types.update_type_and_point(inner, new_inner, other_inner);

            let new_size = match (size, other_size) {
                (Some(a), Some(b)) if a == b => Some(a),
                (Some(size), None) | (None, Some(size)) => Some(size),
                (None, None) => None,
                _ => return None,
            };
            Some(Array(new_size, inner))
        }
        Enum(variants) => {
            match other {
                Enum(other_variants) => {
                    merge_implicit_enums(variants, other_variants, types, symbols)
                }
                Resolved(id, generics) => {
                    let ResolvedTypeDef::Enum(def) = symbols.get_type(id) else { return None };
                    merge_implicit_and_explicit_enum(def, generics, variants, types, symbols).then_some(other)
                }
                _ => None
            }
        }
        Tuple(a_elems, a_count_mode) => {
            use TupleCountMode::{AtLeast, Exact};

            let Tuple(b_elems, b_count_mode) = other else { return None };
            let (res_ty, other_ty, mode) = match (a_count_mode, b_count_mode) {
                (Exact, Exact) => {
                    if a_elems.len() == b_elems.len() {
                        (a_elems, b_elems, Exact)
                    } else {
                        return None;
                    }
                }
                (Exact, AtLeast) => {
                    if a_elems.len() >= b_elems.len() {
                        (a_elems, b_elems, Exact)
                    } else {
                        return None;
                    }
                }
                (AtLeast, Exact) => {
                    if a_elems.len() <= b_elems.len() {
                        (b_elems, a_elems, Exact)
                    } else {
                        return None;
                    }
                }
                (AtLeast, AtLeast) => {
                    if a_elems.len() >= b_elems.len() {
                        (a_elems, b_elems, AtLeast)
                    } else {
                        (b_elems, a_elems, AtLeast)
                    }
                }
            };

            for (a, b) in res_ty.iter().zip(other_ty.iter()) {
                let (a_idx, a_ty) = types.find(a);
                let (b_idx, b_ty) = types.find(b);

                let merged = merge_infos(a_ty, b_ty, types, symbols)?;
                types.replace_idx(a_idx, TypeInfoOrIndex::Type(merged));
                types.replace_idx(b_idx, TypeInfoOrIndex::Idx(a_idx));
            }
            Some(Tuple(res_ty, mode))
        }
        SymbolItem(id) => {
            if let SymbolItem(id2) = other {
                (id == id2).then_some(ty)
            } else {
                None
            }
        }
        
        Generic(i) => {
            // TODO: proper generic type checking
            match other {
                Generic(i2) if i == i2 => Some(ty),
                _ => None
            }
        }
        Invalid => Some(Invalid), // invalid type 'spreading'
        MethodItem { .. } => todo!("merge {ty:?} with {other:?}"), // might be unreachable?
        LocalTypeItem(t1) => {
            let LocalTypeItem(t2) = other else { return None };
            match merge_infos(types.get(t1), types.get(t2), types, symbols) {
                Some(ty) => {
                    Some(LocalTypeItem(types.add(ty)))
                }
                None => None
            }
        }
    }
}

fn merge_implicit_and_explicit_enum(def: &Enum, generics: TypeRefs, variants: EnumVariants,
    types: &mut TypeTable, symbols: &SymbolTable)
-> bool {
    for i in variants.idx .. variants.idx + variants.count {
        let (name, arg_types) = &types.enum_variants[i as usize];
        let Some((_, _, def_arg_types)) = def.variants.get(name) else { return false };
        
        if def_arg_types.len() != arg_types.len() { return false }

        for (a, b) in arg_types.iter().zip(def_arg_types) {
            let (a_idx, a_ty) = types.find(a);
            let (b_ty, b_idx) = dbg!(match b.as_info(types, |i| generics.nth(i as u32).into()) {
                TypeInfoOrIndex::Type(ty) => (ty, None),
                TypeInfoOrIndex::Idx(idx) => (types.find(idx).1, Some(idx)),
            });

            match merge_infos(a_ty, b_ty, types, symbols) {
                Some(new_ty) => {
                    types.replace_idx(a_idx, new_ty.into());
                    if let Some(b_idx) = b_idx {
                        if b_idx.idx() != a_idx.idx() {
                            types.replace_idx(b_idx, a_idx.into());
                        }
                    }
                }
                None => return false
            }
        }
    }
    true
}

fn merge_implicit_enums(a: EnumVariants, b: EnumVariants, types: &mut TypeTable, symbols: &SymbolTable) -> Option<TypeInfo> {
    let (larger, smaller) = if a.count > b.count { (a, b) } else { (b, a) };
    
    let mut new_variants = Vec::with_capacity((larger.count - smaller.count) as usize);

    for smaller_idx in 0..smaller.count {
        let (name, arg_types) = &types.get_enum_variants(smaller)[smaller_idx as usize];
        let arg_types = *arg_types;

        match types.get_enum_variants(larger).iter().find(|(other_name, _)| other_name == name) {
            Some((_, other_arg_types)) => {
                // variant is already in larger, unify the argument types
                if arg_types.len() != other_arg_types.len() {
                    return None;
                }
                for (a, b) in arg_types.iter().zip(other_arg_types.iter()) {
                    if let Err(_) = types.try_merge(a, b, symbols) {
                        return None; // argument merge fails -> fail merge
                    }
                }
            }
            None => new_variants.push((name.clone(), arg_types)) // add new variant to larger
        }
    }
    
    Some(TypeInfo::Enum(types.extend_enum_variants(larger, new_variants)))
}

#[derive(Clone, Copy, Debug)]
pub enum TypeInfoOrIndex {
    Type(TypeInfo),
    Idx(TypeRef),
}
impl From<TypeInfo> for TypeInfoOrIndex {
    fn from(info: TypeInfo) -> Self {
        Self::Type(info)
    }
}
impl From<TypeRef> for TypeInfoOrIndex {
    fn from(value: TypeRef) -> Self {
        Self::Idx(value)
    }
}
