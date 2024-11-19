use std::{ops::Index, rc::Rc};

use id::{ModuleId, TypeId};
use span::{Span, TSpan};
use types::{Primitive, Type};

mod unify;

use unify::unify;

use crate::{
    check::{expr::int_ty_from_variant_count, traits},
    compiler::{Def, Generics, ResolvedTypeDef},
    error::Error,
    parser::ast::{self, TraitId},
    Compiler,
};

id::id!(LocalTypeId);

#[derive(Debug)]
pub struct TypeTable {
    types: Vec<TypeInfoOrIdx>,
    enums: Vec<InferredEnum>,
    variants: Vec<InferredEnumVariant>,
    bounds: Vec<Bound>,
    deferred_checks: Vec<(LocalTypeId, Bounds)>,
}
impl Index<LocalTypeId> for TypeTable {
    type Output = TypeInfo;
    fn index(&self, mut index: LocalTypeId) -> &Self::Output {
        loop {
            match &self.types[index.idx()] {
                &TypeInfoOrIdx::Idx(new_index) => {
                    debug_assert_ne!(new_index, index);
                    index = new_index;
                }
                TypeInfoOrIdx::TypeInfo(info) => return info,
            }
        }
    }
}
impl Index<VariantId> for TypeTable {
    type Output = InferredEnumVariant;

    fn index(&self, index: VariantId) -> &Self::Output {
        &self.variants[index.idx()]
    }
}
impl TypeTable {
    pub fn new() -> Self {
        Self {
            types: Vec::new(),
            enums: Vec::new(),
            variants: Vec::new(),
            bounds: Vec::new(),
            deferred_checks: Vec::new(),
        }
    }

    pub fn add(&mut self, info: TypeInfo) -> LocalTypeId {
        let id = LocalTypeId(self.types.len() as _);
        self.types.push(TypeInfoOrIdx::TypeInfo(info));
        id
    }

    pub fn add_info_or_idx(&mut self, info_or_idx: TypeInfoOrIdx) -> LocalTypeId {
        match info_or_idx {
            TypeInfoOrIdx::Idx(idx) => idx,
            TypeInfoOrIdx::TypeInfo(info) => self.add(info),
        }
    }

    pub fn add_unknown(&mut self) -> LocalTypeId {
        self.add(TypeInfo::Unknown)
    }

    pub fn add_enum_type(&mut self) -> InferredEnumId {
        let id = InferredEnumId(self.enums.len() as u32);
        self.enums.push(InferredEnum {
            variants: Vec::new(),
        });
        id
    }

    pub fn get_enum_variants(&self, enum_id: InferredEnumId) -> &[VariantId] {
        &self.enums[enum_id.idx()].variants
    }

    pub fn append_enum_variant(
        &mut self,
        id: InferredEnumId,
        name: Box<str>,
        args: LocalTypeIds,
    ) -> VariantId {
        debug_assert!(args.count != 0, "enum args should contain ordinal type");
        debug_assert!(
            matches!(
                self.types[args.idx as usize],
                TypeInfoOrIdx::TypeInfo(TypeInfo::Unknown)
            ),
            "ordinal should not be filled in yet"
        );
        let variants = &mut self.enums[id.idx()].variants;
        if let Some(&first) = variants.first() {
            let ordinal_ty = int_ty_from_variant_count((variants.len() + 1) as u32);
            let idx = self.variants[first.0 as usize].args.idx;
            // update the ordinal type because it could have changed with the increased variant
            // count
            self.types[idx as usize] = TypeInfoOrIdx::TypeInfo(ordinal_ty);
            // make the ordinal type of the new variant point to the type
            self.types[args.iter().next().unwrap().idx()] = TypeInfoOrIdx::Idx(LocalTypeId(idx));
        } else {
            // we are adding the first variant so we can fill in the ordinal type into the first
            // arg (as unit for now since only one variant is present)
            self.types[args.idx as usize] =
                TypeInfoOrIdx::TypeInfo(TypeInfo::Primitive(Primitive::Unit));
        }
        let ordinal = variants.len() as u32;
        let variant_id = VariantId(self.variants.len() as _);
        self.variants.push(InferredEnumVariant {
            name,
            ordinal,
            args,
        });
        variants.push(variant_id);
        variant_id
    }

    pub fn to_resolved(&self, info: TypeInfo, generics: &[Type]) -> Type {
        match info {
            TypeInfo::Primitive(p) => Type::Primitive(p),
            TypeInfo::Unknown
            | TypeInfo::Integer
            | TypeInfo::Float
            | TypeInfo::Array {
                element: _,
                count: None,
            } => unreachable!(),
            TypeInfo::Pointer(pointee) => {
                Type::Pointer(Box::new(self.to_resolved(self[pointee], generics)))
            }
            TypeInfo::TypeDef(id, inner_generics) => Type::DefId {
                id,
                generics: inner_generics
                    .iter()
                    .map(|generic| self.to_resolved(self[generic], generics))
                    .collect(),
            },
            TypeInfo::Invalid => Type::Invalid,
            TypeInfo::Generic(i) => generics[i as usize].clone(),
            TypeInfo::Array {
                element,
                count: Some(count),
            } => Type::Array(Box::new((self.to_resolved(self[element], generics), count))),
            _ => todo!("type to resolved: {info:?}"),
        }
    }

    pub fn add_multiple(&mut self, infos: impl IntoIterator<Item = TypeInfo>) -> LocalTypeIds {
        let start = self.types.len();
        self.types
            .extend(infos.into_iter().map(TypeInfoOrIdx::TypeInfo));
        let count = self.types.len() - start;
        LocalTypeIds {
            idx: start as _,
            count: count as _,
        }
    }

    pub fn add_multiple_info_or_idx(
        &mut self,
        infos: impl IntoIterator<Item = TypeInfoOrIdx>,
    ) -> LocalTypeIds {
        let start = self.types.len();
        self.types.extend(infos.into_iter());
        let count = self.types.len() - start;
        LocalTypeIds {
            idx: start as _,
            count: count as _,
        }
    }

    pub fn add_multiple_unknown(&mut self, count: u32) -> LocalTypeIds {
        let start = self.types.len() as _;
        self.types.extend(
            std::iter::repeat(TypeInfoOrIdx::TypeInfo(TypeInfo::Unknown)).take(count as usize),
        );
        LocalTypeIds { idx: start, count }
    }

    pub fn add_bounds(&mut self, bounds: impl IntoIterator<Item = Bound>) -> Bounds {
        let start = self.bounds.len() as u32;
        self.bounds.extend(bounds);
        let count = TryInto::<u32>::try_into(self.bounds.len()).unwrap() - start;
        Bounds { start, count }
    }

    pub fn add_missing_bounds(&mut self, count: u32) -> Bounds {
        let start = self.bounds.len() as u32;
        self.bounds.extend((0..count).map(|_| Bound {
            trait_id: (ModuleId::MISSING, TraitId::MISSING),
            generics: LocalTypeIds::EMPTY,
            span: TSpan::MISSING,
        }));
        Bounds { start, count }
    }

    pub fn replace_bound(&mut self, id: BoundId, bound: Bound) {
        self.bounds[id.0 as usize] = bound;
    }

    pub fn get_bounds(&self, bounds: Bounds) -> &[Bound] {
        &self.bounds[bounds.start as usize..bounds.start as usize + bounds.count as usize]
    }

    pub fn get_bound(&self, id: BoundId) -> &Bound {
        &self.bounds[id.0 as usize]
    }

    pub fn defer_impl_check(&mut self, ty: LocalTypeId, bounds: Bounds) {
        self.deferred_checks.push((ty, bounds));
    }

    pub fn replace(&mut self, id: LocalTypeId, info_or_idx: impl Into<TypeInfoOrIdx>) {
        let info_or_idx = info_or_idx.into();
        debug_assert!(
            !matches!(info_or_idx, TypeInfoOrIdx::Idx(idx) if idx == id),
            "created recursive reference",
        );
        self.types[id.idx()] = info_or_idx;
    }

    pub fn replace_value(&mut self, mut id: LocalTypeId, info_or_idx: impl Into<TypeInfoOrIdx>) {
        loop {
            match &mut self.types[id.idx()] {
                TypeInfoOrIdx::Idx(new_id) => id = *new_id,
                value @ TypeInfoOrIdx::TypeInfo(_) => {
                    *value = info_or_idx.into();
                    break;
                }
            }
        }
    }

    pub fn generic_info_from_resolved(&mut self, compiler: &mut Compiler, ty: &Type) -> TypeInfo {
        let ty = self.from_generic_resolved_internal(compiler, ty, None);
        let TypeInfoOrIdx::TypeInfo(info) = ty else {
            // we can't get back a generic since we don't pass in any generics
            unreachable!()
        };
        info
    }

    pub fn info_from_resolved(&mut self, compiler: &mut Compiler, ty: &Type) -> TypeInfo {
        let ty = self.from_generic_resolved(compiler, ty, LocalTypeIds::EMPTY);
        let TypeInfoOrIdx::TypeInfo(info) = ty else {
            // we can't get back a generic since we don't pass in any generics
            unreachable!()
        };
        info
    }

    pub fn from_generic_resolved(
        &mut self,
        compiler: &mut Compiler,
        ty: &Type,
        generics: LocalTypeIds,
    ) -> TypeInfoOrIdx {
        self.from_generic_resolved_internal(compiler, ty, Some(generics))
    }
    /// Only produces an Index instead of a TypeInfo when the Type is Type::Generic
    /// generics: None will produce generic TypeInfos for generic functions
    fn from_generic_resolved_internal(
        &mut self,
        compiler: &mut Compiler,
        ty: &Type,
        generics: Option<LocalTypeIds>,
    ) -> TypeInfoOrIdx {
        let info = match ty {
            Type::Invalid => TypeInfo::Invalid,
            &Type::Primitive(p) => TypeInfo::Primitive(p),
            Type::DefId {
                id,
                generics: inner_generics,
            } => {
                let count = inner_generics.len();
                let generics_ids = self.add_multiple_unknown(count as u32);
                for (resolved, id) in inner_generics.iter().zip(generics_ids.iter()) {
                    let ty = self.from_generic_resolved_internal(compiler, resolved, generics);
                    self.replace(id, ty)
                }
                TypeInfo::TypeDef(*id, generics_ids)
            }
            Type::Pointer(pointee) => {
                let pointee = self.from_generic_resolved_internal(compiler, pointee, generics);
                let pointee = self.add_info_or_idx(pointee);
                TypeInfo::Pointer(pointee)
            }
            Type::Array(b) => {
                let (elem_ty, count) = &**b;
                let element = self.from_generic_resolved_internal(compiler, elem_ty, generics);
                let element = self.add_info_or_idx(element);
                TypeInfo::Array {
                    element,
                    count: Some(*count),
                }
            }
            Type::Tuple(elements) => {
                let element_ids = self.add_multiple_unknown(elements.len() as _);
                for (element, id) in elements.iter().zip(element_ids.iter()) {
                    self.types[id.idx()] =
                        self.from_generic_resolved_internal(compiler, element, generics);
                }
                TypeInfo::Tuple(element_ids)
            }
            &Type::Generic(i) => match generics {
                Some(generics) => return TypeInfoOrIdx::Idx(generics.nth(i.into()).unwrap()),
                None => TypeInfo::Generic(i),
            },
            Type::LocalEnum(_) => todo!("local enum infos"),
            Type::Function(_) => todo!("fn TypeInfo"),
        };
        TypeInfoOrIdx::TypeInfo(info)
    }

    pub fn info_from_unresolved(
        &mut self,
        ty: &types::UnresolvedType,
        compiler: &mut crate::Compiler,
        module: ModuleId,
        scope: ast::ScopeId,
    ) -> TypeInfo {
        match ty {
            types::UnresolvedType::Primitive { ty, .. } => TypeInfo::Primitive(*ty),
            types::UnresolvedType::Unresolved(path, generics) => {
                let def = compiler.resolve_path(module, scope, *path);
                match def {
                    Def::Invalid => TypeInfo::Invalid,
                    Def::GenericType(id) => {
                        // TODO: decide if types without generic annotations should be allowed
                        let required_generics = compiler.get_resolved_type_generic_count(id);
                        let Some((generics, generics_span)) = generics else {
                            compiler.errors.emit_err(
                                Error::InvalidGenericCount {
                                    expected: required_generics,
                                    found: 0,
                                }
                                .at_span(ty.span().in_mod(module)),
                            );
                            return TypeInfo::Invalid;
                        };
                        let count = generics.len() as u8;
                        if count != required_generics {
                            compiler.errors.emit_err(
                                Error::InvalidGenericCount {
                                    expected: required_generics,
                                    found: count,
                                }
                                .at_span(generics_span.in_mod(module)),
                            );
                            return TypeInfo::Invalid;
                        }
                        let generic_types = self.add_multiple_unknown(count.into());
                        for (ty, r) in generics.iter().zip(generic_types.iter()) {
                            let info = self.info_from_unresolved(ty, compiler, module, scope);
                            self.replace(r, TypeInfoOrIdx::TypeInfo(info));
                        }
                        TypeInfo::TypeDef(id, generic_types)
                    }
                    Def::Type(ty) => {
                        if let Some((_, span)) = generics {
                            compiler
                                .errors
                                .emit_err(Error::UnexpectedGenerics.at_span(span.in_mod(module)));
                            return TypeInfo::Invalid;
                        }
                        let generics = generics.as_ref().map(|(generics, _)| {
                            let generic_infos = self.add_multiple_unknown(generics.len() as _);
                            for (r, ty) in generic_infos.iter().zip(generics) {
                                let info = self.info_from_unresolved(ty, compiler, module, scope);
                                self.replace(r, info);
                            }
                            generic_infos
                        });
                        let TypeInfoOrIdx::TypeInfo(info) =
                            self.from_generic_resolved_internal(compiler, &ty, generics)
                        else {
                            unreachable!()
                        };
                        info
                    }
                    Def::ConstValue(_)
                    | Def::Module(_)
                    | Def::Global(_, _)
                    | Def::Function(_, _)
                    | Def::Trait(_, _) => {
                        compiler
                            .errors
                            .emit_err(Error::TypeExpected.at_span(path.span().in_mod(module)));
                        TypeInfo::Invalid
                    }
                }
            }
            types::UnresolvedType::Pointer(b) => {
                let (pointee, _) = &**b;
                let pointee = self.info_from_unresolved(pointee, compiler, module, scope);
                TypeInfo::Pointer(self.add(pointee))
            }
            types::UnresolvedType::Array(b) => {
                let (elem, count, _) = &**b;
                let elem = self.info_from_unresolved(elem, compiler, module, scope);
                TypeInfo::Array {
                    element: self.add(elem),
                    count: *count,
                }
            }
            types::UnresolvedType::Tuple(elems, _) => {
                let ids = LocalTypeIds {
                    idx: self.types.len() as _,
                    count: elems.len() as _,
                };
                self.types.extend(
                    std::iter::repeat(TypeInfoOrIdx::TypeInfo(TypeInfo::Unknown)).take(elems.len()),
                );

                for (id, unresolved) in ids.iter().zip(elems) {
                    let info = self.info_from_unresolved(unresolved, compiler, module, scope);
                    self.types[id.idx()] = TypeInfoOrIdx::TypeInfo(info);
                }

                TypeInfo::Tuple(ids)
            }
            types::UnresolvedType::Function { .. } => todo!("fn TypeInfo"),
            types::UnresolvedType::Infer(_) => TypeInfo::Unknown,
        }
    }

    pub fn compatible_with_type(&self, info: TypeInfo, ty: &Type) -> bool {
        if let Type::Generic(_) = ty {
            // check that the generics can the type info
            todo!()
        }
        // TODO
        #[allow(unused)]
        match info {
            TypeInfo::Unknown => true,
            TypeInfo::UnknownSatisfying(_bounds) => {
                todo!("check bound compatibility")
            }
            TypeInfo::Primitive(p) => {
                let &Type::Primitive(p2) = ty else {
                    return false;
                };
                p == p2
            }
            TypeInfo::Integer => {
                let Type::Primitive(p) = ty else { return false };
                p.is_int()
            }
            TypeInfo::Float => {
                let Type::Primitive(p) = ty else { return false };
                p.is_float()
            }
            TypeInfo::TypeDef(id, generics) => {
                let Type::DefId {
                    id: ty_id,
                    generics: ty_generics,
                } = ty
                else {
                    return false;
                };
                if id != *ty_id {
                    return false;
                }
                debug_assert_eq!(generics.count, ty_generics.len() as _);
                for (id, ty) in generics.iter().zip(ty_generics) {
                    if !self.compatible_with_type(self[id], ty) {
                        return false;
                    }
                }
                true
            }
            TypeInfo::Pointer(_) => todo!(),
            TypeInfo::Array { element, count } => todo!(),
            TypeInfo::Enum(_) => todo!(),
            TypeInfo::Tuple(_) => todo!(),
            TypeInfo::TypeItem { ty } => todo!(),
            TypeInfo::TraitItem { module, id } => todo!(),
            TypeInfo::FunctionItem {
                module,
                function,
                generics,
            } => todo!(),
            TypeInfo::ModuleItem(_) => todo!(),
            TypeInfo::MethodItem {
                module,
                function,
                generics,
            } => todo!(),
            TypeInfo::TraitMethodItem {
                module,
                trait_id,
                method_index,
            } => todo!(),
            TypeInfo::EnumVariantItem {
                enum_type,
                generics,
                ordinal,
                arg_types,
            } => todo!(),
            TypeInfo::Generic(_) => todo!(),
            TypeInfo::Invalid => todo!(),
        }
    }

    pub fn unify(
        &mut self,
        mut a: LocalTypeId,
        mut b: LocalTypeId,
        generics: &Generics,
        compiler: &mut Compiler,
        span: impl FnOnce() -> Span,
    ) {
        let a_ty = loop {
            match self.types[a.idx()] {
                TypeInfoOrIdx::Idx(idx) => a = idx,
                TypeInfoOrIdx::TypeInfo(ty) => break ty,
            }
        };
        let b_ty = loop {
            match self.types[b.idx()] {
                TypeInfoOrIdx::Idx(idx) => b = idx,
                TypeInfoOrIdx::TypeInfo(ty) => break ty,
            }
        };
        if a == b {
            // a and b point to the same indices
            return;
        }
        self.types[b.idx()] = TypeInfoOrIdx::Idx(a);
        let new = unify(a_ty, b_ty, self, generics, compiler, a).unwrap_or_else(|| {
            let mut expected = String::new();
            self.type_to_string(compiler, a_ty, &mut expected);
            let mut found = String::new();
            self.type_to_string(compiler, b_ty, &mut found);
            compiler
                .errors
                .emit_err(Error::MismatchedType { expected, found }.at_span(span()));
            TypeInfo::Invalid
        });
        self.types[a.idx()] = TypeInfoOrIdx::TypeInfo(new);
    }

    fn try_unify(
        &mut self,
        mut a: LocalTypeId,
        mut b: LocalTypeId,
        generics: &Generics,
        compiler: &mut Compiler,
    ) -> bool {
        let original_b = b;
        let a_ty = loop {
            match self.types[a.idx()] {
                TypeInfoOrIdx::Idx(idx) => a = idx,
                TypeInfoOrIdx::TypeInfo(ty) => break ty,
            }
        };
        let b_ty = loop {
            match self.types[b.idx()] {
                TypeInfoOrIdx::Idx(idx) => b = idx,
                TypeInfoOrIdx::TypeInfo(ty) => break ty,
            }
        };
        a == b
            || unify(a_ty, b_ty, self, generics, compiler, a)
                .map(|unified| {
                    self.types[a.idx()] = TypeInfoOrIdx::TypeInfo(unified);
                    self.types[b.idx()] = TypeInfoOrIdx::Idx(a);
                    self.types[original_b.idx()] = TypeInfoOrIdx::Idx(a);
                })
                .is_some()
    }

    pub fn specify(
        &mut self,
        a: LocalTypeId,
        info: TypeInfo,
        function_generics: &Generics,
        compiler: &mut Compiler,
        span: impl FnOnce() -> Span,
    ) {
        if let Err((a, b)) = self.try_specify(a, info, function_generics, compiler) {
            self.mismatched_type_error(compiler, a, b, span());
        }
    }

    pub fn specify_resolved(
        &mut self,
        id: LocalTypeId,
        resolved: &Type,
        generics: LocalTypeIds,
        function_generics: &Generics,
        compiler: &mut Compiler,
        span: impl FnOnce() -> Span,
    ) {
        if let Err((a, b)) =
            self.try_specify_resolved(id, resolved, generics, function_generics, compiler)
        {
            self.mismatched_type_error(compiler, a, b, span());
        }
    }

    pub fn specify_enum_literal(
        &mut self,
        expected: LocalTypeId,
        name: &str,
        arg_count: u32,
        compiler: &mut Compiler,
    ) -> Result<(OrdinalType, LocalTypeIds), Option<Error>> {
        // Do the type checking manually instead of using `specify`.
        // This allows skipping construction of unneeded enum variant representations.
        let mut idx = expected;
        while let TypeInfoOrIdx::Idx(next) = self.types[idx.idx()] {
            idx = next;
        }
        match self[idx] {
            TypeInfo::Invalid => {
                return Err(None);
            }
            TypeInfo::Enum(id) => {
                let variants = self.get_enum_variants(id);
                if let Some(variant) = variants
                    .iter()
                    .copied()
                    .find(|&variant| (&*self[variant].name == name))
                {
                    let arg_types = self[variant].args;
                    Ok((OrdinalType::Inferred(variant), arg_types))
                } else {
                    let arg_types = self.add_multiple_unknown(arg_count + 1);
                    let variant = self.append_enum_variant(id, name.into(), arg_types);
                    Ok((OrdinalType::Inferred(variant), arg_types))
                }
            }
            TypeInfo::Unknown => {
                let arg_types = self.add_multiple_unknown(arg_count + 1);
                let enum_id = self.add_enum_type();
                let variant = self.append_enum_variant(enum_id, name.into(), arg_types);
                self.replace(idx, TypeInfo::Enum(enum_id));
                Ok((OrdinalType::Inferred(variant), arg_types))
            }
            TypeInfo::TypeDef(id, generics) => {
                let def = Rc::clone(&compiler.get_resolved_type_def(id).def);
                if let ResolvedTypeDef::Enum(enum_) = &*def {
                    let variant = enum_.variants.iter().zip(0..).find_map(
                        |((variant_name, arg_types), i)| {
                            (variant_name == name).then_some((i, &*arg_types))
                        },
                    );
                    if let Some((variant_index, arg_types)) = variant {
                        if arg_types.len() != arg_count as usize {
                            Err(Some(Error::InvalidArgCount {
                                expected: arg_types.len() as _,
                                varargs: false,
                                found: arg_count,
                            }))
                        } else {
                            let arg_type_ids =
                                self.add_multiple_unknown(arg_types.len() as u32 + 1);
                            let mut arg_type_iter = arg_type_ids.iter();
                            self.replace(
                                arg_type_iter.next().unwrap(),
                                int_ty_from_variant_count(enum_.variants.len() as u32),
                            );
                            for (r, ty) in arg_type_iter.zip(arg_types.iter()) {
                                let ty = self.from_generic_resolved(compiler, ty, generics);
                                self.replace(r, ty);
                            }

                            Ok((OrdinalType::Known(variant_index), arg_type_ids))
                        }
                    } else {
                        Err(Some(Error::NonexistantEnumVariant))
                    }
                } else {
                    let mut expected_str = String::new();
                    self.type_to_string(compiler, self[expected], &mut expected_str);
                    Err(Some(Error::MismatchedType {
                        expected: expected_str,
                        found: format!("enum variant \"{name}\""),
                    }))
                }
            }
            _ => {
                let mut expected_str = String::new();
                self.type_to_string(compiler, self[expected], &mut expected_str);
                Err(Some(Error::MismatchedType {
                    expected: expected_str,
                    found: format!("enum variant \"{name}\""),
                }))
            }
        }
    }

    fn mismatched_type_error(&self, compiler: &mut Compiler, a: TypeInfo, b: TypeInfo, span: Span) {
        let mut expected = String::new();
        self.type_to_string(compiler, a, &mut expected);
        let mut found = String::new();
        self.type_to_string(compiler, b, &mut found);
        compiler
            .errors
            .emit_err(Error::MismatchedType { expected, found }.at_span(span));
    }

    pub fn try_specify_resolved(
        &mut self,
        id: LocalTypeId,
        resolved: &Type,
        generics: LocalTypeIds,
        function_generics: &Generics,
        compiler: &mut Compiler,
    ) -> Result<(), (TypeInfo, TypeInfo)> {
        // PERF:could special-case this function to avoid instantiating the Type
        let resolved_info = self.from_generic_resolved(compiler, resolved, generics);
        match resolved_info {
            TypeInfoOrIdx::TypeInfo(info) => {
                self.try_specify(id, info, function_generics, compiler)
            }
            TypeInfoOrIdx::Idx(idx) => {
                if self.try_unify(id, idx, function_generics, compiler) {
                    Ok(())
                } else {
                    Err((self[id], self[idx]))
                }
            }
        }
    }

    pub fn try_specify(
        &mut self,
        mut a: LocalTypeId,
        info: TypeInfo,
        function_generics: &Generics,
        compiler: &mut Compiler,
    ) -> Result<(), (TypeInfo, TypeInfo)> {
        let a_ty = loop {
            match self.types[a.idx()] {
                TypeInfoOrIdx::Idx(idx) => a = idx,
                TypeInfoOrIdx::TypeInfo(info) => break info,
            }
        };
        let Some(info) = unify(a_ty, info, self, function_generics, compiler, a) else {
            self.types[a.idx()] = TypeInfoOrIdx::TypeInfo(TypeInfo::Invalid);
            return Err((a_ty, info));
        };
        self.types[a.idx()] = TypeInfoOrIdx::TypeInfo(info);
        Ok(())
    }

    pub fn invalidate(&mut self, mut ty: LocalTypeId) {
        loop {
            match self.types[ty.idx()] {
                TypeInfoOrIdx::Idx(idx) => ty = idx,
                TypeInfoOrIdx::TypeInfo(ref mut info) => {
                    *info = TypeInfo::Invalid;
                    break;
                }
            }
        }
    }

    pub fn dump_type(&self, compiler: &Compiler, ty: LocalTypeId) {
        let mut s = String::new();
        self.type_to_string(compiler, self[ty], &mut s);
        eprint!("{s}");
    }

    pub fn type_to_string(&self, compiler: &Compiler, ty: TypeInfo, s: &mut String) {
        use std::fmt::Write;
        // TODO: some of these types could be described better if they could look up symbols
        match ty {
            TypeInfo::Unknown | TypeInfo::UnknownSatisfying { .. } => s.push_str("<unknown>"),
            TypeInfo::Primitive(p) => s.push_str(p.into()),
            TypeInfo::Integer => s.push_str("<integer>"),
            TypeInfo::Float => s.push_str("<float>"),
            TypeInfo::TypeDef(id, generics) => {
                let name = compiler.get_type_name(id);
                s.push_str(name);
                if generics.count != 0 {
                    s.push('[');
                    for (i, generic) in generics.iter().enumerate() {
                        if i != 0 {
                            s.push_str(", ");
                        }
                        self.type_to_string(compiler, self[generic], s);
                    }
                    s.push(']');
                }
            }
            TypeInfo::Pointer(pointee) => {
                s.push('*');
                self.type_to_string(compiler, self[pointee], s);
            }
            TypeInfo::Array { element, count } => {
                s.push('[');
                self.type_to_string(compiler, self[element], s);
                s.push_str("; ");
                if let Some(count) = count {
                    write!(s, "{}]", count).unwrap();
                } else {
                    s.push_str("_]");
                }
            }
            TypeInfo::Enum(id) => self.enum_to_string(compiler, s, &self.enums[id.idx()].variants),
            TypeInfo::Tuple(members) => {
                s.push('(');
                let mut first = true;
                for member in members.iter() {
                    if first {
                        first = false;
                    } else {
                        s.push_str(", ");
                    }
                    self.type_to_string(compiler, self[member], s);
                }
                if members.iter().count() == 1 {
                    s.push_str(",)");
                } else {
                    s.push(')');
                }
            }
            TypeInfo::TypeItem { ty } => {
                s.push_str("<type item: (");
                self.type_to_string(compiler, self[ty], s);
                s.push_str(")>");
            }
            TypeInfo::TraitItem { .. } => s.push_str("<trait item>"),
            TypeInfo::FunctionItem { .. } => s.push_str("<function item>"),
            TypeInfo::ModuleItem(_) => s.push_str("<module item>"),
            TypeInfo::MethodItem { .. } => s.push_str("<method item>"),
            TypeInfo::TraitMethodItem { .. } => s.push_str("<trait method item>"),
            TypeInfo::EnumVariantItem { .. } => s.push_str("<enum variant item>"),
            TypeInfo::Generic(i) => write!(s, "${i}").unwrap(),
            TypeInfo::Invalid => s.push_str("<invalid>"),
        }
    }

    pub fn enum_to_string(&self, compiler: &Compiler, s: &mut String, variants: &[VariantId]) {
        s.push_str("enum { ");
        for (i, variant) in variants.iter().enumerate() {
            let variant = &self.variants[variant.idx()];
            if i != 0 {
                s.push_str(", ");
            }
            s.push_str(&variant.name);
            if variant.args.count != 1 {
                s.push('(');
                for (i, arg) in variant.args.iter().skip(1).enumerate() {
                    if i != 0 {
                        s.push_str(", ");
                    }
                    self.type_to_string(compiler, self[arg], s);
                }
                s.push(')');
            }
        }
        s.push_str(" }");
    }

    pub fn get_info_or_idx(&self, info_or_idx: TypeInfoOrIdx) -> TypeInfo {
        match info_or_idx {
            TypeInfoOrIdx::TypeInfo(info) => info,
            TypeInfoOrIdx::Idx(idx) => self[idx],
        }
    }

    pub fn finish(&mut self, compiler: &mut Compiler, generics: &Generics, module: ModuleId) {
        for (ty, bounds) in std::mem::take(&mut self.deferred_checks) {
            let mut idx = ty;
            let info = loop {
                match self.types[idx.0 as usize] {
                    TypeInfoOrIdx::Idx(new_idx) => idx = new_idx,
                    TypeInfoOrIdx::TypeInfo(info) => break info,
                }
            };
            if matches!(info, TypeInfo::Invalid) {
                continue;
            }
            for bound in bounds.iter() {
                let bound = &self.bounds[bound.0 as usize];
                let span = bound.span;
                let Some(checked_trait) =
                    compiler.get_checked_trait(bound.trait_id.0, bound.trait_id.1)
                else {
                    continue;
                };
                let checked_trait = Rc::clone(checked_trait);
                // TODO: probably should retry impl candidates in a loop as long as one bound has
                // multiple candidates but progress is made
                match traits::get_impl_candidates(
                    info,
                    bound.generics,
                    self,
                    generics,
                    &checked_trait,
                ) {
                    traits::Candidates::None => {
                        let trait_name = checked_trait.name.clone();
                        let mut type_name = String::new();
                        self.type_to_string(compiler, info, &mut type_name);
                        compiler.errors.emit_err(
                            Error::UnsatisfiedTraitBound {
                                trait_name,
                                ty: type_name,
                            }
                            .at_span(span.in_mod(module)),
                        );
                        self.types[idx.0 as usize] = TypeInfoOrIdx::TypeInfo(TypeInfo::Invalid);
                    }
                    traits::Candidates::Unique(impl_) => {
                        let self_ty =
                            impl_.instantiate(bound.generics, generics, self, compiler, span);
                        match self_ty {
                            TypeInfoOrIdx::TypeInfo(info) => {
                                self.specify(ty, info, generics, compiler, || span.in_mod(module))
                            }
                            TypeInfoOrIdx::Idx(self_idx) => {
                                self.unify(idx, self_idx, generics, compiler, || {
                                    span.in_mod(module)
                                })
                            }
                        }
                    }
                    traits::Candidates::Multiple => {
                        let name = checked_trait.name.clone();
                        let retry_with = match info {
                            TypeInfo::Integer => Some(TypeInfo::Primitive(Primitive::I32)),
                            TypeInfo::Float => Some(TypeInfo::Primitive(Primitive::F32)),
                            _ => None,
                        };
                        let new_candidate = retry_with.and_then(|new_info| {
                            let new_candidates = traits::get_impl_candidates(
                                new_info,
                                bound.generics,
                                self,
                                generics,
                                &checked_trait,
                            );
                            if let traits::Candidates::Unique(impl_) = new_candidates {
                                Some((new_info, impl_))
                            } else {
                                None
                            }
                        });
                        if let Some((new_info, impl_)) = new_candidate {
                            impl_.instantiate(bound.generics, generics, self, compiler, span);
                            self.replace(idx, new_info);
                        } else {
                            compiler.errors.emit_err(
                                Error::TypeAnnotationNeeded {
                                    bound: name, // TODO: should also show generics here
                                }
                                .at_span(span.in_mod(module)),
                            );
                            self.types[idx.0 as usize] = TypeInfoOrIdx::TypeInfo(TypeInfo::Invalid);
                        }
                    }
                }
            }
        }
        for ty in &mut self.types {
            let TypeInfoOrIdx::TypeInfo(ty) = ty else {
                continue;
            };
            match ty {
                TypeInfo::Unknown => *ty = TypeInfo::Primitive(Primitive::Unit),
                TypeInfo::UnknownSatisfying(bounds) => {
                    if let Some(first_bound) = bounds.iter().next() {
                        let bound = &self.bounds[first_bound.0 as usize];
                        let name = compiler
                            .get_trait_name(bound.trait_id.0, bound.trait_id.1)
                            .to_owned();
                        compiler.errors.emit_err(
                            Error::TypeMustBeKnownHere {
                                needed_bound: Some(name),
                            }
                            .at_span(bound.span.in_mod(module)),
                        );
                        *ty = TypeInfo::Invalid;
                    } else {
                        *ty = TypeInfo::Primitive(Primitive::Unit);
                    }
                }
                TypeInfo::Integer => *ty = TypeInfo::Primitive(Primitive::I32),
                TypeInfo::Float => *ty = TypeInfo::Primitive(Primitive::F32),
                TypeInfo::Array {
                    element: _,
                    count: count @ None,
                } => *count = Some(0),
                _ => {}
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TypeInfoOrIdx {
    TypeInfo(TypeInfo),
    Idx(LocalTypeId),
}
impl From<TypeInfo> for TypeInfoOrIdx {
    fn from(value: TypeInfo) -> Self {
        Self::TypeInfo(value)
    }
}
impl From<LocalTypeId> for TypeInfoOrIdx {
    fn from(value: LocalTypeId) -> Self {
        Self::Idx(value)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LocalTypeIds {
    pub idx: u32,
    pub count: u32,
}
impl LocalTypeIds {
    pub const EMPTY: Self = Self { idx: 0, count: 0 };

    pub fn iter(self) -> impl Iterator<Item = LocalTypeId> {
        (self.idx..self.idx + self.count).map(LocalTypeId)
    }

    pub fn nth(self, i: u32) -> Option<LocalTypeId> {
        (i < self.count).then_some(LocalTypeId(self.idx + i))
    }
}
impl From<LocalTypeId> for LocalTypeIds {
    fn from(value: LocalTypeId) -> Self {
        Self {
            idx: value.0,
            count: 1,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Bound {
    pub trait_id: (ModuleId, TraitId),
    pub generics: LocalTypeIds,
    /// the location where the bound on the type variable is introduced
    pub span: TSpan,
}

#[derive(Debug, Clone, Copy)]
pub struct Bounds {
    start: u32,
    count: u32,
}
impl Bounds {
    pub fn iter(self) -> impl ExactSizeIterator<Item = BoundId> {
        (self.start..self.start + self.count).map(BoundId)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct BoundId(u32);

#[derive(Debug, Clone, Copy)]
pub enum TypeInfo {
    Unknown,
    /// an unknown type that has to implement a list of trait bounds
    UnknownSatisfying(Bounds),
    Primitive(Primitive),
    Integer,
    Float,
    TypeDef(TypeId, LocalTypeIds),
    Pointer(LocalTypeId),
    Array {
        element: LocalTypeId,
        count: Option<u32>,
    },
    Enum(InferredEnumId),
    Tuple(LocalTypeIds),
    TypeItem {
        ty: LocalTypeId,
    },
    TraitItem {
        module: ModuleId,
        id: ast::TraitId,
    },
    FunctionItem {
        module: ModuleId,
        function: ast::FunctionId,
        generics: LocalTypeIds,
    },
    ModuleItem(ModuleId),
    MethodItem {
        module: ModuleId,
        function: ast::FunctionId,
        generics: LocalTypeIds,
    },
    TraitMethodItem {
        module: ModuleId,
        trait_id: ast::TraitId,
        method_index: u16,
    },
    EnumVariantItem {
        enum_type: TypeId,
        generics: LocalTypeIds,
        ordinal: u32,
        /// always includes the ordinal type as it's first type
        arg_types: LocalTypeIds,
    },
    Generic(u8),
    Invalid,
}
impl TypeInfo {
    pub fn is_invalid(&self) -> bool {
        matches!(self, Self::Invalid)
    }
}
impl From<Primitive> for TypeInfo {
    fn from(value: Primitive) -> Self {
        TypeInfo::Primitive(value)
    }
}

id::id!(InferredEnumId);
id::id!(VariantId);

#[derive(Debug)]
pub struct InferredEnum {
    variants: Vec<VariantId>,
}

#[derive(Debug)]
pub struct InferredEnumVariant {
    pub name: Box<str>,
    pub ordinal: u32,
    pub args: LocalTypeIds,
}

#[derive(Debug, Clone, Copy)]
pub enum OrdinalType {
    Inferred(VariantId),
    Known(u32),
}
