use std::ops::{Index, IndexMut};

use dmap::DHashMap;
use error::Error;
use error::span::TSpan;
use parser::ast::{self, ModuleId, Primitive, TraitId, UnresolvedType};

mod display;
mod unify;

use unify::unify;

use crate::{
    Compiler, InvalidTypeError, Type,
    check::{
        expr::{type_from_variant_count, type_info_from_variant_count},
        traits,
    },
    compiler::{
        Def, Generics, Instance, ModuleSpan, ResolvedEnumDef, ResolvedTypeContent, ResolvedTypeDef,
    },
    helpers::IteratorExt,
    layout::Layout,
    types::{BaseType, TypeFull, Types},
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
impl IndexMut<VariantId> for TypeTable {
    fn index_mut(&mut self, index: VariantId) -> &mut Self::Output {
        &mut self.variants[index.idx()]
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
        self.add(TypeInfo::Unknown(Bounds::EMPTY))
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
                TypeInfoOrIdx::TypeInfo(TypeInfo::Unknown(bounds)) if bounds.is_empty()
            ),
            "ordinal should not be filled in yet"
        );
        let variants = &mut self.enums[id.idx()].variants;
        if let Some(&first) = variants.first() {
            let ordinal_ty = type_info_from_variant_count((variants.len() + 1) as u32);
            let idx = self.variants[first.0 as usize].args.idx;
            // update the ordinal type because it could have changed with the increased variant
            // count
            self.types[idx as usize] = TypeInfoOrIdx::TypeInfo(ordinal_ty);
            // make the ordinal type of the new variant point to the type
            self.types[args.iter().next().unwrap().idx()] = TypeInfoOrIdx::Idx(LocalTypeId(idx));
        } else {
            // we are adding the first variant so we can fill in the ordinal type into the first
            // arg (as unit for now since only one variant is present)
            self.types[args.idx as usize] = TypeInfoOrIdx::TypeInfo(TypeInfo::UNIT);
        }
        let ordinal = variants.len() as u64;
        let variant_id = VariantId(self.variants.len() as _);
        self.variants.push(InferredEnumVariant {
            name,
            ordinal,
            args,
        });
        variants.push(variant_id);
        variant_id
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
        self.types.extend(infos);
        let count = self.types.len() - start;
        LocalTypeIds {
            idx: start as _,
            count: count as _,
        }
    }

    pub fn add_multiple_unknown(&mut self, count: u32) -> LocalTypeIds {
        let start = self.types.len() as _;
        self.types.extend(std::iter::repeat_n(
            TypeInfoOrIdx::TypeInfo(TypeInfo::Unknown(Bounds::EMPTY)),
            count as usize,
        ));
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
            trait_id: (ModuleId::MISSING, TraitId::from_inner(u32::MAX)),
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

    fn find_shorten(&mut self, mut var: LocalTypeId) -> (LocalTypeId, TypeInfo) {
        let original_var = var;
        let (final_var, info) = loop {
            match self.types[var.idx()] {
                TypeInfoOrIdx::TypeInfo(info) => break (var, info),
                TypeInfoOrIdx::Idx(v) => var = v,
            }
        };
        // now shorten all links by pointing them to the final index
        let mut var = original_var;
        while let TypeInfoOrIdx::Idx(new) = self.types[var.idx()] {
            self.types[var.idx()] = TypeInfoOrIdx::Idx(final_var);
            var = new;
        }
        (final_var, info)
    }

    pub fn from_annotation(
        &mut self,
        ty: &UnresolvedType,
        compiler: &crate::Compiler,
        module: ModuleId,
        scope: ast::ScopeId,
    ) -> TypeInfo {
        match ty {
            &UnresolvedType::Primitive { ty, .. } => ty.into(),
            UnresolvedType::Unresolved(path, generics) => {
                let def = compiler.resolve_path(module, scope, *path);
                match def {
                    Def::Invalid => TypeInfo::INVALID,
                    Def::BaseType(id) => {
                        // TODO: decide if types without generic annotations should be allowed
                        let required_generics = compiler.get_base_type_generic_count(id);
                        let Some((generics, generics_span)) = generics else {
                            compiler.errors.emit(
                                module,
                                Error::InvalidGenericCount {
                                    expected: required_generics,
                                    found: 0,
                                }
                                .at_span(ty.span()),
                            );
                            return TypeInfo::INVALID;
                        };
                        let count = generics.len() as u8;
                        if count != required_generics {
                            compiler.errors.emit(
                                module,
                                Error::InvalidGenericCount {
                                    expected: required_generics,
                                    found: count,
                                }
                                .at_span(*generics_span),
                            );
                            return TypeInfo::INVALID;
                        }
                        let required_ty = compiler.get_base_type_def(id);
                        let generic_types = required_ty.generics.instantiate(self, ty.span());
                        for (ty, r) in generics.iter().zip(generic_types.iter()) {
                            let info = self.from_annotation(ty, compiler, module, scope);
                            self.replace(r, TypeInfoOrIdx::TypeInfo(info));
                        }
                        TypeInfo::Instance(id, generic_types)
                    }
                    Def::Type(ty) => {
                        if let &Some((_, span)) = generics {
                            compiler
                                .errors
                                .emit(module, Error::UnexpectedGenerics.at_span(span));
                            return TypeInfo::INVALID;
                        }
                        TypeInfo::Known(ty)
                    }
                    Def::ConstValue(_) => todo!("consts as types"),
                    Def::Module(_) | Def::Global(_, _) | Def::Function(_, _) | Def::Trait(_, _) => {
                        compiler
                            .errors
                            .emit(module, Error::TypeExpected.at_span(path.span()));
                        TypeInfo::INVALID
                    }
                }
            }
            UnresolvedType::Pointer(b) => {
                let (pointee, _) = &**b;
                let pointee = self.from_annotation(pointee, compiler, module, scope);
                TypeInfo::Instance(BaseType::Pointer, self.add(pointee).into())
            }
            UnresolvedType::Array(b) => {
                let (elem, count, _) = &**b;
                let elem = self.from_annotation(elem, compiler, module, scope);
                let count_const = if let Some(count) = *count {
                    TypeInfo::Known(compiler.types.intern(TypeFull::Const(count.into())))
                } else {
                    TypeInfo::UnknownConst
                };
                TypeInfo::Instance(BaseType::Array, self.add_multiple([elem, count_const]))
            }
            UnresolvedType::Tuple(elems, _) => {
                let ids = self.add_multiple_unknown(elems.len() as _);

                for (id, unresolved) in ids.iter().zip(elems) {
                    let info = self.from_annotation(unresolved, compiler, module, scope);
                    self.types[id.idx()] = TypeInfoOrIdx::TypeInfo(info);
                }

                TypeInfo::Instance(BaseType::Tuple, ids)
            }
            UnresolvedType::Function {
                span_and_return_type,
                params,
            } => {
                let return_and_param_ids = self.add_multiple_unknown(1 + params.len() as u32);
                for (param, r) in params.iter().zip(return_and_param_ids.skip(1).iter()) {
                    let info = self.from_annotation(param, compiler, module, scope);
                    self.types[r.idx()] = TypeInfoOrIdx::TypeInfo(info);
                }
                let return_type =
                    self.from_annotation(&span_and_return_type.1, compiler, module, scope);
                self.replace(return_and_param_ids.nth(0).unwrap(), return_type);
                TypeInfo::Instance(BaseType::Function, return_and_param_ids)
            }
            UnresolvedType::Infer(_) => TypeInfo::Unknown(Bounds::EMPTY),
        }
    }

    pub fn compatible_with_type(
        &self,
        types: &Types,
        info: TypeInfo,
        ty: Type,
    ) -> Result<bool, InvalidTypeError> {
        let full = types.lookup(ty);
        if let TypeFull::Generic(_) = full {
            // FIXME: it is not always correct to return true here as the generic may appear in
            // multiple places. Therefore, unification would be needed but isn't trivially possible
            //
            return Ok(true);
        }
        #[allow(unused)]
        Ok(match info {
            TypeInfo::Instance(BaseType::Invalid, _) => return Err(InvalidTypeError),
            TypeInfo::UnknownConst => matches!(types.lookup(ty), TypeFull::Const(_)),
            TypeInfo::Known(known) => known.is_same_as(ty)?,
            TypeInfo::Unknown(bounds) => bounds
                .iter()
                .all(|bound| todo!("check bound compatibility")),
            TypeInfo::Integer => matches!(full, TypeFull::Instance(base, _) if base.is_int()),
            TypeInfo::Float => matches!(full, TypeFull::Instance(base, _) if base.is_float()),
            TypeInfo::Instance(base, generics) => {
                let TypeFull::Instance(type_base, type_generics) = full else {
                    return Ok(false);
                };
                if base != type_base || generics.count != type_generics.len() as u32 {
                    return Ok(false);
                }
                for (v, &ty) in generics.iter().zip(type_generics) {
                    if !self.compatible_with_type(types, self[v], ty)? {
                        return Ok(false);
                    }
                }
                true
            }
            TypeInfo::Enum(_) => todo!("check if local enum could infer to real type"),
            TypeInfo::BaseTypeItem(_)
            | TypeInfo::TypeItem(_)
            | TypeInfo::TraitItem { .. }
            | TypeInfo::FunctionItem { .. }
            | TypeInfo::ModuleItem(_)
            | TypeInfo::MethodItem { .. }
            | TypeInfo::TraitMethodItem { .. }
            | TypeInfo::EnumVariantItem { .. } => false,
            // a generic type from the function is not compatible with any concrete type
            TypeInfo::Generic(i) => false,
        })
    }

    pub fn unify(
        &mut self,
        mut a: LocalTypeId,
        mut b: LocalTypeId,
        generics: &Generics,
        compiler: &Compiler,
        span: impl FnOnce() -> ModuleSpan,
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
            let ModuleSpan { module, span } = span();
            compiler.errors.emit(
                module,
                Error::MismatchedType { expected, found }.at_span(span),
            );
            TypeInfo::INVALID
        });
        self.types[a.idx()] = TypeInfoOrIdx::TypeInfo(new);
    }

    fn try_unify(
        &mut self,
        mut a: LocalTypeId,
        mut b: LocalTypeId,
        generics: &Generics,
        compiler: &Compiler,
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
        compiler: &Compiler,
        span: impl FnOnce() -> ModuleSpan,
    ) {
        if let Err((a, b)) = self.try_specify(a, info, function_generics, compiler) {
            self.mismatched_type_error(compiler, a, b, span());
        }
    }

    /// Specifies the base type with the supplied generic count. Returns the generics.
    /// Just returns the existing generics if the type was already correct
    pub fn specify_base(
        &mut self,
        ty: LocalTypeId,
        base: BaseType,
        generic_count: u32,
        function_generics: &Generics,
        compiler: &Compiler,
        span: impl FnOnce() -> ModuleSpan,
        fresh_generics: impl FnOnce(&mut Self) -> LocalTypeIds,
    ) -> LocalTypeIds {
        let (idx, info) = self.find_shorten(ty);
        // check if the type is already correct to avoid adding unnecessary variables
        if let TypeInfo::Instance(existing_base, generics) = info
            && existing_base == base
            && generics.count == generic_count
        {
            return generics;
        }
        let generics = fresh_generics(self);
        let info = TypeInfo::Instance(base, generics);
        self.specify(idx, info, function_generics, compiler, span);
        generics
    }

    pub fn specify_type_instance(
        &mut self,
        id: LocalTypeId,
        ty: Type,
        generics: LocalTypeIds,
        function_generics: &Generics,
        compiler: &Compiler,
        span: impl FnOnce() -> ModuleSpan,
    ) {
        if let Err((a, b)) =
            self.try_specify_type_instance(id, ty, generics, function_generics, compiler)
        {
            self.mismatched_type_error(compiler, a, b, span());
        }
    }

    pub fn specify_enum_literal(
        &mut self,
        expected: LocalTypeId,
        name: &str,
        arg_count: u32,
        compiler: &Compiler,
    ) -> Result<(OrdinalType, LocalTypeIds), Option<Error>> {
        // Do the type checking manually instead of using `specify`.
        // This allows skipping construction of unneeded enum variant representations.
        let mut idx = expected;
        while let TypeInfoOrIdx::Idx(next) = self.types[idx.idx()] {
            idx = next;
        }
        match self[idx] {
            TypeInfo::Instance(BaseType::Invalid, _) => Err(None),
            TypeInfo::Enum(id) => {
                let variants = self.get_enum_variants(id);
                if let Some(variant) = variants
                    .iter()
                    .copied()
                    .find(|&variant| &*self[variant].name == name)
                {
                    let arg_types = self[variant].args;
                    Ok((OrdinalType::Inferred(variant), arg_types))
                } else {
                    let arg_types = self.add_multiple_unknown(arg_count + 1);
                    let variant = self.append_enum_variant(id, name.into(), arg_types);
                    Ok((OrdinalType::Inferred(variant), arg_types))
                }
            }
            TypeInfo::Unknown(bounds) if bounds.is_empty() => {
                let arg_types = self.add_multiple_unknown(arg_count + 1);
                let enum_id = self.add_enum_type();
                let variant = self.append_enum_variant(enum_id, name.into(), arg_types);
                self.replace(idx, TypeInfo::Enum(enum_id));
                Ok((OrdinalType::Inferred(variant), arg_types))
            }
            TypeInfo::Instance(id, generics) => {
                let resolved_ty = compiler.get_base_type_def(id);
                if let ResolvedTypeContent::Enum(enum_) = &resolved_ty.def {
                    let variant =
                        enum_
                            .variants
                            .iter()
                            .find_map(|(variant_name, ordinal, arg_types)| {
                                (&**variant_name == name).then_some((*ordinal, &**arg_types))
                            });
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
                                type_info_from_variant_count(enum_.variants.len() as u32),
                            );
                            for (r, &ty) in arg_type_iter.zip(arg_types.iter()) {
                                let ty = self.from_type_instance(&compiler.types, ty, generics);
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

    fn mismatched_type_error(
        &self,
        compiler: &Compiler,
        a: TypeInfo,
        b: TypeInfo,
        span: ModuleSpan,
    ) {
        let mut expected = String::new();
        self.type_to_string(compiler, a, &mut expected);
        let mut found = String::new();
        self.type_to_string(compiler, b, &mut found);
        let ModuleSpan { module, span } = span;
        compiler.errors.emit(
            module,
            Error::MismatchedType { expected, found }.at_span(span),
        );
    }

    pub fn try_specify_type_instance(
        &mut self,
        id: LocalTypeId,
        ty: Type,
        generics: LocalTypeIds,
        function_generics: &Generics,
        compiler: &Compiler,
    ) -> Result<(), (TypeInfo, TypeInfo)> {
        // PERF:could special-case this function to avoid instantiating the Type
        let resolved_info = self.from_type_instance(&compiler.types, ty, generics);
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

    pub fn from_type_instance(
        &mut self,
        types: &Types,
        ty: Type,
        generics: LocalTypeIds,
    ) -> TypeInfoOrIdx {
        if generics.is_empty() {
            return TypeInfo::Known(ty).into();
        }
        match types.lookup(ty) {
            TypeFull::Instance(base, type_generics) => {
                if type_generics.is_empty() {
                    return TypeInfo::Known(ty).into();
                }
                let type_generic_vars = self.add_multiple_unknown(type_generics.len() as _);
                for (&generic, var) in type_generics.iter().zip(type_generic_vars.iter()) {
                    let info = self.from_type_instance(types, generic, generics);
                    self.replace(var, info);
                }
                TypeInfo::Instance(base, type_generic_vars).into()
            }
            TypeFull::Generic(i) => generics.nth(u32::from(i)).unwrap().into(),
            TypeFull::Const(_) => unreachable!("consts don't have generics"),
        }
    }

    pub fn try_specify(
        &mut self,
        mut a: LocalTypeId,
        info: TypeInfo,
        function_generics: &Generics,
        compiler: &Compiler,
    ) -> Result<(), (TypeInfo, TypeInfo)> {
        let a_ty = loop {
            match self.types[a.idx()] {
                TypeInfoOrIdx::Idx(idx) => a = idx,
                TypeInfoOrIdx::TypeInfo(info) => break info,
            }
        };
        let Some(info) = unify(a_ty, info, self, function_generics, compiler, a) else {
            self.types[a.idx()] = TypeInfoOrIdx::TypeInfo(TypeInfo::INVALID);
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
                    *info = TypeInfo::INVALID;
                    break;
                }
            }
        }
    }

    pub fn display<'a>(
        &'a self,
        compiler: &'a Compiler,
        ty: LocalTypeId,
    ) -> display::TypeDisplay<'a> {
        display::TypeDisplay {
            ty,
            table: self,
            compiler,
        }
    }

    pub fn type_to_string(&self, compiler: &Compiler, ty: TypeInfo, s: &mut String) {
        use std::fmt::Write;
        // TODO: some of these types could be described better if they could look up symbols
        match ty {
            TypeInfo::Unknown(bounds) => {
                s.push_str("<unknown>");
                if !bounds.is_empty() {
                    s.push_str(": ");
                    for (i, bound) in self.get_bounds(bounds).iter().enumerate() {
                        if i != 0 {
                            s.push_str(", ");
                        }
                        s.push_str(compiler.get_trait_name(bound.trait_id.0, bound.trait_id.1));
                        if bound.generics.count != 0 {
                            s.push('[');
                            for (i, generic) in bound.generics.iter().enumerate() {
                                if i != 0 {
                                    s.push_str(", ");
                                }
                                self.type_to_string(compiler, self[generic], s);
                            }
                            s.push(']');
                        }
                    }
                }
            }
            TypeInfo::UnknownConst => s.push_str("<unknown constant>"),
            TypeInfo::Known(ty) => {
                write!(s, "{}", compiler.types.display(ty)).unwrap();
            }
            TypeInfo::Integer => s.push_str("<integer>"),
            TypeInfo::Float => s.push_str("<float>"),
            TypeInfo::Instance(base, generics) => match base {
                BaseType::Invalid => s.push_str("<invalid>"),
                BaseType::Tuple => {
                    s.push('(');
                    let mut first = true;
                    for member in generics.iter() {
                        if first {
                            first = false;
                        } else {
                            s.push_str(", ");
                        }
                        self.type_to_string(compiler, self[member], s);
                    }
                    s.push(')');
                }
                BaseType::Array => {
                    s.push('[');
                    self.type_to_string(compiler, self[generics.nth(0).unwrap()], s);
                    s.push_str("; ");
                    self.type_to_string(compiler, self[generics.nth(1).unwrap()], s);
                    s.push(']');
                }
                BaseType::Pointer => {
                    debug_assert_eq!(generics.count, 1);
                    s.push('*');
                    self.type_to_string(compiler, self[generics.nth(0).unwrap()], s);
                }
                BaseType::Function => {
                    s.push_str("fn(");
                    for (i, param) in generics.skip(1).iter().enumerate() {
                        if i != 0 {
                            s.push_str(", ");
                        }
                        self.type_to_string(compiler, self[param], s);
                    }
                    s.push_str(") -> ");
                    self.type_to_string(compiler, self[generics.nth(0).unwrap()], s);
                }
                _ => {
                    let name = &compiler.types.get_base(base).name;
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
            },
            TypeInfo::Enum(id) => self.enum_to_string(compiler, s, &self.enums[id.idx()].variants),
            TypeInfo::BaseTypeItem(base) => {
                let name = &compiler.types.get_base(base).name;
                s.push_str("<base type item: ");
                s.push_str(name);
                s.push('>');
            }
            TypeInfo::TypeItem(ty) => {
                s.push_str("<type item: ");
                self.type_to_string(compiler, self[ty], s);
                s.push('>');
            }
            TypeInfo::TraitItem { .. } => s.push_str("<trait item>"),
            TypeInfo::FunctionItem { .. } => s.push_str("<function item>"),
            TypeInfo::ModuleItem(_) => s.push_str("<module item>"),
            TypeInfo::MethodItem { .. } => s.push_str("<method item>"),
            TypeInfo::TraitMethodItem { .. } => s.push_str("<trait method item>"),
            TypeInfo::EnumVariantItem { .. } => s.push_str("<enum variant item>"),
            TypeInfo::Generic(i) => write!(s, "${i}").unwrap(),
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

    fn intern_var(
        &mut self,
        compiler: &Compiler,
        module: ModuleId,
        var: LocalTypeId,
        buf: &mut Vec<Type>,
    ) -> Type {
        let mut idx = var;
        let info = loop {
            match self.types[idx.0 as usize] {
                TypeInfoOrIdx::TypeInfo(info) => break info,
                TypeInfoOrIdx::Idx(new) => idx = new,
            }
        };
        let ty = match info {
            TypeInfo::Unknown(bounds) => {
                if let Some(first_bound) = bounds.iter().next() {
                    let bound = &self.bounds[first_bound.0 as usize];
                    let name = compiler
                        .get_trait_name(bound.trait_id.0, bound.trait_id.1)
                        .to_owned();
                    compiler.errors.emit(
                        module,
                        Error::TypeMustBeKnownHere {
                            needed_bound: Some(name),
                        }
                        .at_span(bound.span),
                    );
                    Type::Invalid
                } else {
                    Type::Unit
                }
            }
            TypeInfo::UnknownConst => {
                compiler.errors.emit(
                    module,
                    Error::TypeMustBeKnownHere {
                        needed_bound: Some("const".into()),
                    }
                    .at_span(TSpan::MISSING), // TODO: span of UnknownConst
                );
                Type::Invalid
            }
            TypeInfo::Known(ty) => ty,
            TypeInfo::Integer => Type::I32,
            TypeInfo::Float => Type::F32,
            TypeInfo::Instance(base, type_generics) => {
                let start = buf.len();
                buf.reserve(type_generics.count as usize);
                for i in type_generics.iter() {
                    let generic = self.intern_var(compiler, module, i, buf);
                    buf.push(generic);
                }
                debug_assert_eq!(buf[start..].len(), type_generics.count as usize);
                let ty = compiler
                    .types
                    .intern(TypeFull::Instance(base, &buf[start..]));
                buf.truncate(start);
                ty
            }
            TypeInfo::Enum(id) => {
                // PERF: also buffer variants? and params somehow?
                let mut variants = Vec::new();
                for variant_idx in 0..self.enums[id.idx()].variants.len() {
                    let variant = &self.variants[self.enums[id.idx()].variants[variant_idx].idx()];
                    let name = variant.name.clone();
                    let ordinal = variant.ordinal;
                    let params = variant
                        .args
                        .iter()
                        .map(|param| self.intern_var(compiler, module, param, buf))
                        .collect();
                    variants.push((name, ordinal, params));
                }
                // TODO: better, unique names for local_enum types
                let base = compiler.types.add_resolved_base(
                    module,
                    ast::TypeId::MISSING,
                    "local_enum".into(),
                    0,
                    ResolvedTypeDef {
                        def: ResolvedTypeContent::Enum(ResolvedEnumDef {
                            variants: variants.into_boxed_slice(),
                        }),
                        module,
                        methods: DHashMap::default(),
                        generics: Generics::EMPTY,
                        inherent_trait_impls: DHashMap::default(),
                    },
                );
                compiler.types.intern(TypeFull::Instance(base, &[]))
            }
            TypeInfo::BaseTypeItem(_)
            | TypeInfo::TypeItem(_)
            | TypeInfo::TraitItem { .. }
            | TypeInfo::FunctionItem { .. }
            | TypeInfo::ModuleItem(_)
            | TypeInfo::MethodItem { .. }
            | TypeInfo::TraitMethodItem { .. }
            | TypeInfo::EnumVariantItem { .. } => Type::Invalid, // TODO: what to return here?
            TypeInfo::Generic(i) => compiler.types.intern(TypeFull::Generic(i)),
        };
        self.types[idx.idx()] = TypeInfo::Known(ty).into();
        ty
    }

    pub fn finish(
        mut self,
        compiler: &Compiler,
        function_generics: &Generics,
        module: ModuleId,
    ) -> (Box<[Type]>, Box<[InferredEnumVariant]>) {
        for (ty, bounds) in std::mem::take(&mut self.deferred_checks) {
            let mut idx = ty;
            let info = loop {
                match self.types[idx.0 as usize] {
                    TypeInfoOrIdx::Idx(new_idx) => idx = new_idx,
                    TypeInfoOrIdx::TypeInfo(info) => break info,
                }
            };
            if info.is_invalid() {
                continue;
            }
            for bound in bounds.iter() {
                let bound = self.bounds[bound.0 as usize];
                let span = bound.span;
                let Some(checked_trait) =
                    compiler.get_checked_trait(bound.trait_id.0, bound.trait_id.1)
                else {
                    continue;
                };
                // TODO: probably should retry impl candidates in a loop as long as one bound has
                // multiple candidates but progress is made
                match traits::get_impl_candidates(
                    compiler,
                    &bound,
                    info,
                    &mut self,
                    function_generics,
                ) {
                    traits::Candidates::Invalid => {
                        continue;
                    }
                    traits::Candidates::None => {
                        let trait_name = checked_trait.name.clone();
                        let mut type_name = String::new();
                        self.type_to_string(compiler, info, &mut type_name);
                        compiler.errors.emit(
                            module,
                            Error::UnsatisfiedTraitBound {
                                trait_name,
                                ty: type_name,
                            }
                            .at_span(span),
                        );
                        self.types[idx.0 as usize] = TypeInfoOrIdx::TypeInfo(TypeInfo::INVALID);
                    }
                    traits::Candidates::Unique { instance } => {
                        let span = || ModuleSpan { module, span };
                        match instance {
                            TypeInfoOrIdx::TypeInfo(info) => {
                                self.specify(ty, info, function_generics, compiler, span)
                            }
                            TypeInfoOrIdx::Idx(self_idx) => {
                                self.unify(idx, self_idx, function_generics, compiler, span)
                            }
                        }
                    }
                    traits::Candidates::Multiple => {
                        let name = checked_trait.name.clone();
                        let retry_with = match info {
                            TypeInfo::Integer => Some(Primitive::I32.into()),
                            TypeInfo::Float => Some(Primitive::F32.into()),
                            _ => None,
                        };
                        let new_candidate = retry_with.and_then(|new_info| {
                            let new_candidates = traits::get_impl_candidates(
                                compiler,
                                &bound,
                                new_info,
                                &mut self,
                                function_generics,
                            );
                            if let traits::Candidates::Unique { instance: _ } = new_candidates {
                                Some(new_info)
                            } else {
                                None
                            }
                        });
                        if let Some(new_info) = new_candidate {
                            self.replace(idx, new_info);
                        } else {
                            compiler.errors.emit(
                                module,
                                Error::TypeAnnotationNeeded {
                                    bound: name, // TODO: should also show generics here
                                }
                                .at_span(span),
                            );
                            self.types[idx.0 as usize] = TypeInfoOrIdx::TypeInfo(TypeInfo::INVALID);
                        }
                    }
                }
            }
        }
        let mut buf = Vec::new();
        let types = (0..self.types.len() as u32)
            .map(|i| self.intern_var(compiler, module, LocalTypeId(i), &mut buf))
            .collect();
        (types, self.variants.into_boxed_slice())
    }

    fn unify_with_generic_type(
        &mut self,
        var: LocalTypeId,
        ty: Type,
        compiler: &Compiler,
        function_generics: &Generics,
    ) -> Result<bool, InvalidTypeError> {
        let (idx, info) = self.find_shorten(var);
        match self.specify_generic_type(info, ty, compiler, function_generics) {
            Ok(true) => {
                debug_assert!(matches!(
                    self.types[idx.0 as usize],
                    TypeInfoOrIdx::TypeInfo(_),
                ));
                self.types[idx.0 as usize] = TypeInfoOrIdx::TypeInfo(TypeInfo::Known(ty));
                Ok(true)
            }
            Ok(false) => Ok(false),
            Err(InvalidTypeError) => {
                self.types[idx.0 as usize] =
                    TypeInfoOrIdx::TypeInfo(TypeInfo::Known(Type::Invalid));
                Err(InvalidTypeError)
            }
        }
    }

    fn specify_generic_type(
        &mut self,
        info: TypeInfo,
        ty: Type,
        compiler: &Compiler,
        function_generics: &Generics,
    ) -> Result<bool, InvalidTypeError> {
        if let TypeInfo::Known(other_ty) = info {
            return Ok(ty == other_ty);
        }
        Ok(match compiler.types.lookup(ty) {
            TypeFull::Instance(BaseType::Invalid, _) => return Err(InvalidTypeError),
            TypeFull::Instance(base, instance) => match info {
                TypeInfo::Unknown(bounds) => {
                    for bound in bounds.iter() {
                        let bound = *self.get_bound(bound);
                        if !self.unify_bound_with_type(ty, bound, compiler)? {
                            return Ok(false);
                        }
                    }
                    true
                }
                TypeInfo::Integer if base.is_int() => true,
                TypeInfo::Float if base.is_float() => true,
                TypeInfo::Enum(_id) => todo!("unify inferred enums with known"),
                TypeInfo::Instance(info_base, info_instance)
                    if base == info_base && instance.len() as u32 == info_instance.count =>
                {
                    instance
                        .iter()
                        .zip(info_instance.iter())
                        .try_all(|(&ty, info)| {
                            self.unify_with_generic_type(info, ty, compiler, function_generics)
                        })?
                }
                _ => false,
            },
            TypeFull::Generic(i) => match info {
                TypeInfo::Unknown(_) => true,
                TypeInfo::Generic(j) if i == j => true,
                _ => false,
            },
            TypeFull::Const(_) => matches!(info, TypeInfo::UnknownConst),
        })
    }

    fn unify_bound_with_type(
        &mut self,
        ty: Type,
        bound: Bound,
        compiler: &Compiler,
    ) -> Result<bool, InvalidTypeError> {
        let mut has_invalid_type = false;
        let candidates =
            compiler.get_impl(
                bound.trait_id,
                ty,
                bound.generics.iter(),
                |var, ty| match self.compatible_with_type(&compiler.types, self[var], ty) {
                    Ok(b) => b,
                    Err(InvalidTypeError) => {
                        has_invalid_type = true;
                        false
                    }
                },
            );
        if has_invalid_type {
            return Err(InvalidTypeError);
        }
        match candidates {
            traits::Candidates::None => Ok(false),
            traits::Candidates::Invalid => Err(InvalidTypeError),
            traits::Candidates::Multiple => Ok(true),
            traits::Candidates::Unique {
                instance: ((_, impl_), impl_generics),
            } => {
                let impl_generics =
                    self.add_multiple(impl_generics.into_iter().map(TypeInfo::Known));
                for (var, &ty) in bound.generics.iter().zip(&impl_.trait_generics) {
                    let (var, _) = self.find_shorten(var);
                    let ty = self.from_type_instance(&compiler.types, ty, impl_generics);
                    self.replace(var, ty);
                }
                Ok(true)
            }
        }
    }

    pub fn is_uninhabited(
        &mut self,
        compiler: &Compiler,
        info: TypeInfo,
    ) -> Result<bool, InvalidTypeError> {
        Ok(match info {
            TypeInfo::Unknown(_) | TypeInfo::Generic(_) | TypeInfo::Integer | TypeInfo::Float => {
                false
            }
            TypeInfo::Known(ty) => compiler.is_uninhabited(ty, &Instance::EMPTY)?,
            TypeInfo::Instance(BaseType::Invalid, _) => return Err(InvalidTypeError),
            TypeInfo::Instance(base, instance) => match &compiler.get_base_type_def(base).def {
                ResolvedTypeContent::Builtin(_) => false,
                ResolvedTypeContent::Struct(def) => def.all_fields().try_any(|(_, ty)| {
                    let ty = self.from_type_instance(&compiler.types, ty, instance);
                    self.is_uninhabited(compiler, self.get_info_or_idx(ty))
                })?,
                ResolvedTypeContent::Enum(def) => def.variants.iter().try_all(|(_, _, args)| {
                    args.iter().try_any(|&ty| {
                        let ty = self.from_type_instance(&compiler.types, ty, instance);
                        self.is_uninhabited(compiler, self.get_info_or_idx(ty))
                    })
                })?,
            },
            TypeInfo::Enum(id) => (0..self.get_enum_variants(id).len()).try_all(|i| {
                let variant = self.get_enum_variants(id)[i];
                self[variant]
                    .args
                    .iter()
                    .try_any(|ty| self.is_uninhabited(compiler, self[ty]))
            })?,
            TypeInfo::BaseTypeItem(_)
            | TypeInfo::TypeItem(_)
            | TypeInfo::TraitItem { .. }
            | TypeInfo::FunctionItem { .. }
            | TypeInfo::ModuleItem(_)
            | TypeInfo::MethodItem { .. }
            | TypeInfo::TraitMethodItem { .. }
            | TypeInfo::EnumVariantItem { .. } => false,
            TypeInfo::UnknownConst => unreachable!(),
        })
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

    pub fn is_empty(self) -> bool {
        self.count == 0
    }

    pub fn iter(self) -> impl Clone + ExactSizeIterator<Item = LocalTypeId> {
        (self.idx..self.idx + self.count).map(LocalTypeId)
    }

    pub fn nth(self, i: u32) -> Option<LocalTypeId> {
        (i < self.count).then_some(LocalTypeId(self.idx + i))
    }

    pub fn skip(&self, n: u32) -> Self {
        Self {
            idx: self.idx + n,
            count: self.count - n,
        }
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
    pub const EMPTY: Self = Self { start: 0, count: 0 };

    pub fn iter(self) -> impl ExactSizeIterator<Item = BoundId> {
        (self.start..self.start + self.count).map(BoundId)
    }

    pub fn is_empty(&self) -> bool {
        self.count == 0
    }
}

#[derive(Debug, Clone, Copy)]
pub struct BoundId(u32);

#[derive(Debug, Clone, Copy)]
pub enum TypeInfo {
    Unknown(Bounds),
    UnknownConst, // TODO: typed consts
    Known(Type),
    Integer,
    Float,
    Instance(BaseType, LocalTypeIds),
    Enum(InferredEnumId),
    BaseTypeItem(BaseType),
    TypeItem(LocalTypeId),
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
        enum_type: BaseType,
        generics: LocalTypeIds,
        ordinal: u64,
        /// always includes the ordinal type as it's first type
        arg_types: LocalTypeIds,
    },
    Generic(u8),
}
impl From<Primitive> for TypeInfo {
    fn from(value: Primitive) -> Self {
        TypeInfo::Known(value.into())
    }
}
impl TypeInfo {
    pub const INVALID: Self = Self::Known(Type::Invalid);
    pub const UNIT: Self = Self::Instance(BaseType::Tuple, LocalTypeIds::EMPTY);

    pub fn is_invalid(&self) -> bool {
        matches!(
            self,
            Self::Instance(BaseType::Invalid, _) | Self::Known(Type::Invalid)
        )
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
    pub ordinal: u64,
    pub args: LocalTypeIds,
}

#[derive(Debug, Clone, Copy)]
pub enum OrdinalType {
    Inferred(VariantId),
    Known(u64),
}

impl Compiler {
    pub fn resolved_layout(
        &self,
        ty: Type,
        generics: Instance,
    ) -> Result<Layout, InvalidTypeError> {
        Ok(match ty {
            Type::Invalid => return Err(InvalidTypeError),
            Type::Unit => Layout::EMPTY,
            Type::I8 | Type::U8 => Layout {
                size: 1,
                alignment: 1,
            },
            Type::I16 | Type::U16 => Layout {
                size: 2,
                alignment: 2,
            },
            Type::I32 | Type::U32 | Type::F32 => Layout {
                size: 4,
                alignment: 4,
            },
            Type::I64 | Type::U64 | Type::F64 => Layout {
                size: 8,
                alignment: 8,
            },
            Type::I128 | Type::U128 => Layout {
                size: 8,
                alignment: 8,
            },
            Type::Type => Layout::EMPTY,
            ty => match self.types.lookup(ty) {
                TypeFull::Instance(BaseType::Tuple, elems) => {
                    let mut layout = Layout::EMPTY;
                    for &elem in elems {
                        layout.accumulate(self.resolved_layout(elem, generics)?);
                    }
                    layout
                }
                TypeFull::Instance(BaseType::Array, array) => {
                    let elem = array[0];
                    let TypeFull::Const(n) = self.types.lookup(array[1]) else {
                        debug_assert_eq!(array[1], Type::Invalid);
                        return Err(InvalidTypeError);
                    };
                    Layout::array(self.resolved_layout(elem, generics)?, n)
                }
                TypeFull::Instance(BaseType::Pointer | BaseType::Function, _) => Layout::PTR,
                TypeFull::Instance(base, type_generics) => {
                    let def = self.get_base_type_def(base);
                    match &def.def {
                        ResolvedTypeContent::Builtin(_) => unreachable!(),
                        ResolvedTypeContent::Struct(def) => {
                            let mut layout = Layout::EMPTY;
                            for (_, field) in def.all_fields() {
                                layout.accumulate(self.resolved_layout(
                                    field,
                                    Instance {
                                        types: type_generics,
                                        outer: Some(&generics),
                                    },
                                )?);
                            }
                            layout
                        }
                        ResolvedTypeContent::Enum(def) => {
                            let instance = Instance {
                                types: type_generics,
                                outer: Some(&generics),
                            };
                            let variant_count = def
                                .variants
                                .iter()
                                .filter(|(_, _, args)| {
                                    args.iter().all(|&arg| {
                                        !self.is_uninhabited(arg, &instance).is_ok_and(|b| b)
                                    })
                                })
                                .count() as u32;
                            let ordinal_layout = self.resolved_layout(
                                type_from_variant_count(variant_count),
                                Instance::EMPTY,
                            )?;
                            let mut layout = ordinal_layout;
                            for (_, _, args) in &def.variants {
                                if args.iter().any(|&arg| {
                                    self.is_uninhabited(arg, &instance).is_ok_and(|b| b)
                                }) {
                                    continue;
                                }
                                let mut variant_layout = ordinal_layout;
                                for &arg in args {
                                    variant_layout.accumulate(self.resolved_layout(arg, generics)?);
                                }
                                layout.add_variant(variant_layout);
                            }
                            layout
                        }
                    }
                }
                TypeFull::Generic(i) => self.resolved_layout(generics[i], generics.outer())?,
                TypeFull::Const(_) => Layout::EMPTY,
            },
        })
    }
}
