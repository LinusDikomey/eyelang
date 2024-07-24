mod cast;
mod exhaust;
pub mod expr;
mod lval;
mod pattern;
pub mod traits;

pub use traits::check_trait;

use id::ModuleId;
use span::TSpan;
use types::{Primitive, Type};

use crate::{
    compiler::{Generics, Signature},
    error::{CompileError, Error},
    hir::{CastId, HIRBuilder, Node, HIR},
    parser::ast::{Ast, ExprId, ScopeId},
    types::{LocalTypeId, LocalTypeIds, TypeInfo, TypeInfoOrIdx, TypeTable},
    Compiler,
};

use self::exhaust::Exhaustion;

pub fn check(
    compiler: &mut Compiler,
    ast: &Ast,
    module: ModuleId,
    types: TypeTable,
    generics: &Generics,
    scope: ScopeId,
    args: impl IntoIterator<Item = (String, LocalTypeId)>,
    expr: ExprId,
    expected: LocalTypeId,
) -> (HIR, TypeTable) {
    let mut hir = HIRBuilder::new(types);
    let variables = args
        .into_iter()
        .map(|(name, ty)| (name, hir.add_var(ty)))
        .collect();
    let mut scope = crate::compiler::LocalScope {
        parent: None,
        variables,
        module,
        static_scope: Some(scope),
    };
    let mut check_ctx = Ctx {
        compiler,
        ast,
        module,
        generics,
        hir,
        deferred_exhaustions: Vec::new(),
        deferred_casts: Vec::new(),
    };
    let root = expr::check(
        &mut check_ctx,
        expr,
        &mut scope,
        expected,
        expected,
        &mut false,
    );
    let (hir, types) = check_ctx.finish(root);
    (hir, types)
}

pub struct Ctx<'a> {
    pub compiler: &'a mut Compiler,
    pub ast: &'a Ast,
    pub module: ModuleId,
    pub generics: &'a Generics,
    pub hir: HIRBuilder,
    /// Exhaustion value, type, pattern expr
    pub deferred_exhaustions: Vec<(Exhaustion, LocalTypeId, ExprId)>,
    /// from, to, cast_expr
    pub deferred_casts: Vec<(LocalTypeId, LocalTypeId, ExprId, CastId)>,
}
impl<'a> Ctx<'a> {
    fn span(&self, expr: ExprId) -> span::Span {
        self.ast[expr].span_in(self.ast, self.module)
    }

    fn specify(
        &mut self,
        ty: LocalTypeId,
        info: impl Into<TypeInfo>,
        span: impl FnOnce(&Ast) -> TSpan,
    ) {
        self.hir
            .types
            .specify(ty, info.into(), self.generics, self.compiler, || {
                span(self.ast).in_mod(self.module)
            })
    }

    fn specify_resolved(
        &mut self,
        ty: LocalTypeId,
        resolved: &Type,
        generics: LocalTypeIds,
        span: impl FnOnce(&Ast) -> TSpan,
    ) {
        // PERF:could special-case this function to avoid instantiating the Type
        let func_return_ty = self.type_from_resolved(resolved, generics);
        match func_return_ty {
            TypeInfoOrIdx::TypeInfo(info) => self.specify(ty, info, span),
            TypeInfoOrIdx::Idx(idx) => self.unify(ty, idx, span),
        }
    }

    fn unify(&mut self, a: LocalTypeId, b: LocalTypeId, span: impl FnOnce(&Ast) -> TSpan) {
        self.hir
            .types
            .unify(a, b, self.generics, self.compiler, || {
                span(self.ast).in_mod(self.module)
            })
    }

    fn invalidate(&mut self, ty: LocalTypeId) {
        self.hir.types.invalidate(ty);
    }

    pub fn type_from_resolved(&mut self, ty: &Type, generics: LocalTypeIds) -> TypeInfoOrIdx {
        self.hir
            .types
            .from_generic_resolved(self.compiler, ty, generics)
    }

    pub fn types_from_resolved<'t>(
        &mut self,
        types: impl ExactSizeIterator<Item = &'t Type>,
        generics: LocalTypeIds,
    ) -> LocalTypeIds {
        let hir_types = self.hir.types.add_multiple_unknown(types.len() as u32);
        for (r, ty) in hir_types.iter().zip(types) {
            let ty = self.type_from_resolved(&ty, generics);
            self.hir.types.replace(r, ty);
        }
        hir_types
    }

    fn auto_ref_deref(
        &mut self,
        mut pointer_count: u32,
        required_pointer_count: u32,
        mut value: Node,
        ty: LocalTypeId,
    ) -> Node {
        let mut current_ty = TypeInfoOrIdx::Idx(ty);
        while pointer_count < required_pointer_count {
            let inner = self.hir.add(value);
            let value_ty = self.hir.types.add_info_or_idx(current_ty);
            value = Node::AddressOf { inner, value_ty };
            current_ty = TypeInfoOrIdx::TypeInfo(TypeInfo::Pointer(value_ty));
            pointer_count += 1;
        }
        while pointer_count > required_pointer_count {
            let TypeInfo::Pointer(pointee) = self.hir.types.get_info_or_idx(current_ty) else {
                // the deref was already checked so we know the type is wrapped in
                // `pointer_count` pointers
                unreachable!()
            };
            let prev_value = self.hir.add(value);
            value = Node::Deref {
                value: prev_value,
                deref_ty: pointee,
            };
            current_ty = TypeInfoOrIdx::Idx(pointee);
            pointer_count -= 1;
        }
        value
    }

    pub(crate) fn finish(self, root: Node) -> (HIR, TypeTable) {
        let (mut hir, types) = self
            .hir
            .finish(root, self.compiler, self.generics, self.module);
        for (exhaustion, ty, pat) in self.deferred_exhaustions {
            if let Some(false) = exhaustion.is_exhausted(types[ty], &types, self.compiler) {
                let error =
                    Error::Inexhaustive.at_span(self.ast[pat].span_in(&self.ast, self.module));
                self.compiler.errors.emit_err(error)
            }
        }
        for (from_ty, to_ty, cast_expr, cast_id) in self.deferred_casts {
            let (cast, err) = cast::check(from_ty, to_ty, self.compiler, &types);
            hir[cast_id].cast_ty = cast;
            if let Some(err) = err {
                self.compiler
                    .errors
                    .emit_err(err.at_span(self.ast[cast_expr].span_in(self.ast, self.module)));
            }
        }
        (hir, types)
    }
}

pub fn verify_main_signature(
    signature: &Signature,
    main_module: ModuleId,
) -> Result<(), Option<CompileError>> {
    if signature.args.len() != 0 || signature.varargs {
        return Err(Some(
            Error::MainArgs.at_span(signature.span.in_mod(main_module)),
        ));
    }
    if signature.generics.count() != 0 {
        return Err(Some(
            Error::MainGenerics.at_span(signature.span.in_mod(main_module)),
        ));
    }
    match &signature.return_type {
        Type::Invalid => return Err(None),
        Type::Primitive(p) if p.is_int() | matches!(p, Primitive::Unit) => Ok(()),
        ty => {
            return Err(Some(
                Error::InvalidMainReturnType(ty.to_string())
                    .at_span(signature.span.in_mod(main_module)),
            ))
        }
    }
}

fn get_string_literal(src: &str, span: TSpan) -> Box<str> {
    let inp = &src[span.start as usize + 1..span.end as usize];
    let mut out = String::with_capacity(inp.len());
    let mut saw_backslash = false;
    for c in inp.chars() {
        if saw_backslash {
            let c = match c {
                '\\' => '\\',
                'n' => '\n',
                't' => '\t',
                'r' => '\r',
                '0' => '\0',
                '\"' => '\"',
                _ => unreachable!("invalid escape should have been caught in parser"),
            };
            out.push(c);
            saw_backslash = false;
        } else if c == '\\' {
            saw_backslash = true;
        } else {
            out.push(c);
        }
    }
    out.into_boxed_str()
}
