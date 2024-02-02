mod cast;
mod exhaust;
pub mod expr;
mod lval;
mod pattern;

use id::ModuleId;
use span::TSpan;
use types::{Primitive, Type};

use crate::{
    Compiler,
    parser::ast::{Ast, ExprId},
    compiler::Signature,
    type_table::{TypeInfo, LocalTypeId, TypeTable, LocalTypeIds, TypeInfoOrIdx},
    hir::{HIRBuilder, Node, HIR, CastId}, error::{Error, CompileError},
};

use self::exhaust::Exhaustion;

pub struct Ctx<'a> {
    pub compiler: &'a mut Compiler,
    pub ast: &'a Ast,
    pub module: ModuleId,
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

    fn specify(&mut self, ty: LocalTypeId, info: impl Into<TypeInfo>, span: impl FnOnce(&Ast) -> TSpan) {
        self.hir.types.specify(
            ty,
            info.into(),
            &mut self.compiler.errors,
            || span(self.ast).in_mod(self.module),
        )
    }

    fn unify(&mut self, a: LocalTypeId, b: LocalTypeId, span: impl FnOnce(&Ast) -> TSpan) {
        self.hir.types.unify(a, b, &mut self.compiler.errors, || span(self.ast).in_mod(self.module))
    }

    fn invalidate(&mut self, ty: LocalTypeId) {
        self.hir.types.invalidate(ty);
    }

    fn type_from_resolved(&mut self, ty: &Type, generics: LocalTypeIds) -> TypeInfoOrIdx {
        self.hir.types.from_generic_resolved(self.compiler, ty, generics)
    }

    pub(crate) fn finish(self, root: Node) -> (HIR, TypeTable) {
        // TODO: finalize types?
        let (mut hir, types) = self.hir.finish(root);
        for (exhaustion, ty, pat) in self.deferred_exhaustions {
            if let Some(false) = exhaustion.is_exhausted(types[ty], &types, self.compiler) {
                let error = Error::Inexhaustive.at_span(self.ast[pat].span_in(&self.ast, self.module));
                self.compiler.errors.emit_err(error)
            }
        }
        for (from_ty, to_ty, cast_expr, cast_id) in self.deferred_casts {
            let (cast, err) = cast::check(from_ty, to_ty, &types);
            hir[cast_id].cast_ty = cast;
            if let Some(err) = err {
                self.compiler.errors.emit_err(err.at_span(self.ast[cast_expr].span_in(self.ast, self.module)));
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
        return Err(Some(Error::MainArgs.at_span(signature.span.in_mod(main_module))));
    }
    if !signature.generics.is_empty() {
        return Err(Some(Error::MainGenerics.at_span(signature.span.in_mod(main_module))));
    }
    match &signature.return_type {
        Type::Invalid => return Err(None),
        Type::Primitive(p) if p.is_int() | matches!(p, Primitive::Unit) => Ok(()),
        ty => return Err(Some(
            Error::InvalidMainReturnType(ty.to_string())
                .at_span(signature.span.in_mod(main_module))
        )),
    }
}
