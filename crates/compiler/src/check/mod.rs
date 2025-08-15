mod call;
mod cast;
mod closure;
mod exhaust;
pub mod expr;
mod lval;
mod pattern;
pub mod traits;
mod type_def;

use std::rc::Rc;

use error::{CompileError, Error, Errors, span::TSpan};
use parser::ast::{Ast, ExprId, ModuleId, ScopeId};
pub use traits::trait_def;
pub use type_def::type_def;

use crate::{
    Compiler, Type,
    compiler::{
        CheckedFunction, Generics, LocalScopeParent, ModuleSpan, Resolvable, Signature, VarId,
        builtins,
    },
    hir::{CastId, HIRBuilder, Hir, LValue, Node, NodeId},
    typing::{LocalTypeId, LocalTypeIds, TypeInfo, TypeInfoOrIdx, TypeTable},
};

use self::exhaust::Exhaustion;

pub(crate) fn function(
    compiler: &mut Compiler,
    module: ModuleId,
    id: parser::ast::FunctionId,
) -> crate::compiler::CheckedFunction {
    let resolving = &mut compiler.modules[module.idx()]
        .ast
        .as_mut()
        .unwrap()
        .symbols
        .functions[id.idx()];
    *resolving = Resolvable::Resolving;
    let ast = compiler.modules[module.idx()]
        .ast
        .as_ref()
        .unwrap()
        .ast
        .clone();

    let function = &ast[id];

    compiler.get_signature(module, id);
    // signature is resolved above
    let Resolvable::Resolved(signature) = &compiler.modules[module.idx()]
        .ast
        .as_ref()
        .unwrap()
        .symbols
        .function_signatures[id.idx()]
    else {
        unreachable!()
    };

    let signature = Rc::clone(signature);

    let mut types = TypeTable::new();

    let param_types = types.add_multiple_unknown(signature.total_arg_count() as u32);
    for ((_, param), r) in signature.all_params().zip(param_types.iter()) {
        let i = TypeInfoOrIdx::TypeInfo(types.generic_info_from_resolved(param));
        types.replace(r, i);
    }

    let return_type = types.generic_info_from_resolved(&signature.return_type);
    let return_type = types.add(return_type);

    let generic_count = signature.generics.count();
    let varargs = signature.varargs;

    let (body, types) = if let Some(body) = function.body {
        let hir = HIRBuilder::new(types);
        let params = signature
            .all_params()
            .zip(param_types.iter())
            .map(|((name, _), id)| (name.into(), id));

        let (hir, types) = check(
            compiler,
            &ast,
            module,
            &signature.generics,
            function.scope,
            hir,
            params,
            body,
            return_type,
            LocalScopeParent::None,
        );
        (Some(hir), types)
    } else {
        (None, types)
    };

    // TODO: factor potential closed_over_scope into name
    let name = crate::compiler::function_name(&ast, function, module, id);

    CheckedFunction {
        name,
        types,
        params: param_types,
        varargs,
        return_type,
        generic_count,
        body,
    }
}

pub fn check(
    compiler: &mut Compiler,
    ast: &Ast,
    module: ModuleId,
    generics: &Generics,
    scope: ScopeId,
    mut hir: HIRBuilder,
    params: impl IntoIterator<Item = (Box<str>, LocalTypeId)>,
    expr: ExprId,
    expected: LocalTypeId,
    parent_scope: LocalScopeParent,
) -> (Hir, TypeTable) {
    let params = params.into_iter();
    let mut param_vars = Vec::with_capacity(params.size_hint().0);
    let variables = params
        .map(|(name, ty)| {
            let var = hir.add_var(ty);
            param_vars.push(var);
            (name, var)
        })
        .collect();

    let mut scope = crate::compiler::LocalScope {
        parent: parent_scope,
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
        control_flow_stack: Vec::new(),
        deferred_exhaustions: Vec::new(),
        deferred_casts: Vec::new(),
        capture_elements_to_replace: Vec::new(),
    };
    let root = expr::check(
        &mut check_ctx,
        expr,
        &mut scope,
        expected,
        expected,
        &mut false,
    );
    debug_assert!(
        check_ctx.capture_elements_to_replace.is_empty(),
        "non-closure tried to capture something"
    );
    let (hir, types) = check_ctx.finish(root, param_vars);
    (hir, types)
}

pub struct ProjectErrors {
    pub by_file: dmap::DHashMap<ModuleId, Errors>,
    crash_on_error: bool,
}
impl ProjectErrors {
    #[track_caller]
    pub fn emit(&mut self, module: ModuleId, error: CompileError) {
        if self.crash_on_error {
            panic!(
                "Error encountered and --crash-on-error is enabled. The error is: {error:?} in {module:?}"
            );
        }
        self.by_file.entry(module).or_default().emit_err(error);
    }

    pub fn enable_crash_on_error(&mut self) {
        self.crash_on_error = true;
    }

    pub fn new() -> Self {
        Self {
            by_file: dmap::new(),
            crash_on_error: false,
        }
    }

    pub fn add_module(&mut self, module: ModuleId, errors: Errors) {
        let previous = self.by_file.insert(module, errors);
        debug_assert!(previous.is_none(), "Duplicate module inserted into errors");
    }
}

pub struct Ctx<'a> {
    pub compiler: &'a mut Compiler,
    pub ast: &'a Ast,
    pub module: ModuleId,
    pub generics: &'a Generics,
    pub hir: HIRBuilder,
    /// tracks a stack of any control flow that break/continue apply to (loops)
    /// labels will make the Vec actually useful to track labeled break/continue
    pub control_flow_stack: Vec<()>,
    /// Exhaustion value, type, pattern expr
    pub deferred_exhaustions: Vec<(Exhaustion, LocalTypeId, ExprId)>,
    /// from, to, cast_expr
    pub deferred_casts: Vec<(LocalTypeId, LocalTypeId, ExprId, CastId)>,
    pub capture_elements_to_replace: Vec<NodeId>,
}
impl Ctx<'_> {
    fn emit(&mut self, error: CompileError) {
        self.compiler.errors.emit(self.module, error);
    }

    fn primitives(&self) -> &builtins::Primitives {
        &self.compiler.builtins.primitives
    }

    fn span(&self, expr: ExprId) -> TSpan {
        self.ast[expr].span(self.ast)
    }

    fn specify(
        &mut self,
        ty: LocalTypeId,
        info: impl Into<TypeInfo>,
        span: impl FnOnce(&Ast) -> TSpan,
    ) {
        let info = info.into();
        self.hir
            .types
            .specify(ty, info, self.generics, self.compiler, || ModuleSpan {
                module: self.module,
                span: span(self.ast),
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
            .unify(a, b, self.generics, self.compiler, || ModuleSpan {
                module: self.module,
                span: span(self.ast),
            })
    }

    fn invalidate(&mut self, ty: LocalTypeId) {
        self.hir.types.invalidate(ty);
    }

    pub fn type_from_resolved(&mut self, ty: &Type, generics: LocalTypeIds) -> TypeInfoOrIdx {
        self.hir.types.from_generic_resolved(ty, generics)
    }

    pub fn types_from_resolved<'t>(
        &mut self,
        types: impl ExactSizeIterator<Item = &'t Type>,
        generics: LocalTypeIds,
    ) -> LocalTypeIds {
        let hir_types = self.hir.types.add_multiple_unknown(types.len() as u32);
        for (r, ty) in hir_types.iter().zip(types) {
            let ty = self.type_from_resolved(ty, generics);
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
        // try promoting the value to an lvalue first to potentially add one level of pointer
        if pointer_count < required_pointer_count
            && let Some(lval) = LValue::try_from_node(&value, &mut self.hir)
        {
            let value_ty = self.hir.types.add_info_or_idx(current_ty);
            value = Node::AddressOf {
                value: self.hir.add_lvalue(lval),
                value_ty,
            };
            current_ty = TypeInfoOrIdx::TypeInfo(TypeInfo::Pointer(value_ty));
            pointer_count += 1
        }
        while pointer_count < required_pointer_count {
            let value_ty = self.hir.types.add_info_or_idx(current_ty);
            let variable = self.hir.add_var(value_ty);
            value = Node::Promote {
                value: self.hir.add(value),
                variable,
            };
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

    pub(crate) fn finish(self, root: Node, params: Vec<VarId>) -> (Hir, TypeTable) {
        let (mut hir, types) =
            self.hir
                .finish(root, self.compiler, self.generics, self.module, params);
        for (exhaustion, ty, pat) in self.deferred_exhaustions {
            if let Some(false) = exhaustion.is_exhausted(types[ty], &types, self.compiler) {
                let error = Error::Inexhaustive.at_span(self.ast[pat].span(self.ast));
                self.compiler.errors.emit(self.module, error);
            }
        }
        for (from_ty, to_ty, cast_expr, cast_id) in self.deferred_casts {
            let (cast, err) = cast::check(from_ty, to_ty, self.compiler, &types);
            hir[cast_id].cast_ty = cast;
            if let Some(err) = err {
                self.compiler
                    .errors
                    .emit(self.module, err.at_span(self.ast[cast_expr].span(self.ast)));
            }
        }
        (hir, types)
    }
}

pub fn verify_main_signature(signature: &Signature) -> Result<(), Option<CompileError>> {
    if !signature.params.is_empty() || signature.varargs {
        return Err(Some(Error::MainArgs.at_span(signature.span)));
    }
    if signature.generics.count() != 0 {
        return Err(Some(Error::MainGenerics.at_span(signature.span)));
    }
    match &signature.return_type {
        Type::Invalid => Err(None),
        Type::Tuple(elems) if elems.is_empty() => Ok(()),
        Type::Primitive(p) if p.is_int() => Ok(()),
        ty => Err(Some(
            Error::InvalidMainReturnType(ty.to_string()).at_span(signature.span),
        )),
    }
}

fn get_string_literal(src: &str, span: TSpan) -> Box<str> {
    let inp = &src[span.start as usize + 1..span.end as usize - 1];
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
