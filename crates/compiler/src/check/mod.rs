mod call;
mod cast;
mod closure;
mod exhaust;
pub mod expr;
mod lval;
mod pattern;
pub mod traits;
mod type_def;

use std::cell::RefCell;

use dmap::DHashMap;
use error::{CompileError, Error, Errors, span::TSpan};
use parser::ast::{Ast, ExprId, ModuleId, ScopeId};
pub use traits::trait_def;
pub use type_def::type_def;

use crate::{
    Compiler, Type,
    compiler::{
        BodyOrTypes, CheckedFunction, Generics, LocalScopeParent, ModuleSpan, Signature, VarId,
        builtins,
    },
    hir::{CastId, HIRBuilder, Hir, LValue, Node, NodeId},
    types::{BaseType, TypeFull},
    typing::{LocalTypeId, LocalTypeIds, TypeInfo, TypeInfoOrIdx, TypeTable},
};

use self::exhaust::Exhaustion;

pub(crate) fn function(
    compiler: &Compiler,
    module: ModuleId,
    id: parser::ast::FunctionId,
) -> crate::compiler::CheckedFunction {
    let ast = &compiler.modules[module.idx()].ast.get().unwrap().ast;

    let function = &ast[id];

    let signature = compiler.get_signature(module, id);

    let mut types = TypeTable::new();

    let param_types = types.add_multiple_unknown(signature.total_arg_count() as u32);
    for ((_, param), r) in signature.all_params().zip(param_types.iter()) {
        let i = TypeInfoOrIdx::TypeInfo(TypeInfo::Known(param));
        types.replace(r, i);
    }

    let return_type = types.add(TypeInfo::Known(signature.return_type));

    let generic_count = signature.generics.count();
    let varargs = signature.varargs;

    let body_or_types = if let Some(body) = function.body {
        let hir = HIRBuilder::new(types);
        let params = signature
            .all_params()
            .zip(param_types.iter())
            .map(|((name, _), id)| (name.into(), id));

        let hir = check(
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
        BodyOrTypes::Body(hir)
    } else {
        let types = types.finish(compiler, &signature.generics, module);
        BodyOrTypes::Types(types)
    };

    // TODO: factor potential closed_over_scope into name
    let name = crate::compiler::function_name(&ast, function, module, id);

    CheckedFunction {
        name,
        params: param_types,
        varargs,
        return_type,
        generic_count,
        body_or_types,
    }
}

pub fn check(
    compiler: &Compiler,
    ast: &Ast,
    module: ModuleId,
    generics: &Generics,
    scope: ScopeId,
    mut hir: HIRBuilder,
    params: impl IntoIterator<Item = (Box<str>, LocalTypeId)>,
    expr: ExprId,
    expected: LocalTypeId,
    parent_scope: LocalScopeParent,
) -> Hir {
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
    check_ctx.finish(root, param_vars)
}

pub struct ProjectErrors {
    pub by_file: RefCell<dmap::DHashMap<ModuleId, Errors>>,
    crash_on_error: bool,
}
impl ProjectErrors {
    #[track_caller]
    pub fn emit(&self, module: ModuleId, error: CompileError) {
        if self.crash_on_error {
            panic!(
                "Error encountered and --crash-on-error is enabled. The error is: {error:?} in {module:?}"
            );
        }
        self.by_file
            .borrow_mut()
            .entry(module)
            .or_default()
            .emit_err(error);
    }

    pub fn enable_crash_on_error(&mut self) {
        self.crash_on_error = true;
    }

    pub fn new() -> Self {
        Self {
            by_file: RefCell::new(DHashMap::default()),
            crash_on_error: false,
        }
    }

    pub fn add_module(&self, module: ModuleId, errors: Errors) {
        let previous = self.by_file.borrow_mut().insert(module, errors);
        debug_assert!(previous.is_none(), "Duplicate module inserted into errors");
    }
}

pub struct Ctx<'a> {
    pub compiler: &'a Compiler,
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

    fn specify_base(
        &mut self,
        ty: LocalTypeId,
        base: BaseType,
        generic_count: u32,
        span: impl FnOnce(&Ast) -> TSpan,
    ) -> LocalTypeIds {
        self.hir.types.specify_base(
            ty,
            base,
            generic_count,
            self.generics,
            self.compiler,
            || ModuleSpan {
                module: self.module,
                span: span(self.ast),
            },
        )
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

    pub fn from_type_instance(&mut self, ty: Type, generics: LocalTypeIds) -> TypeInfoOrIdx {
        self.hir
            .types
            .from_type_instance(&self.compiler.types, ty, generics)
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
            current_ty =
                TypeInfoOrIdx::TypeInfo(TypeInfo::Instance(BaseType::Pointer, value_ty.into()));
            pointer_count += 1
        }
        while pointer_count < required_pointer_count {
            let value_ty = self.hir.types.add_info_or_idx(current_ty);
            let variable = self.hir.add_var(value_ty);
            value = Node::Promote {
                value: self.hir.add(value),
                variable,
            };
            current_ty =
                TypeInfoOrIdx::TypeInfo(TypeInfo::Instance(BaseType::Pointer, value_ty.into()));
            pointer_count += 1;
        }
        while pointer_count > required_pointer_count {
            let TypeInfo::Instance(BaseType::Pointer, pointee) =
                self.hir.types.get_info_or_idx(current_ty)
            else {
                // the deref was already checked so we know the type is wrapped in
                // `pointer_count` pointers
                unreachable!()
            };
            let pointee = pointee.nth(0).unwrap();
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

    pub(crate) fn finish(self, root: Node, params: Vec<VarId>) -> Hir {
        let mut hir = self
            .hir
            .finish(root, self.compiler, self.generics, self.module, params);
        for (exhaustion, ty, pat) in self.deferred_exhaustions {
            if let Ok(false) = exhaustion.is_exhausted(hir[ty], self.compiler) {
                let error = Error::Inexhaustive.at_span(self.ast[pat].span(self.ast));
                self.compiler.errors.emit(self.module, error);
            }
        }
        for (from_ty, to_ty, cast_expr, cast_id) in self.deferred_casts {
            let (cast, err) = cast::check(hir[from_ty], hir[to_ty], self.compiler);
            hir[cast_id].cast_ty = cast;
            if let Some(err) = err {
                self.compiler
                    .errors
                    .emit(self.module, err.at_span(self.ast[cast_expr].span(self.ast)));
            }
        }
        hir
    }

    fn specify_resolved(
        &mut self,
        var: LocalTypeId,
        ty: Type,
        generics: LocalTypeIds,
        span: impl Fn(&Ast) -> TSpan,
    ) {
        let info = if generics.is_empty() {
            TypeInfoOrIdx::TypeInfo(TypeInfo::Known(ty))
        } else {
            self.from_type_instance(ty, generics)
        };
        match info {
            TypeInfoOrIdx::TypeInfo(info) => self.specify(var, info, span),
            TypeInfoOrIdx::Idx(other) => self.unify(var, other, span),
        }
    }

    fn emit_unknown(&self, bounds: crate::typing::Bounds, span: TSpan) {
        let needed_bound = (!bounds.is_empty()).then(|| {
            let mut s = String::new();
            let mut first = true;
            for bound in bounds.iter() {
                let bound = self.hir.types.get_bound(bound);
                if first {
                    first = false;
                } else {
                    s.push_str(" + ");
                }
                s.push_str(
                    self.compiler
                        .get_trait_name(bound.trait_id.0, bound.trait_id.1),
                );
            }
            s
        });
        let err = Error::TypeMustBeKnownHere { needed_bound };
        self.compiler.errors.emit(self.module, err.at_span(span));
    }
}

pub fn verify_main_signature(
    compiler: &Compiler,
    signature: &Signature,
) -> Result<(), Option<CompileError>> {
    if !signature.params.is_empty() || signature.varargs {
        return Err(Some(Error::MainArgs.at_span(signature.span)));
    }
    if signature.generics.count() != 0 {
        return Err(Some(Error::MainGenerics.at_span(signature.span)));
    }
    match compiler.types.lookup(signature.return_type) {
        TypeFull::Instance(BaseType::Invalid, _) => Err(None),
        TypeFull::Instance(BaseType::Tuple, elems) if elems.is_empty() => Ok(()),
        TypeFull::Instance(b, _) if b.is_int() => Ok(()),
        _ => Err(Some(
            Error::InvalidMainReturnType(compiler.types.display(signature.return_type).to_string())
                .at_span(signature.span),
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
