pub mod builtins;
mod display;

use std::{
    cell::RefCell,
    collections::VecDeque,
    path::{Path, PathBuf},
    rc::Rc,
};

use dmap::DHashMap;
use error::{CompileError, Error, Errors, ImplIncompatibility};
use id::{ConstValueId, ModuleId, TypeId};
use indexmap::IndexMap;
use ir::ModuleOf;
use parser::{
    self,
    ast::{self, Ast, DefExprId, FunctionId, GenericDef, GlobalId, ScopeId, TraitId},
};
use span::{IdentPath, Span, TSpan};
use types::{FunctionType, InvalidTypeError, Primitive, Type, UnresolvedType};

use crate::{
    ProjectId,
    check::{self, traits},
    eval::{self, ConstValue},
    hir::Hir,
    irgen,
    types::{Bound, LocalTypeId, LocalTypeIds, TypeInfo, TypeTable},
};

use builtins::Builtins;

pub struct Compiler {
    projects: Vec<Project>,
    pub modules: Vec<Module>,
    pub const_values: Vec<(ConstValue, Type)>,
    pub types: Vec<ResolvableTypeDef>,
    pub ir: ir::Environment,
    pub ir_module: ir::ModuleId,
    pub dialects: Dialects,
    pub errors: Errors,
    pub builtins: Builtins,
}
impl ir::builder::HasEnvironment for &mut Compiler {
    fn env(&self) -> &ir::Environment {
        &self.ir
    }
}

#[derive(Clone, Copy)]
pub struct Dialects {
    pub arith: ModuleOf<ir::dialect::Arith>,
    pub tuple: ModuleOf<ir::dialect::Tuple>,
    pub mem: ModuleOf<ir::dialect::Mem>,
    pub cf: ModuleOf<ir::dialect::Cf>,
}
impl Compiler {
    pub fn new() -> Self {
        let mut ir = ir::Environment::new(ir::dialect::Primitive::create_infos());
        let dialects = Dialects {
            arith: ir.get_dialect_module(),
            tuple: ir.get_dialect_module(),
            mem: ir.get_dialect_module(),
            cf: ir.get_dialect_module(),
        };
        let ir_module = ir.create_module("main");
        Self {
            projects: Vec::new(),
            modules: Vec::new(),
            const_values: Vec::new(),
            types: Vec::new(),
            ir,
            ir_module,
            dialects,
            errors: Errors::new(),
            builtins: Builtins::default(),
        }
    }

    pub fn add_project(&mut self, name: String, root: PathBuf) -> Result<ProjectId, ProjectError> {
        let root = root.canonicalize().unwrap_or(root);
        if !root
            .try_exists()
            .map_err(|err| ProjectError::CantAccessPath(err, root.clone()))?
        {
            return Err(ProjectError::NonexistentPath(root));
        }
        for (project, i) in self.projects.iter().zip(0..) {
            if project.name == name && project.root == root {
                return Ok(ProjectId(i));
            }
        }
        let project_id = ProjectId(self.projects.len() as _);
        let root_module_id = ModuleId(self.modules.len() as _);
        self.modules.push(Module::at_path(
            root.clone(),
            project_id,
            root_module_id,
            None,
        ));
        self.projects.push(Project {
            name,
            root,
            root_module: root_module_id,
            dependencies: Vec::new(),
        });

        Ok(project_id)
    }

    pub fn add_dependency(&mut self, project: ProjectId, dependency: ProjectId) {
        self.projects[project.idx()].dependencies.push(dependency);
    }

    pub fn add_type_def(
        &mut self,
        module: ModuleId,
        id: ast::TypeId,
        name: Box<str>,
        generic_count: u8,
    ) -> TypeId {
        Self::add_type_def_to_types(module, id, name, generic_count, &mut self.types)
    }

    pub fn add_type_def_to_types(
        module: ModuleId,
        id: ast::TypeId,
        name: Box<str>,
        generic_count: u8,
        types: &mut Vec<ResolvableTypeDef>,
    ) -> TypeId {
        let type_id = TypeId(types.len() as _);
        types.push(ResolvableTypeDef {
            generic_count,
            module,
            id,
            name,
            resolved: Resolvable::Unresolved,
        });
        type_id
    }

    pub fn add_const_value(&mut self, value: ConstValue, ty: Type) -> ConstValueId {
        let id = ConstValueId(self.const_values.len() as _);
        self.const_values.push((value, ty));
        id
    }

    pub fn get_project(&self, id: ProjectId) -> &Project {
        &self.projects[id.idx()]
    }

    pub fn get_root_module(&self, module: ModuleId) -> ModuleId {
        self.modules[module.idx()].root
    }

    pub fn get_module_ast(&mut self, module_id: ModuleId) -> &Rc<Ast> {
        &self.get_parsed_module(module_id).ast
    }

    pub fn get_parsed_module(&mut self, module_id: ModuleId) -> &mut ParsedModule {
        if self.modules[module_id.idx()].ast.is_some() {
            // borrowing bullshit
            let Some(parsed) = &mut self.modules[module_id.idx()].ast else {
                unreachable!()
            };
            parsed
        } else {
            let module = &mut self.modules[module_id.idx()];
            let project = module.project;
            let root = module.root;

            // add dependencies to each module first
            let mut definitions: DHashMap<String, ast::Definition> = self.projects
                [module.project.idx()]
            .dependencies
            .iter()
            .map(|dependency| {
                let dependency = &self.projects[dependency.idx()];
                (
                    dependency.name.clone(),
                    ast::Definition::Module(dependency.root_module),
                )
            })
            .collect();

            let mut child_modules = Vec::new();
            let contents = if module.path.is_file() {
                std::fs::read_to_string(&module.path)
            } else {
                let (file, child_module_paths) =
                    crate::modules::module_and_children(&module.path, module_id == module.root);
                for (name, path) in child_module_paths {
                    let id = ModuleId(self.modules.len() as _);
                    self.modules
                        .push(Module::at_path(path, project, root, Some(module_id)));
                    definitions.insert(name, ast::Definition::Module(id));
                    child_modules.push(id);
                }
                let s = std::fs::read_to_string(&file);
                self.modules[module_id.idx()].path = file;
                s
            };
            let source = match contents {
                Ok(source) => source.into_boxed_str(),
                Err(err) => panic!(
                    "compiler failed to open the file {}: {:?}",
                    self.modules[module_id.idx()].path.display(),
                    err,
                ),
            };

            let mut errors = Errors::new();
            if self.errors.crash_on_error() {
                errors.enable_crash_on_error();
            }
            let ast = parser::parse(source, &mut errors, module_id, definitions);
            self.errors.append(errors);
            let checked = ModuleSymbols::empty(&ast);
            let module = &mut self.modules[module_id.idx()];
            let instances = IrInstances::new(ast.function_count(), ast.global_count());
            module.ast = Some(ParsedModule {
                ast: Rc::new(ast),
                child_modules,
                symbols: checked,
                instances,
            });
            let Some(parsed) = module.ast.as_mut() else {
                unreachable!()
            };
            parsed
        }
    }

    pub fn resolve_in_module(&mut self, module: ModuleId, name: &str, name_span: Span) -> Def {
        let scope = self.get_module_ast(module).top_level_scope_id();
        self.resolve_in_scope(module, scope, name, name_span)
    }

    pub fn resolve_in_scope(
        &mut self,
        module: ModuleId,
        mut scope: ScopeId,
        name: &str,
        name_span: Span,
    ) -> Def {
        let def = loop {
            match self.get_scope_def(module, scope, name) {
                Some(def) => break Some(def),
                None => {
                    if let Some(parent) = self.get_module_ast(module)[scope].parent {
                        scope = parent;
                    } else {
                        break None;
                    }
                }
            }
        };
        def.unwrap_or_else(|| {
            if let Some(builtin_module) = builtins::get_prelude(self) {
                let builtin_scope = self.get_module_ast(builtin_module).top_level_scope_id();
                if let Some(def) = self.get_scope_def(builtin_module, builtin_scope, name) {
                    return def;
                }
            }
            self.errors
                .emit_err(Error::UnknownIdent(name.into()).at_span(name_span));
            Def::Invalid
        })
    }

    pub fn get_scope_def(&mut self, module: ModuleId, scope: ScopeId, name: &str) -> Option<Def> {
        let ast = self.get_module_ast(module);
        let &def = ast[scope].definitions.get(name)?;
        let def = match def {
            // PERF: return reference here instead of cloning if possible
            ast::Definition::Expr { id, .. } => self.get_def_expr(module, scope, name, id).clone(),
            ast::Definition::Use { path, .. } => self.resolve_path(module, scope, path),
            ast::Definition::Global(id) => Def::Global(module, id),
            ast::Definition::Module(id) => Def::Module(id),
            ast::Definition::Generic(i) => Def::Type(Type::Generic(i)),
        };
        Some(def)
    }

    pub fn get_def_expr(
        &mut self,
        module: ModuleId,
        scope: ScopeId,
        name: &str,
        id: DefExprId,
    ) -> &Def {
        let parsed = self.get_parsed_module(module);
        let def_expr = &mut parsed.symbols.def_exprs[id.0 as usize];
        match def_expr {
            Resolvable::Resolved(_) => {
                // borrowing bullshit
                let Resolvable::Resolved(def) =
                    &self.get_parsed_module(module).symbols.def_exprs[id.0 as usize]
                else {
                    unreachable!()
                };
                return def;
            }
            Resolvable::Resolving => {
                let ast = self.get_module_ast(module);
                let (value, _) = ast[id];
                let span = ast[value].span(ast).in_mod(module);
                self.errors
                    .emit_err(Error::RecursiveDefinition.at_span(span));
                return &Def::Invalid;
            }
            Resolvable::Unresolved => {
                *def_expr = Resolvable::Resolving;
            }
        }
        let ast = Rc::clone(&parsed.ast);
        let (value, ty) = &ast[id];
        let value = *value;
        let def = eval::def_expr(self, module, scope, &ast, value, name, ty);
        self.get_parsed_module(module).symbols.def_exprs[id.0 as usize].put(def)
    }

    pub fn resolve_path(&mut self, module: ModuleId, mut scope: ScopeId, path: IdentPath) -> Def {
        let ast = self.get_module_ast(module).clone();
        let (root, segments, last) = path.segments(ast.src());
        let mut current_module = module;
        if root.is_some() {
            let module = &self.modules[current_module.idx()];
            current_module = module.root;
            scope = self.get_module_ast(current_module).top_level_scope_id();
        }
        for (name, name_span) in segments {
            match self.resolve_in_scope(current_module, scope, name, name_span.in_mod(module)) {
                Def::Module(new_mod) => {
                    current_module = new_mod;
                    scope = self.get_module_ast(current_module).top_level_scope_id();
                }
                Def::Invalid => return Def::Invalid,
                _ => {
                    self.errors
                        .emit_err(Error::ModuleExpected.at_span(name_span.in_mod(module)));
                    return Def::Invalid;
                }
            }
        }
        let Some((name, name_span)) = last else {
            return Def::Module(current_module);
        };
        self.resolve_in_scope(current_module, scope, name, name_span.in_mod(module))
    }

    pub fn resolve_type(&mut self, ty: &UnresolvedType, module: ModuleId, scope: ScopeId) -> Type {
        match ty {
            &UnresolvedType::Primitive { ty, .. } => Type::Primitive(ty),
            UnresolvedType::Unresolved(path, generics) => {
                match self.resolve_path(module, scope, *path) {
                    Def::GenericType(id) => {
                        let expected = self.get_resolved_type_generic_count(id);
                        let found = generics.as_ref().map_or(0, |g| g.0.len() as u8);
                        if expected != found {
                            let span = generics.as_ref().map_or_else(|| path.span(), |g| g.1);
                            self.errors.emit_err(
                                Error::InvalidGenericCount { expected, found }
                                    .at_span(span.in_mod(module)),
                            );
                            return Type::Invalid;
                        }
                        Type::DefId {
                            id,
                            generics: generics
                                .as_ref()
                                .map_or::<&[UnresolvedType], _>(&[], |g| &*g.0)
                                .iter()
                                .map(|ty| self.resolve_type(ty, module, scope))
                                .collect(),
                        }
                    }
                    Def::Type(ty) => {
                        if let Some((_, span)) = generics {
                            self.errors
                                .emit_err(Error::UnexpectedGenerics.at_span(span.in_mod(module)));
                        }
                        ty
                    }
                    Def::Invalid => Type::Invalid,
                    _ => {
                        self.errors
                            .emit_err(Error::TypeExpected.at_span(ty.span().in_mod(module)));
                        Type::Invalid
                    }
                }
            }
            UnresolvedType::Pointer(b) => {
                let (pointee, _) = &**b;
                Type::Pointer(Box::new(self.resolve_type(pointee, module, scope)))
            }
            UnresolvedType::Array(b) => {
                let (elem_ty, size, _) = &**b;
                let elem_ty = self.resolve_type(elem_ty, module, scope);
                let Some(size) = *size else {
                    panic!("inferred array size is not allowed here")
                };
                Type::Array(Box::new((elem_ty, size)))
            }
            UnresolvedType::Tuple(elems, _) => {
                let elems = elems
                    .iter()
                    .map(|elem| self.resolve_type(elem, module, scope))
                    .collect();
                Type::Tuple(elems)
            }
            UnresolvedType::Function {
                span_and_return_type,
                params,
            } => Type::Function(types::FunctionType {
                params: params
                    .iter()
                    .map(|param| self.resolve_type(param, module, scope))
                    .collect(),
                return_type: Box::new(self.resolve_type(&span_and_return_type.1, module, scope)),
            }),
            UnresolvedType::Infer(span) => {
                self.errors
                    .emit_err(Error::InferredTypeNotAllowedHere.at_span(span.in_mod(module)));
                Type::Invalid
            }
        }
    }

    pub fn unresolved_primitive(
        &mut self,
        ty: &UnresolvedType,
        module: ModuleId,
        scope: ScopeId,
    ) -> ResolvedPrimitive {
        match ty {
            &UnresolvedType::Primitive { ty, .. } => ResolvedPrimitive::Primitive(ty),
            &UnresolvedType::Unresolved(path, None) => {
                match self.resolve_path(module, scope, path) {
                    Def::Invalid => ResolvedPrimitive::Invalid,
                    Def::Type(Type::Primitive(p)) => ResolvedPrimitive::Primitive(p),
                    _ => ResolvedPrimitive::Other,
                }
            }
            UnresolvedType::Infer(_) => ResolvedPrimitive::Infer,
            _ => ResolvedPrimitive::Other,
        }
    }

    pub fn unresolved_matches_primitive(
        &mut self,
        ty: &UnresolvedType,
        primitive: Primitive,
        module: ModuleId,
        scope: ScopeId,
    ) -> Result<bool, InvalidTypeError> {
        match self.unresolved_primitive(ty, module, scope) {
            ResolvedPrimitive::Infer => Ok(true),
            ResolvedPrimitive::Primitive(p) => Ok(p == primitive),
            ResolvedPrimitive::Other => Ok(false),
            ResolvedPrimitive::Invalid => Err(InvalidTypeError),
        }
    }

    pub fn get_signature(&mut self, module: ModuleId, id: ast::FunctionId) -> &Rc<Signature> {
        let parsed = self.modules[module.idx()].ast.as_mut().unwrap();
        let signature = &mut parsed.symbols.function_signatures[id.idx()];
        match signature {
            Resolvable::Resolved(_) => {
                // borrowing bullshit
                let Resolvable::Resolved(signature) = &self.modules[module.idx()]
                    .ast
                    .as_ref()
                    .unwrap()
                    .symbols
                    .function_signatures[id.idx()]
                else {
                    unreachable!()
                };
                signature
            }
            Resolvable::Resolving => panic!("function signature depends on itself recursively"),
            Resolvable::Unresolved => {
                *signature = Resolvable::Resolving;
                let ast = parsed.ast.clone();
                let function = &ast[id];
                // TODO: don't always allow inferring function
                let signature = self.check_signature(function, module, &ast);
                self.modules[module.idx()]
                    .ast
                    .as_mut()
                    .unwrap()
                    .symbols
                    .function_signatures[id.idx()]
                .put(Rc::new(signature))
            }
        }
    }

    pub fn check_signature_with_type(
        &mut self,
        func_id: (ModuleId, ast::FunctionId),
        ty: &UnresolvedType,
        scope: ScopeId,
        ty_module: ModuleId,
        func_span: Span,
    ) -> Result<(), SignatureError> {
        let signature = self.get_signature(func_id.0, func_id.1);
        match ty {
            UnresolvedType::Infer(_) => Ok(()),
            UnresolvedType::Function {
                span_and_return_type: _,
                params: _,
            } => todo!("check partial function type annotation"),
            UnresolvedType::Unresolved(path, generics) => {
                let signature = Rc::clone(signature);
                match self.resolve_path(ty_module, scope, *path) {
                    Def::Invalid => Err(SignatureError),
                    Def::Type(ty) => {
                        if let Some((generics, generics_span)) = generics
                            && !generics.is_empty()
                        {
                            self.errors.emit_err(
                                Error::UnexpectedGenerics.at_span(generics_span.in_mod(ty_module)),
                            );
                            return Err(SignatureError);
                        }
                        let Type::Function(function_ty) = &ty else {
                            self.errors.emit_err(
                                Error::MismatchedType {
                                    expected: ty.to_string(),
                                    found: "a function".to_owned(),
                                }
                                .at_span(func_span),
                            );
                            return Err(SignatureError);
                        };
                        match signature.fits_function_type(function_ty) {
                            Ok(true) => Ok(()),
                            Ok(false) => {
                                self.errors.emit_err(
                                    Error::MismatchedType {
                                        expected: ty.to_string(),
                                        found: "TODO: display function type".to_owned(),
                                    }
                                    .at_span(func_span),
                                );
                                Err(SignatureError)
                            }
                            Err(InvalidTypeError) => Err(SignatureError),
                        }
                    }
                    _ => {
                        self.errors
                            .emit_err(Error::TypeExpected.at_span(path.span().in_mod(ty_module)));
                        Err(SignatureError)
                    }
                }
            }
            _ => {
                let mut expected = String::new();
                ty.to_string(&mut expected, self.get_module_ast(ty_module).src());
                self.errors.emit_err(
                    Error::MismatchedType {
                        expected,
                        found: "a function".to_owned(),
                    }
                    .at_span(func_span),
                );
                Err(SignatureError)
            }
        }
    }

    pub fn resolve_generics(
        &mut self,
        generics: &[GenericDef],
        module: ModuleId,
        scope: ScopeId,
        ast: &Ast,
    ) -> Generics {
        let generics = generics
            .iter()
            .map(|def| {
                let requirements = def
                    .bounds
                    .iter()
                    .map(|bound| match self.resolve_path(module, scope, bound.path) {
                        Def::Trait(trait_module, trait_id) => {
                            let trait_id = (trait_module, trait_id);
                            let generic_count = self.get_trait_generic_count(trait_id);
                            if generic_count as usize != bound.generics.len() {
                                self.errors.emit_err(
                                    Error::InvalidGenericCount {
                                        expected: generic_count,
                                        found: bound.generics.len() as _,
                                    }
                                    .at_span(bound.generics_span.in_mod(module)),
                                );
                                todo!("handle invalid bounds")
                            }
                            let generics = bound
                                .generics
                                .iter()
                                .map(|ty| self.resolve_type(ty, module, scope))
                                .collect();
                            TraitBound { trait_id, generics }
                        }
                        Def::Invalid => todo!("handle invalid bounds"),
                        _ => {
                            self.errors.emit_err(
                                Error::TraitExpected.at_span(bound.path.span().in_mod(module)),
                            );
                            todo!("handle invalid bounds")
                        }
                    })
                    .collect();
                (def.name(ast.src()).to_owned(), requirements)
            })
            .collect();
        Generics { generics }
    }

    pub fn check_signature(
        &mut self,
        function: &ast::Function,
        module: ModuleId,
        ast: &Ast,
    ) -> Signature {
        let scope = function.scope;
        let generics = self.resolve_generics(&function.generics, module, scope, ast);

        let params = function
            .params
            .iter()
            .map(|(name_span, ty)| {
                let name = ast[*name_span].into();
                let ty = self.resolve_type(ty, module, scope);
                (name, ty)
            })
            .collect();

        let named_params = function
            .named_params
            .iter()
            .map(|(name_span, ty, default_value)| {
                let name = ast[*name_span].into();
                let (ty, default_value) = match default_value.map(|default_value| {
                    match eval::value_expr(self, module, scope, ast, default_value, ty) {
                        Ok(val) => val,
                        Err(err) => {
                            self.errors.emit_err(
                                Error::EvalFailed(err)
                                    .at_span(ast[default_value].span(ast).in_mod(module)),
                            );
                            (ConstValue::Undefined, Type::Invalid)
                        }
                    }
                }) {
                    Some((value, ty)) => (ty.clone(), Some(self.add_const_value(value, ty))),
                    None => (self.resolve_type(ty, module, scope), None),
                };
                (name, ty, default_value)
            })
            .collect();
        let return_type = self.resolve_type(&function.return_type, module, scope);
        Signature {
            params,
            named_params,
            varargs: function.varargs,
            return_type,
            generics,
            span: function.signature_span,
        }
    }

    pub fn get_trait_name(&self, module: ModuleId, id: ast::TraitId) -> &str {
        let parsed = self.modules[module.idx()].ast.as_ref().unwrap();
        let trait_def = &parsed.ast[id];
        &parsed.ast.src()[trait_def.associated_name.range()]
    }

    pub fn get_trait_generic_count(&mut self, trait_id: (ModuleId, TraitId)) -> u8 {
        // subtract the self generic
        (self.get_parsed_module(trait_id.0).ast[trait_id.1]
            .generics
            .len()
            - 1)
        .try_into()
        .unwrap()
    }

    /// returns None when the trait can't be resolved, an error was already emitted in that case
    pub fn get_checked_trait(
        &mut self,
        module: ModuleId,
        id: ast::TraitId,
    ) -> Option<&Rc<CheckedTrait>> {
        let parsed = self.get_parsed_module(module);
        match &parsed.symbols.traits[id.idx()] {
            Resolvable::Resolved(_) => {
                // borrowing bullshit
                let Resolvable::Resolved(checked) =
                    &self.get_parsed_module(module).symbols.traits[id.idx()]
                else {
                    unreachable!()
                };
                Some(checked)
            }
            Resolvable::Resolving => {
                let span = parsed.ast[id].span(parsed.ast.scopes()).in_mod(module);
                self.errors
                    .emit_err(Error::RecursiveDefinition.at_span(span));
                None
            }
            Resolvable::Unresolved => {
                let ast = Rc::clone(&parsed.ast);
                let checked = check::trait_def(self, ast, (module, id));
                Some(self.get_parsed_module(module).symbols.traits[id.idx()].put(Rc::new(checked)))
            }
        }
    }

    pub fn get_impl_method(
        &mut self,
        trait_id: (ModuleId, ast::TraitId),
        ty: &Type,
        trait_generics: &[Type],
        method_index: u16,
    ) -> Option<((ModuleId, FunctionId), Vec<Type>)> {
        let mut impl_generics = Vec::new();
        let def = if let &Type::DefId { id, .. } = ty {
            Some(Rc::clone(self.get_resolved_type_def(id)))
        } else {
            None
        };

        let checked_trait = self.get_checked_trait(trait_id.0, trait_id.1)?;
        let impls = def
            .iter()
            .flat_map(|def| {
                def.inherent_trait_impls
                    .get(&trait_id)
                    .map_or(&[] as &[_], |impls| impls.as_slice())
            })
            .chain(&checked_trait.impls);
        'impls: for impl_ in impls {
            impl_generics.clear();
            impl_generics.resize(impl_.generics.count().into(), Type::Invalid);
            if !impl_.impl_ty.matches_type(ty, &mut impl_generics) {
                continue 'impls;
            }
            debug_assert_eq!(trait_generics.len(), impl_.trait_generics.len());
            for (impl_ty, ty) in impl_.trait_generics.iter().zip(trait_generics) {
                if !impl_ty.instantiate_matches(ty, &mut impl_generics) {
                    continue 'impls;
                }
            }
            debug_assert!(
                impl_generics.iter().all(|ty| !matches!(ty, Type::Invalid)),
                "impl generics were not properly instantiated"
            );
            return Some((
                (impl_.impl_module, impl_.functions[method_index as usize]),
                impl_generics,
            ));
        }
        None
    }

    pub fn get_hir(&mut self, module: ModuleId, id: ast::FunctionId) -> &Rc<CheckedFunction> {
        let checked = &self.modules[module.idx()].ast.as_ref().unwrap().symbols;
        match &checked.functions[id.idx()] {
            Resolvable::Resolved(_) => {
                // borrowing bullshit
                let Resolvable::Resolved(checked) = &self.modules[module.idx()]
                    .ast
                    .as_ref()
                    .unwrap()
                    .symbols
                    .functions[id.idx()]
                else {
                    unreachable!()
                };
                checked
            }
            Resolvable::Resolving => panic!("checked function depends on itself recursively"),
            Resolvable::Unresolved => {
                let checked = check::function(self, module, id);
                self.modules[module.idx()]
                    .ast
                    .as_mut()
                    .unwrap()
                    .symbols
                    .functions[id.idx()]
                .put(Rc::new(checked))
            }
        }
    }

    pub fn get_function_name(&self, module: ModuleId, function: ast::FunctionId) -> &str {
        let ast = &self.modules[module.idx()].ast.as_ref().unwrap().ast;
        &ast[ast[function].associated_name]
    }

    pub fn get_type_name(&self, ty: TypeId) -> &str {
        &self.types[ty.idx()].name
    }

    pub fn get_resolved_type_generic_count(&mut self, ty: TypeId) -> u8 {
        self.types[ty.idx()].generic_count
    }

    pub fn get_resolved_type_def(&mut self, ty: TypeId) -> &Rc<ResolvedTypeDef> {
        match &self.types[ty.idx()].resolved {
            Resolvable::Resolved(_) => {
                // borrowing bullshit
                let Resolvable::Resolved(id) = &self.types[ty.idx()].resolved else {
                    unreachable!()
                };
                id
            }
            Resolvable::Resolving => todo!("handle recursive type definition"),
            Resolvable::Unresolved => {
                let resolved = check::type_def(self, ty);
                self.types[ty.idx()].resolved.put(Rc::new(resolved))
            }
        }
    }

    pub fn uninhabited(&mut self, ty: &Type, generics: &[Type]) -> Result<bool, InvalidTypeError> {
        Ok(match ty {
            Type::Primitive(_) => false,
            Type::DefId {
                id,
                generics: inner_generics,
            } => {
                let inner_generics: Box<[Type]> = inner_generics
                    .iter()
                    .map(|ty| ty.instantiate_generics(generics))
                    .collect();
                let def = Rc::clone(self.get_resolved_type_def(*id));
                def.def.uninhabited(self, &inner_generics)?
            }
            Type::Pointer(_) => false,
            Type::Array(arr) => arr.1 != 0 && self.uninhabited(&arr.0, generics)?,
            Type::Tuple(fields) => fields.iter().try_fold(false, |b, field| {
                Ok(b || self.uninhabited(field, generics)?)
            })?,
            Type::Generic(_) => false, // TODO: does this cause problems anywhere? a generic type is not *known* to be uninhabited
            Type::LocalEnum(variants) => variants.iter().try_fold(true, |b, (_, args)| {
                Ok(b && args
                    .iter()
                    .try_fold(false, |b, arg| Ok(b || self.uninhabited(arg, generics)?))?)
            })?,
            Type::Function(_) => false,
            Type::Invalid => return Err(InvalidTypeError),
        })
    }

    pub fn get_checked_global(&mut self, module: ModuleId, id: GlobalId) -> &(ConstValue, Type) {
        let parsed = self.get_parsed_module(module);
        let ast = parsed.ast.clone();
        match &parsed.symbols.globals[id.idx()] {
            Resolvable::Resolved(_) => {
                let Resolvable::Resolved(global) =
                    &self.get_parsed_module(module).symbols.globals[id.idx()]
                else {
                    unreachable!()
                };
                global
            }
            Resolvable::Resolving => {
                let span = ast[id].span.in_mod(module);
                self.errors
                    .emit_err(Error::RecursiveDefinition.at_span(span));
                self.get_parsed_module(module).symbols.globals[id.idx()]
                    .put((ConstValue::Undefined, Type::Invalid))
            }
            Resolvable::Unresolved => {
                parsed.symbols.globals[id.idx()] = Resolvable::Resolving;
                let global = &ast[id];
                let (const_value, ty) = match eval::def_expr(
                    self,
                    module,
                    global.scope,
                    &ast,
                    global.val,
                    &global.name,
                    &global.ty,
                ) {
                    Def::ConstValue(id) => self.const_values[id.idx()].clone(),
                    Def::Invalid => (ConstValue::Undefined, Type::Invalid),
                    def => {
                        if !matches!(def, Def::Invalid) {
                            let error =
                                Error::ExpectedValue.at_span(ast[global.val].span_in(&ast, module));
                            self.errors.emit_err(error);
                        }
                        (ConstValue::Undefined, Type::Invalid)
                    }
                };
                self.modules[module.idx()]
                    .ast
                    .as_mut()
                    .unwrap()
                    .symbols
                    .globals[id.idx()]
                .put((const_value, ty))
            }
        }
    }

    pub fn get_builtin_panic(&mut self) -> ir::FunctionId {
        let (panic_mod, panic_function) = builtins::get_panic(self);
        self.get_ir_function_id(panic_mod, panic_function, Vec::new())
    }

    pub fn check_complete_project(&mut self, project: ProjectId) {
        let root = self.projects[project.idx()].root_module;
        let mut modules_to_check = VecDeque::from([root]);
        while let Some(module) = modules_to_check.pop_front() {
            let ast = self.get_module_ast(module).clone();
            for scope in ast.scope_ids() {
                for (name, def) in &ast[scope].definitions {
                    match *def {
                        ast::Definition::Use { path, .. } => {
                            // TODO: cache results to prevent duplicate errors/avoid duplicate resolval
                            self.resolve_path(module, scope, path);
                        }
                        ast::Definition::Expr { id, .. } => {
                            let def = self.get_def_expr(module, scope, name, id);
                            if let &Def::Function(module, id) = def {
                                self.get_hir(module, id);
                            }
                        }
                        ast::Definition::Module(id) => {
                            // when checking std, each module still gets a reference to std. To
                            // prevent an infinite loop when checking the std library, check that
                            // this isn't the case by comparing against the root module
                            if self.modules[id.idx()].project == project && id != root {
                                modules_to_check.push_back(id);
                            }
                        }
                        ast::Definition::Global(_) | ast::Definition::Generic(_) => {}
                    }
                }
            }

            for id in ast.type_ids() {
                let parsed = self.modules[module.idx()].ast.as_mut().unwrap();
                let id = match &mut parsed.symbols.types[id.idx()] {
                    Some(id) => *id,
                    ty @ None => {
                        let generic_count = parsed.ast[id].generic_count();
                        let id = Self::add_type_def_to_types(
                            module,
                            id,
                            "<anonymous type>".into(),
                            generic_count,
                            &mut self.types,
                        );
                        *ty = Some(id);
                        id
                    }
                };
                let resolved = Rc::clone(self.get_resolved_type_def(id));
                for &method in resolved.methods.values() {
                    self.get_hir(module, method);
                }
                for impls in resolved.inherent_trait_impls.values() {
                    for impl_ in impls {
                        for &id in &impl_.functions {
                            self.get_hir(module, id);
                        }
                    }
                }
            }

            for id in ast.global_ids() {
                self.get_checked_global(module, id);
            }

            for id in ast.trait_ids() {
                if let Some(checked) = self.get_checked_trait(module, id) {
                    let checked = Rc::clone(checked);
                    for impl_ in &checked.impls {
                        for &id in &impl_.functions {
                            self.get_hir(module, id);
                        }
                    }
                }
            }
        }
    }

    pub fn get_ir_function_id(
        &mut self,
        module: ModuleId,
        function: ast::FunctionId,
        generics: Vec<Type>,
    ) -> ir::FunctionId {
        self.get_parsed_module(module);
        if let Some(&id) = self.modules[module.idx()]
            .ast
            .as_mut()
            .unwrap()
            .instances
            .functions[function.idx()]
        .get(&generics)
        {
            return id;
        }

        let mut to_generate = vec![];
        let checked = Rc::clone(self.get_hir(module, function));
        let func = irgen::declare_function(self, &checked, &generics);
        let id = self.ir.add_function(self.ir_module, func);
        to_generate.push(FunctionToGenerate {
            ir_id: id,
            module,
            ast_function_id: function,
            generics: generics.clone(),
        });
        let prev = self.modules[module.idx()]
            .ast
            .as_mut()
            .unwrap()
            .instances
            .functions[function.idx()]
        .insert(generics, id);
        debug_assert!(prev.is_none());

        while let Some(f) = to_generate.pop() {
            self.get_hir(f.module, f.ast_function_id);
            // got checked function above
            let symbols = &self.modules[f.module.idx()].ast.as_mut().unwrap().symbols;
            let Resolvable::Resolved(checked) = &symbols.functions[f.ast_function_id.idx()] else {
                unreachable!()
            };
            let checked = Rc::clone(checked);
            assert_eq!(
                checked.generic_count as usize,
                f.generics.len(),
                "a function instance queued for ir generation has an invalid generic count"
            );

            if let Some(body) = &checked.body {
                let return_type = self.ir[f.ir_id].return_type().unwrap();
                let (builder, params) = ir::builder::Builder::begin_function(&mut *self, f.ir_id);
                let res = irgen::lower_hir(
                    builder,
                    body,
                    &checked.types,
                    &mut to_generate,
                    &f.generics,
                    params,
                    return_type,
                );
                self.ir.attach_body(f.ir_id, res);
            }
        }
        id
    }

    pub fn print_project_hir(&mut self, project: ProjectId) {
        let project = self.get_project(project);
        let mut module_queue = VecDeque::from([project.root_module]);
        while let Some(module) = module_queue.pop_front() {
            let functions = self.get_module_ast(module).function_ids();
            for function in functions {
                self.get_hir(module, function);
                let Resolvable::Resolved(hir) = &self.modules[module.idx()]
                    .ast
                    .as_ref()
                    .unwrap()
                    .symbols
                    .functions[function.idx()]
                else {
                    unreachable!()
                };
                tracing::debug!(target: "hir", function = hir.name, "\n{}", hir.display(self));
            }
            module_queue.extend(self.get_parsed_module(module).child_modules.iter().copied())
        }
    }

    /// Emit project ir starting from a root function (for example the main function) while
    /// generating all functions recursively that are called by that function
    pub fn emit_ir_from_root(&mut self, root: (ModuleId, FunctionId)) -> Vec<ir::FunctionId> {
        let mut functions_to_emit = VecDeque::from([(root.0, root.1, vec![])]);
        let mut finished_functions = Vec::new();
        while let Some((module, function, generics)) = functions_to_emit.pop_front() {
            let id = self.get_ir_function_id(module, function, generics);
            finished_functions.push(id);
        }

        finished_functions
    }

    /// Emit the ir for all non-generic top-level functions in a project and functions called by them.
    pub fn emit_whole_project_ir(&mut self, project: ProjectId) {
        let project = self.get_project(project);
        let mut module_queue = VecDeque::from([project.root_module]);
        while let Some(module) = module_queue.pop_front() {
            let ast = Rc::clone(self.get_module_ast(module));
            let functions = ast.function_ids();
            for function in functions {
                if ast[function].generics.is_empty() {
                    self.emit_ir_from_root((module, function));
                }
            }
        }
    }

    pub fn verify_main_and_add_entry_point(
        &mut self,
        main: (ModuleId, FunctionId),
    ) -> Result<ir::FunctionId, Option<CompileError>> {
        let main_ir_id = self.get_ir_function_id(main.0, main.1, vec![]);
        let main_signature = self.get_signature(main.0, main.1);
        check::verify_main_signature(main_signature, main.0).map(|()| {
            let main_signature = Rc::clone(self.get_signature(main.0, main.1));
            let entry_point = irgen::entry_point(
                main_ir_id,
                &main_signature.return_type,
                &self.ir,
                &self.dialects,
            );
            self.ir.add_function(self.ir_module, entry_point)
        })
    }

    pub fn get_ir_function(&self, id: ir::FunctionId) -> &ir::Function {
        &self.ir[id]
    }

    /// prints all errors, consuming them and returns true if any fatal errors were present
    pub fn print_errors(&mut self) -> bool {
        let working_directory = std::env::current_dir().ok();
        use color_format::cprintln;
        let errors = std::mem::replace(&mut self.errors, Errors::new());
        let mut print = |error: &CompileError| {
            if error.span.is_missing() {
                println!(
                    "[missing location]: {} {}",
                    error.err.conclusion(),
                    error.err.details().unwrap_or_default(),
                );
            } else {
                let ast = self.get_module_ast(error.span.module).clone();
                let mut path: &Path = &self.modules[error.span.module.idx()].path;
                let relative = working_directory
                    .as_ref()
                    .and_then(|cwd| pathdiff::diff_paths(path, cwd));
                if let Some(relative) = &relative {
                    path = relative;
                }
                error::print(
                    &error.err,
                    TSpan::new(error.span.start, error.span.end),
                    ast.src(),
                    path,
                );
            }
        };
        let err_count = errors.error_count();
        if err_count != 0 {
            cprintln!(
                "#r<Finished with #u;r!<{}> error{}>",
                err_count,
                if err_count == 1 { "" } else { "s" }
            );
            for error in &errors.errors {
                print(error);
            }
            return true;
        }
        if errors.warning_count() != 0 {
            let c = errors.warning_count();
            cprintln!(
                "#r<Finished with #u;r!<{}> warning{}>",
                c,
                if c == 1 { "" } else { "s" }
            );
            for warn in &errors.warnings {
                print(warn);
            }
        }
        false
    }

    pub fn resolve_builtins(&mut self, std: ProjectId) {
        self.builtins.std = std;
        self.builtins.primitives = builtins::Primitives::resolve(self);
    }
}

pub enum ProjectError {
    CantAccessPath(std::io::Error, PathBuf),
    NonexistentPath(PathBuf),
}

#[derive(Debug, Default, Clone, Copy)]
pub enum Resolvable<T> {
    #[default]
    Unresolved,
    Resolving,
    Resolved(T),
}
impl<T> Resolvable<T> {
    pub fn put(&mut self, resolved: T) -> &mut T {
        debug_assert!(!matches!(self, Self::Resolved(_)), "put Resolved twice");
        *self = Self::Resolved(resolved);
        let Self::Resolved(resolved) = self else {
            // SAFETY: was just set to resolved variant and we have unique access
            unsafe { std::hint::unreachable_unchecked() }
        };
        resolved
    }
}

id::id!(VarId);
id::id!(CaptureId);

pub enum LocalScopeParent<'p> {
    Some(&'p LocalScope<'p>),
    ClosedOver {
        scope: &'p LocalScope<'p>,
        captures: &'p RefCell<IndexMap<VarId, CaptureId>>,
    },
    None,
}

pub struct LocalScope<'p> {
    pub parent: LocalScopeParent<'p>,
    pub variables: DHashMap<Box<str>, VarId>,
    pub module: ModuleId,
    /// should only be none if this scope has a parent
    pub static_scope: Option<ScopeId>,
}
pub enum LocalItem {
    Var(VarId),
    Def(Def),
    Capture(CaptureId),
    Invalid,
}
impl LocalScope<'_> {
    pub fn resolve(&self, name: &str, name_span: TSpan, compiler: &mut Compiler) -> LocalItem {
        if let Some(var) = self.variables.get(name) {
            LocalItem::Var(*var)
        } else if let Some(def) = self
            .static_scope
            .and_then(|static_scope| compiler.get_scope_def(self.module, static_scope, name))
        {
            LocalItem::Def(def)
        } else {
            match &self.parent {
                LocalScopeParent::Some(parent) => parent.resolve(name, name_span, compiler),
                LocalScopeParent::ClosedOver { scope, captures } => {
                    let local = scope.resolve(name, name_span, compiler);
                    match local {
                        LocalItem::Var(id) => {
                            let mut captures = captures.borrow_mut();
                            let next_id = CaptureId(captures.len() as _);
                            LocalItem::Capture(*captures.entry(id).or_insert_with(|| next_id))
                        }
                        LocalItem::Def(def) => LocalItem::Def(def),
                        LocalItem::Capture(_) => todo!("capture captures"),
                        LocalItem::Invalid => LocalItem::Invalid,
                    }
                }
                LocalScopeParent::None => {
                    if let Some(static_parent) = self.static_scope.and_then(|static_scope| {
                        compiler.get_module_ast(self.module)[static_scope].parent
                    }) {
                        LocalItem::Def(compiler.resolve_in_scope(
                            self.module,
                            static_parent,
                            name,
                            name_span.in_mod(self.module),
                        ))
                    } else {
                        compiler.errors.emit_err(
                            Error::UnknownIdent(name.into()).at_span(name_span.in_mod(self.module)),
                        );
                        LocalItem::Invalid
                    }
                }
            }
        }
    }

    pub fn get_innermost_static_scope(&self) -> ScopeId {
        let mut current_local = self;
        loop {
            if let Some(static_scope) = self.static_scope {
                return static_scope;
            }
            // a local scope has to have a parent scope if it doesn't have a static scope
            // associated with it
            current_local = match &current_local.parent {
                LocalScopeParent::Some(parent) => parent,
                LocalScopeParent::ClosedOver { scope, captures: _ } => scope,
                LocalScopeParent::None => unreachable!(),
            };
        }
    }
}

#[derive(Clone, Debug)]
pub enum Def {
    Invalid,
    Function(ModuleId, ast::FunctionId),
    // a base type with generics not yet applied to it
    GenericType(id::TypeId),
    Type(Type),
    Trait(ModuleId, ast::TraitId),
    ConstValue(ConstValueId),
    Module(ModuleId),
    Global(ModuleId, GlobalId),
}
impl Def {
    /// returns a potentially changed Def if the type matches and "found" string on type mismatch
    /// or Err(None) on an invalid type
    pub fn check_with_type(
        self,
        module: ModuleId,
        scope: ScopeId,
        compiler: &mut Compiler,
        ty: &UnresolvedType,
    ) -> Result<Def, Option<&'static str>> {
        match self {
            Def::Invalid => Ok(Def::Invalid),
            Def::Function(_, _) | Def::Module(_) | Def::GenericType(_) => match ty {
                UnresolvedType::Infer(_) => Ok(self),
                _ => Err(Some("a function")),
            },
            Def::Type(_) => compiler
                .unresolved_matches_primitive(ty, Primitive::Type, module, scope)
                .map_or(Ok(Def::Invalid), |matches| {
                    matches.then_some(self).ok_or(Some("type"))
                }),
            Def::Trait(_, _) => match ty {
                UnresolvedType::Infer(_) => Ok(self),
                _ => Err(Some("a trait")),
            },
            Def::ConstValue(_const_val_id) => {
                todo!("check const value with type")
                /*
                // PERF: cloning ConstValue
                let (const_val, const_val_ty) = compiler.const_values[const_val_id.idx()].clone();
                let ty = compiler.resolve_type(ty, module, scope);
                match const_val.check_with_type(module, scope, compiler, ty)? {
                    None => Ok(self),
                    Some(new_val) => Ok(Def::ConstValue(compiler.add_const_value(new_val))),
                }
                */
            }
            Def::Global(_, _) => todo!("handle globals in constants"),
        }
    }

    pub fn dump(&self, compiler: &Compiler) {
        match self {
            Self::Invalid => print!("<invalid>"),
            Self::Function(module, id) => print!("Function({}, {})", module.idx(), id.idx()),
            Self::GenericType(id) => print!("GenericType({id:?})"),
            Self::Type(ty) => print!("Type({ty:?})"),
            Self::Trait(module, id) => print!("Trait({}, {})", module.idx(), id.idx()),
            Self::ConstValue(value) => {
                let (val, ty) = &compiler.const_values[value.idx()];
                val.dump();
                print!(": {ty}");
            }
            Self::Module(id) => print!("Module({})", id.idx()),
            Self::Global(module, id) => print!("Global({}, {})", module.idx(), id.idx()),
        }
    }

    pub fn get_span(&self, compiler: &mut Compiler) -> Option<Span> {
        match self {
            Self::Invalid => None,
            &Self::Function(module, id) => {
                let ast = compiler.get_module_ast(module);
                Some(ast[ast[id].scope].span.in_mod(module))
            }
            Self::GenericType(_) | Self::Type(_) => todo!("spans of types"),
            &Self::Trait(module, id) => {
                let ast = compiler.get_module_ast(module);
                Some(ast[ast[id].scope].span.in_mod(module))
            }
            Self::ConstValue(_id) => todo!("spans of const values"),
            // maybe better to show reference to module
            &Self::Module(id) => Some(TSpan::MISSING.in_mod(id)),
            &Self::Global(module, id) => {
                let ast = compiler.get_module_ast(module);
                Some(ast[id].span.in_mod(module))
            }
        }
    }
}

pub struct Project {
    pub name: String,
    pub root: PathBuf,
    pub root_module: id::ModuleId,
    pub dependencies: Vec<ProjectId>,
}
pub struct Module {
    pub path: PathBuf,
    pub project: ProjectId,
    pub ast: Option<ParsedModule>,
    pub root: ModuleId,
    pub parent: Option<ModuleId>,
}
impl Module {
    pub fn at_path(
        path: PathBuf,
        project: ProjectId,
        root: ModuleId,
        parent: Option<ModuleId>,
    ) -> Self {
        Self {
            path,
            project,
            ast: None,
            root,
            parent,
        }
    }
}

pub struct ParsedModule {
    pub ast: Rc<Ast>,
    pub child_modules: Vec<ModuleId>,
    pub symbols: ModuleSymbols,
    pub instances: IrInstances,
}

type NamedParams = Box<[(Box<str>, Type, Option<ConstValueId>)]>;

#[derive(Debug)]
pub struct Signature {
    pub params: Box<[(Box<str>, Type)]>,
    pub named_params: NamedParams,
    pub varargs: bool,
    pub return_type: Type,
    pub generics: Generics,
    pub span: TSpan,
}
impl Signature {
    pub fn total_arg_count(&self) -> usize {
        self.params.len() + self.named_params.len()
    }

    pub fn all_params(&self) -> impl Iterator<Item = (&str, &Type)> {
        self.params
            .iter()
            .map(|(name, ty)| (&**name, ty))
            .chain(self.named_params.iter().map(|(name, ty, _)| (&**name, ty)))
    }

    pub fn fits_function_type(&self, ty: &FunctionType) -> Result<bool, InvalidTypeError> {
        if self.generics.count() != 0 {
            return Ok(false);
        }
        if self.varargs {
            return Ok(false);
        }
        if self.params.len() != ty.params.len() {
            return Ok(false);
        }
        for ((_, arg), ty_arg) in self.all_params().zip(&ty.params) {
            if !arg.is_same_as(ty_arg)? {
                return Ok(false);
            }
        }
        if !self.return_type.is_same_as(&ty.return_type)? {
            return Ok(false);
        }
        Ok(true)
    }

    /// used for checking if a function in a trait impl is compatible with a base type.
    /// The signature is allowed to have looser trait bound requirements than the base.
    pub fn compatible_with(
        &self,
        base: &Signature,
        generics_offset: u8,
        base_generics_offset: u8,
        base_generics: &[Type],
    ) -> Result<Option<ImplIncompatibility>, InvalidTypeError> {
        if !self.generics.compatible_with(
            &base.generics,
            generics_offset,
            base_generics_offset,
            base_generics,
        )? {
            return Ok(Some(ImplIncompatibility::Generics));
        }
        if self.varargs != base.varargs {
            return Ok(Some(if base.varargs {
                ImplIncompatibility::VarargsNeeded
            } else {
                ImplIncompatibility::NoVarargsNeeded
            }));
        }
        if self.params.len() != base.params.len() {
            return Ok(Some(ImplIncompatibility::ArgCount {
                base: base.params.len() as _,
                impl_: self.params.len() as _,
            }));
        }
        // TODO: should the default value also be compared?
        for (((_, arg), (_, base_arg)), i) in self.all_params().zip(base.all_params()).zip(0..) {
            if !arg.is_same_as(&base_arg.instantiate_generics(base_generics))? {
                return Ok(Some(ImplIncompatibility::Arg(i)));
            }
        }
        if !self
            .return_type
            .is_same_as(&base.return_type.instantiate_generics(base_generics))?
        {
            return Ok(Some(ImplIncompatibility::ReturnType));
        }
        Ok(None)
    }
}

#[derive(Debug)]
pub struct Generics {
    generics: Vec<(String, Vec<TraitBound>)>,
}
impl Generics {
    pub const EMPTY: Self = Self {
        generics: Vec::new(),
    };

    pub fn count(&self) -> u8 {
        self.generics.len() as u8
    }

    pub fn unify_generic_bound(
        &self,
        generic: u8,
        bound: &Bound,
        types: &mut TypeTable,
        compiler: &mut Compiler,
    ) -> bool {
        let mut found = None;
        for generic_bound in self.generics[generic as usize].1.iter() {
            if bound.trait_id == generic_bound.trait_id {
                assert!(
                    found.is_none(),
                    "TODO: handle multiple potential generic bounds"
                );
                found = Some(generic_bound);
            }
        }
        found.is_some_and(|found| {
            debug_assert_eq!(found.generics.len() as u8, bound.generics.count as u8);
            for (id, ty) in bound.generics.iter().zip(found.generics.iter()) {
                let info = types.generic_info_from_resolved(ty);
                if types.try_specify(id, info, self, compiler).is_err() {
                    return false;
                }
            }
            true
        })
    }

    pub fn instantiate(&self, types: &mut TypeTable, span: TSpan) -> LocalTypeIds {
        let generics = types.add_multiple_unknown(self.generics.len() as _);
        for ((_, bounds), r) in self.generics.iter().zip(generics.iter()) {
            let info = if bounds.is_empty() {
                TypeInfo::Unknown
            } else {
                let bound_ids = types.add_missing_bounds(bounds.len() as _);
                for (bound, r) in bounds.iter().zip(bound_ids.iter()) {
                    // TODO: generic trait bounds, assuming no generics for now
                    let trait_generics = types.add_multiple_unknown(bound.generics.len() as _);
                    for (ty, r) in bound.generics.iter().zip(trait_generics.iter()) {
                        let ty = types.from_generic_resolved(ty, generics);
                        types.replace(r, ty);
                    }
                    let bound = crate::types::Bound {
                        trait_id: bound.trait_id,
                        generics: trait_generics,
                        span,
                    };
                    types.replace_bound(r, bound);
                }
                TypeInfo::UnknownSatisfying(bound_ids)
            };
            types.replace(r, info);
        }
        generics
    }

    pub fn compatible_with(
        &self,
        base: &Self,
        offset: u8,
        base_offset: u8,
        base_generics: &[Type],
    ) -> Result<bool, InvalidTypeError> {
        if self.generics.len() as u8 - offset != base.generics.len() as u8 - base_offset {
            return Ok(false);
        }
        for ((_, bounds), (_, base_bounds)) in self
            .generics
            .iter()
            .skip(offset.into())
            .zip(base.generics.iter().skip(base_offset.into()))
        {
            'bounds: for bound in bounds {
                'base_bounds: for base_bound in base_bounds {
                    if base_bound.trait_id != bound.trait_id {
                        continue;
                    }
                    for (a, b) in base_bound.generics.iter().zip(&bound.generics) {
                        if !a.is_same_as(&b.instantiate_generics(base_generics))? {
                            continue 'base_bounds;
                        }
                    }
                    // bound is satisfied by base_bound
                    continue 'bounds;
                }
                // no base bound satisfies the bound
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[derive(Debug)]
pub struct TraitBound {
    pub trait_id: (ModuleId, TraitId),
    pub generics: Box<[Type]>,
}

#[derive(Debug)]
pub struct ResolvedTypeDef {
    pub def: ResolvedTypeContent,
    pub module: ModuleId,
    pub methods: DHashMap<String, FunctionId>,
    pub generics: Generics,
    pub inherent_trait_impls: DHashMap<(ModuleId, TraitId), Vec<check::traits::Impl>>,
}

#[derive(Debug)]
pub enum ResolvedTypeContent {
    Struct(ResolvedStructDef),
    Enum(ResolvedEnumDef),
}
impl ResolvedTypeContent {
    pub fn uninhabited(
        &self,
        compiler: &mut Compiler,
        generics: &[Type],
    ) -> Result<bool, InvalidTypeError> {
        Ok(match self {
            Self::Struct(struct_def) => struct_def
                .all_fields()
                .try_fold(false, |s, (_, field_ty)| {
                    Ok(s || compiler.uninhabited(field_ty, generics)?)
                })?,
            Self::Enum(enum_def) => {
                enum_def
                    .variants
                    .iter()
                    .try_fold(true, |s, (_, variant_param_types)| {
                        Ok(s && variant_param_types.iter().try_fold(false, |s, ty| {
                            Ok(s || compiler.uninhabited(ty, generics)?)
                        })?)
                    })?
            }
        })
    }
}

#[derive(Debug)]
pub struct ResolvedStructDef {
    pub fields: Box<[(Box<str>, Type)]>,
    pub named_fields: NamedParams,
}
impl ResolvedStructDef {
    pub fn all_fields(&self) -> impl Iterator<Item = (&str, &Type)> {
        self.fields
            .iter()
            .map(|(name, ty)| (&**name, ty))
            .chain(self.named_fields.iter().map(|(name, ty, _)| (&**name, ty)))
    }

    pub fn field_count(&self) -> u32 {
        (self.fields.len() + self.named_fields.len()) as u32
    }

    /// get the index of a field while getting the element types of all fields
    pub fn get_indexed_field(
        &self,
        ctx: &mut crate::check::Ctx,
        generics: LocalTypeIds,
        name: &str,
    ) -> (Option<(u32, LocalTypeId)>, LocalTypeIds) {
        // PERF: Every time we index a struct, all fields are mapped to TypeInfo's
        // again. This could be improved by caching structs somehow ?? or by putting
        // the fields along the TypeDef (easier but would make TypeDef very large,
        // similar problem for enums and extra solution required).
        let elem_types = ctx
            .hir
            .types
            .add_multiple_unknown((self.fields.len() + self.named_fields.len()) as _);
        let mut indexed_field = None;
        for (((field_name, ty), index), r) in self.all_fields().zip(0..).zip(elem_types.iter()) {
            let ty = ctx.type_from_resolved(ty, generics);
            if field_name == name {
                indexed_field = Some((index, r));
            }
            ctx.hir.types.replace(r, ty);
        }
        (indexed_field, elem_types)
    }
}

pub enum ResolvedPrimitive {
    Primitive(Primitive),
    Infer,
    Invalid,
    Other,
}

#[derive(Debug, Clone)]
pub struct ResolvedEnumDef {
    pub variants: Box<[(String, Box<[Type]>)]>,
}
impl ResolvedEnumDef {
    pub fn get_by_name(&self, name: &str) -> Option<(u32, &[Type])> {
        self.variants
            .iter()
            .zip(0..)
            .find_map(|((variant_name, args), ordinal)| {
                (variant_name == name).then_some((ordinal, &**args))
            })
    }
}

pub struct ResolvableTypeDef {
    pub module: ModuleId,
    pub id: ast::TypeId,
    pub name: Box<str>,
    pub generic_count: u8,
    pub resolved: Resolvable<Rc<ResolvedTypeDef>>,
}

#[derive(Debug)]
pub struct ModuleSymbols {
    pub function_signatures: Box<[Resolvable<Rc<Signature>>]>,
    pub functions: Box<[Resolvable<Rc<CheckedFunction>>]>,
    pub types: Box<[Option<TypeId>]>,
    pub globals: Box<[Resolvable<(ConstValue, Type)>]>,
    pub traits: Box<[Resolvable<Rc<CheckedTrait>>]>,
    pub def_exprs: Box<[Resolvable<Def>]>,
}
impl ModuleSymbols {
    fn empty(ast: &Ast) -> Self {
        Self {
            function_signatures: (0..ast.function_count())
                .map(|_| Resolvable::Unresolved)
                .collect(),
            functions: (0..ast.function_count())
                .map(|_| Resolvable::Unresolved)
                .collect(),
            types: vec![None; ast.type_count()].into_boxed_slice(),
            globals: (0..ast.global_count())
                .map(|_| Resolvable::Unresolved)
                .collect(),
            traits: (0..ast.trait_count())
                .map(|_| Resolvable::Unresolved)
                .collect(),
            def_exprs: (0..ast.def_expr_count())
                .map(|_| Resolvable::Unresolved)
                .collect(),
        }
    }
}

#[derive(Debug)]
pub struct CheckedFunction {
    pub name: String,
    pub types: TypeTable,
    pub params: LocalTypeIds,
    pub varargs: bool,
    pub return_type: LocalTypeId,
    pub generic_count: u8,
    pub body: Option<Hir>,
}
impl CheckedFunction {
    pub fn display<'a>(&'a self, compiler: &'a Compiler) -> display::CheckedFunctionDisplay<'a> {
        display::CheckedFunctionDisplay {
            function: self,
            compiler,
        }
    }
}

#[derive(Debug)]
pub struct CheckedTrait {
    pub name: Box<str>,
    pub generics: Generics,
    pub functions: Vec<Signature>,
    pub functions_by_name: DHashMap<String, u16>,
    pub impls: Vec<traits::Impl>,
}

pub struct IrInstances {
    pub functions: Vec<DHashMap<Vec<Type>, ir::FunctionId>>,
    pub globals: Vec<Option<ir::GlobalId>>,
}
impl IrInstances {
    pub fn new(function_count: usize, global_count: usize) -> Self {
        Self {
            functions: vec![dmap::new(); function_count],
            globals: vec![None; global_count],
        }
    }
}

pub struct FunctionToGenerate {
    pub ir_id: ir::FunctionId,
    pub module: ModuleId,
    pub ast_function_id: ast::FunctionId,
    pub generics: Vec<Type>,
}

pub fn mangle_name(checked: &CheckedFunction, generics: &[Type]) -> String {
    let mut name = checked.name.clone();
    if name == "main" {
        name.clear();
        name.push_str("eyemain");
    }
    if !generics.is_empty() {
        // 2 characters per type because of commas and brackets is the minimum
        name.reserve(1 + 2 * generics.len());
        name.push('[');
        let mut first = true;
        for ty in generics {
            if first {
                first = false;
            } else {
                name.push(',');
            }
            use std::fmt::Write;
            write!(name, "{ty}").unwrap();
        }
        name.push(']');
    }
    name
}

pub fn function_name(
    ast: &Ast,
    function: &ast::Function,
    module: ModuleId,
    id: FunctionId,
) -> String {
    if function.associated_name != TSpan::EMPTY {
        ast.src()[function.associated_name.range()].to_owned()
    } else {
        // If no name is associated, assign a name based on unique ids.
        // This will be the case for lambdas right now, maybe a better name is possible
        format!("function_{}_{}", module.idx(), id.idx())
    }
}

pub struct SignatureError;
