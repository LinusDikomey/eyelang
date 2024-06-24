pub mod builtins;

use std::{
    collections::VecDeque,
    path::{Path, PathBuf},
    rc::Rc,
};

use dmap::DHashMap;
use id::{ConstValueId, ModuleId, ProjectId, TypeId};
use span::{IdentPath, Span, TSpan};
use types::{Primitive, Type, UnresolvedType};

use crate::{
    check,
    error::{CompileError, Error, Errors},
    eval::{self, ConstValue},
    hir::HIR,
    irgen,
    parser::{
        self,
        ast::{self, Ast, FunctionId, GlobalId, ScopeId},
    },
    types::{traits, LocalTypeId, LocalTypeIds, TypeInfoOrIdx, TypeTable},
    MainError,
};

use builtins::Builtins;

pub struct Compiler {
    projects: Vec<Project>,
    pub modules: Vec<Module>,
    pub const_values: Vec<ConstValue>,
    pub types: Vec<ResolvableTypeDef>,
    pub ir_module: ir::Module,
    pub errors: Errors,
    pub builtins: Builtins,
}
impl Compiler {
    pub fn new() -> Self {
        Self {
            projects: Vec::new(),
            modules: Vec::new(),
            const_values: Vec::new(),
            types: Vec::new(),
            ir_module: ir::Module {
                name: "main_module".to_owned(),
                funcs: Vec::new(),
                globals: Vec::new(),
            },
            errors: Errors::new(),
            builtins: Builtins::default(),
        }
    }

    pub fn add_project(&mut self, name: String, root: PathBuf) -> Result<ProjectId, MainError> {
        let root = root.canonicalize().unwrap_or(root);
        if !root
            .try_exists()
            .map_err(|err| MainError::CantAccessPath(err, root.clone()))?
        {
            return Err(MainError::NonexistentPath(root));
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

    pub fn add_type_def(&mut self, module: ModuleId, id: ast::TypeId, name: Box<str>) -> TypeId {
        Self::add_type_def_to_types(module, id, name, &mut self.types)
    }

    pub fn add_type_def_to_types(
        module: ModuleId,
        id: ast::TypeId,
        name: Box<str>,
        types: &mut Vec<ResolvableTypeDef>,
    ) -> TypeId {
        let type_id = TypeId(types.len() as _);
        types.push(ResolvableTypeDef {
            module,
            id,
            name,
            resolved: Resolvable::Unresolved,
        });
        type_id
    }

    pub fn add_const_value(&mut self, value: ConstValue) -> ConstValueId {
        let id = ConstValueId(self.const_values.len() as _);
        self.const_values.push(value);
        id
    }

    pub fn get_project(&self, id: ProjectId) -> &Project {
        &self.projects[id.idx()]
    }

    pub fn get_root_module(&self, module: ModuleId) -> ModuleId {
        self.modules[module.idx()].root
    }

    pub fn get_module_ast(&mut self, module_id: ModuleId) -> &Rc<Ast> {
        &self.get_module_ast_and_symbols(module_id).ast
    }

    pub fn get_module_ast_and_symbols(&mut self, module_id: ModuleId) -> &mut ParsedModule {
        if self.modules[module_id.idx()].ast.is_some() {
            // borrowing bullshit
            let Some(parsed) = &mut self.modules[module_id.idx()].ast else {
                unreachable!()
            };
            parsed
        } else {
            let module = &mut self.modules[module_id.idx()];
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
                if !module.path.is_dir() {
                    // We canonicalized the path, this shouldn't really happen. Maybe still add an
                    // error for it.
                    panic!(
                        "project at {} is not a directory or file",
                        module.path.display()
                    );
                }
                let is_root = module_id == module.root;
                let file = if is_root {
                    module.path.join("main.eye")
                } else {
                    module.path.join("mod.eye")
                };
                if !(file.exists() && file.is_file()) {
                    panic!("File {} doesn't exist", file.display());
                    // return Err(MainError::NoMainFileInProjectDirectory);
                };
                let root = module.root;
                let project = module.project;
                // gather child modules, insert them into the definitions and create Modules for them
                let dir_read = self.modules[module_id.idx()]
                    .path
                    .read_dir()
                    .expect("couldn't read module directory");
                for entry in dir_read {
                    let entry = entry.expect("failed to read module directory entry");
                    let ty = entry
                        .file_type()
                        .expect("failed to access file type of module directory entry");
                    let path = entry.path();
                    if ty.is_file() {
                        if path.extension().is_some_and(|ext| ext == "eye") {
                            let name = path
                                .with_extension("")
                                .file_name()
                                .and_then(|name| name.to_str())
                                .expect("file doesn't have a valid name")
                                .to_owned();
                            if !matches!(name.as_str(), "main" | "mod") {
                                let id = ModuleId(self.modules.len() as _);
                                self.modules.push(Module::at_path(
                                    path,
                                    project,
                                    root,
                                    Some(module_id),
                                ));
                                definitions.insert(name, ast::Definition::Module(id));
                                child_modules.push(id);
                            }
                        }
                    } else if ty.is_dir() {
                        let path = entry.path();
                        if path.join("mod.eye").exists() {
                            let name = path
                                .file_name()
                                .and_then(|name| name.to_str())
                                .expect("directory doesn't have a valid name")
                                .to_owned();
                            let id = ModuleId(self.modules.len() as _);
                            self.modules.push(Module::at_path(
                                path,
                                project,
                                root,
                                Some(module_id),
                            ));
                            definitions.insert(name, ast::Definition::Module(id));
                            child_modules.push(id);
                        }
                    }
                }
                let s = std::fs::read_to_string(&file);
                self.modules[module_id.idx()].path = file;
                s
            };
            let source = match contents {
                Ok(source) => source,
                Err(err) => panic!(
                    "compiler failed to open the file {}: {:?}",
                    self.modules[module_id.idx()].path.display(),
                    err,
                ),
            };

            // TODO: handle errors, don't just create them here and ignore them
            let mut errors = Errors::new();
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
        let ast = self.get_module_ast(module).clone();
        let Some(def) = ast[scope].definitions.get(name) else {
            return None;
        };
        let def = match def {
            ast::Definition::Expr { value, ty } => {
                let value = *value;
                // TODO: cache results
                eval::def_expr(self, module, scope, &ast, value, name, &ty)
            }
            &ast::Definition::Path(path) => self.resolve_path(module, scope, path),
            ast::Definition::Global(id) => Def::Global(module, *id),
            &ast::Definition::Module(id) => Def::Module(id),
            &ast::Definition::Generic(i) => Def::Type(Type::Generic(i)),
        };
        Some(def)
    }

    pub fn resolve_path(&mut self, module: ModuleId, scope: ScopeId, path: IdentPath) -> Def {
        let ast = self.get_module_ast(module).clone();
        let (root, segments, last) = path.segments(ast.src());
        let mut scope = Some(scope);
        let mut current_module = module;
        if root.is_some() {
            let module = &self.modules[current_module.idx()];
            current_module = module.root;
            scope = None;
        }
        for (name, name_span) in segments {
            let scope_id =
                scope.unwrap_or_else(|| self.get_module_ast(module).top_level_scope_id());
            match self.resolve_in_scope(current_module, scope_id, name, name_span.in_mod(module)) {
                Def::Module(new_mod) => {
                    current_module = new_mod;
                    scope = None;
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
        let scope_id = scope.unwrap_or_else(|| self.get_module_ast(module).top_level_scope_id());
        self.resolve_in_scope(current_module, scope_id, name, name_span.in_mod(module))
    }

    pub fn resolve_type(&mut self, ty: &UnresolvedType, module: ModuleId, scope: ScopeId) -> Type {
        match ty {
            &UnresolvedType::Primitive { ty, .. } => Type::Primitive(ty),
            UnresolvedType::Unresolved(path, generics) => {
                match self.resolve_path(module, scope, *path) {
                    Def::Type(ty) => match ty {
                        Type::Invalid => Type::Invalid,
                        Type::DefId {
                            id,
                            generics: existing_generics,
                        } => {
                            let generics = match (existing_generics, generics) {
                                (Some(generics), None) => Some(generics),
                                (None, Some((generics, _span))) => {
                                    let generics = generics
                                        .iter()
                                        .map(|ty| self.resolve_type(ty, module, scope))
                                        .collect();
                                    // TODO: check correct generics count
                                    Some(generics)
                                }
                                (None, None) => {
                                    let def = self.get_resolved_type_def(id);
                                    if def.generic_count != 0 {
                                        let count = def.generic_count;
                                        let span = path.span().in_mod(module);
                                        self.errors.emit_err(
                                            Error::InvalidGenericCount {
                                                expected: count,
                                                found: 0,
                                            }
                                            .at_span(span),
                                        );
                                        Some(
                                            std::iter::repeat(Type::Invalid)
                                                .take(count as usize)
                                                .collect(),
                                        )
                                    } else {
                                        Some([].into())
                                    }
                                }
                                (Some(_), Some((_, span))) => {
                                    self.errors.emit_err(
                                        Error::UnexpectedGenerics.at_span(span.in_mod(module)),
                                    );
                                    return Type::Invalid;
                                }
                            };
                            Type::DefId { id, generics }
                        }
                        other => {
                            if let Some((_, span)) = generics {
                                self.errors.emit_err(
                                    Error::UnexpectedGenerics.at_span(span.in_mod(module)),
                                );
                                Type::Invalid
                            } else {
                                other
                            }
                        }
                    },
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
    ) -> Result<Option<Primitive>, ()> {
        match ty {
            &UnresolvedType::Primitive { ty, .. } => Ok(Some(ty)),
            &UnresolvedType::Unresolved(path, None) => {
                match self.resolve_path(module, scope, path) {
                    Def::Invalid => Err(()), // TODO: handle this seperately
                    Def::Type(Type::Primitive(p)) => Ok(Some(p)),
                    _ => Err(()),
                }
            }
            UnresolvedType::Infer(_) => Ok(None),
            _ => Err(()),
        }
    }

    pub fn unresolved_matches_primitive(
        &mut self,
        ty: &UnresolvedType,
        primitive: Primitive,
        module: ModuleId,
        scope: ScopeId,
    ) -> bool {
        match self.unresolved_primitive(ty, module, scope) {
            Ok(None) => true,
            Ok(Some(p)) => p == primitive,
            Err(()) => false,
        }
    }

    pub fn get_signature(&mut self, module: ModuleId, id: ast::FunctionId) -> &Rc<Signature> {
        let parsed = self.modules[module.idx()].ast.as_ref().unwrap();
        match &parsed.symbols.function_signatures[id.idx()] {
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
                let ast = parsed.ast.clone();
                let function = &ast[id];
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

    fn check_signature(
        &mut self,
        function: &ast::Function,
        module: ModuleId,
        ast: &Ast,
    ) -> Signature {
        let scope = function.scope;
        let generics = function
            .generics
            .iter()
            .map(|def| def.name(ast.src()).to_owned())
            .collect();

        let args = function
            .params
            .clone()
            .into_iter()
            .map(|(name_span, ty)| {
                (
                    ast[name_span].to_owned(),
                    self.resolve_type(&ty, module, scope),
                )
            })
            .collect();
        let return_type = self.resolve_type(&function.return_type, module, scope);
        Signature {
            args,
            varargs: function.varargs,
            return_type,
            generics,
            span: function.signature_span,
        }
    }

    /// returns None when the trait can't be resolved, an error was already emitted in that case
    pub fn get_checked_trait(
        &mut self,
        module: ModuleId,
        id: ast::TraitId,
    ) -> Option<&Rc<CheckedTrait>> {
        let parsed = self.get_module_ast_and_symbols(module);
        match &parsed.symbols.traits[id.idx()] {
            Resolvable::Resolved(_) => {
                // borrowing bullshit
                let Resolvable::Resolved(checked) =
                    &self.get_module_ast_and_symbols(module).symbols.traits[id.idx()]
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
                let def = &ast[id];
                // don't include self type in generic count
                let generics = def.generics.len() as u8 - 1;
                let mut functions_by_name = dmap::with_capacity(def.functions.len());
                let functions: Vec<Signature> = def
                    .functions
                    .iter()
                    .zip(0..)
                    .map(|((name_span, function), function_index)| {
                        let name = ast[*name_span].to_owned();
                        let prev = functions_by_name.insert(name, function_index);
                        if prev.is_some() {
                            self.errors.emit_err(
                                Error::DuplicateDefinition.at_span(name_span.in_mod(module)),
                            );
                        }
                        self.check_signature(function, module, &ast)
                    })
                    .collect();
                let impls = def
                    .impls
                    .iter()
                    .map(|(impl_generics, generic_count, impl_ty, impl_functions)| {
                        let generic_count = *generic_count;
                        // don't count the Self type as a generic
                        let impl_ty = self.resolve_type(impl_ty, module, *impl_generics);
                        let impl_ty = traits::ImplTree::from_type(&impl_ty, self);
                        let mut functions = vec![ast::FunctionId(u32::MAX); functions.len()];
                        for &(name_span, function) in impl_functions {
                            let name = &ast[name_span];
                            let Some(&function_idx) = functions_by_name.get(name) else {
                                self.errors.emit_err(
                                    Error::NotATraitMember {
                                        trait_name: "TODO(trait_name)".to_owned(),
                                        function: name.to_owned(),
                                    }
                                    .at_span(name_span.in_mod(module)),
                                );
                                continue;
                            };
                            if functions[function_idx as usize].0 != u32::MAX {
                                self.errors.emit_err(
                                    Error::DuplicateDefinition.at_span(name_span.in_mod(module)),
                                );
                                continue;
                            }
                            // TODO: check impl signature
                            functions[function_idx as usize] = function;
                        }
                        traits::Impl {
                            generic_count,
                            impl_ty,
                            impl_module: module,
                            functions,
                        }
                    })
                    .collect();
                Some(
                    self.get_module_ast_and_symbols(module).symbols.traits[id.idx()].put(Rc::new(
                        CheckedTrait {
                            generics,
                            functions,
                            functions_by_name,
                            impls,
                        },
                    )),
                )
            }
        }
    }

    pub fn get_hir(&mut self, module: ModuleId, id: ast::FunctionId) -> &CheckedFunction {
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
                let resolving = &mut self.modules[module.idx()]
                    .ast
                    .as_mut()
                    .unwrap()
                    .symbols
                    .functions[id.idx()];
                *resolving = Resolvable::Resolving;
                let ast = self.modules[module.idx()].ast.as_ref().unwrap().ast.clone();

                let function = &ast[id];

                let name = if function.associated_name != TSpan::EMPTY {
                    ast.src()[function.associated_name.range()].to_owned()
                } else {
                    // If no name is associated, assign a name based on unique ids.
                    // This will be the case for lambdas right now, maybe a better name is possible
                    format!("function_{}_{}", module.idx(), id.idx())
                };

                self.get_signature(module, id);
                // signature is resolved above
                let Resolvable::Resolved(signature) = &self.modules[module.idx()]
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

                let param_types = types.add_multiple_unknown(signature.args.len() as u32);
                for ((_, param), r) in signature.args.iter().zip(param_types.iter()) {
                    let i = TypeInfoOrIdx::TypeInfo(types.generic_info_from_resolved(self, param));
                    types.replace(r, i);
                }

                let return_type = types.generic_info_from_resolved(self, &signature.return_type);
                let return_type = types.add(return_type);

                let generic_count = signature.generics.len().try_into().unwrap();
                let varargs = signature.varargs;

                let (body, types) = if let Some(body) = function.body {
                    let args = signature
                        .args
                        .iter()
                        .map(|(name, _ty)| name.clone())
                        .zip(param_types.iter());

                    let (hir, types) = check::check(
                        self,
                        &ast,
                        module,
                        types,
                        function.scope,
                        args,
                        body,
                        return_type,
                    );
                    (Some(hir), types)
                } else {
                    (None, types)
                };

                let checked = CheckedFunction {
                    name,
                    types,
                    params: param_types,
                    varargs,
                    return_type,
                    generic_count,
                    body,
                };
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

    pub fn get_resolved_type_def(&mut self, ty: TypeId) -> &ResolvedType {
        match &self.types[ty.idx()].resolved {
            Resolvable::Resolved(_) => {
                // borrowing bullshit
                let Resolvable::Resolved(id) = &self.types[ty.idx()].resolved else {
                    unreachable!()
                };
                id
            }
            Resolvable::Resolving => panic!("recursive type definition"),
            Resolvable::Unresolved => {
                let resolved_ty = &self.types[ty.idx()];
                let module = resolved_ty.module;
                let ast_id = resolved_ty.id;
                let ast = Rc::clone(self.get_module_ast(module));
                let def = &ast[ast_id];
                let generic_count = def.generic_count();
                let methods;
                let def = match def {
                    ast::TypeDef::Struct(struct_def) => {
                        let fields = struct_def
                            .members
                            .iter()
                            .map(|(name_span, ty)| {
                                (
                                    ast[*name_span].to_owned(),
                                    self.resolve_type(ty, module, struct_def.scope),
                                )
                            })
                            .collect();
                        methods = struct_def.methods.clone();
                        ResolvedTypeDef::Struct(ResolvedStructDef { fields })
                    }
                    ast::TypeDef::Enum(def) => {
                        methods = def.methods.clone();
                        let variants = def
                            .variants
                            .iter()
                            .map(|variant| {
                                let variant_name = ast[variant.name_span].to_owned();
                                let args = variant
                                    .args
                                    .iter()
                                    .map(|ty| self.resolve_type(ty, module, def.scope))
                                    .collect();
                                (variant_name, args)
                            })
                            .collect();

                        ResolvedTypeDef::Enum(ResolvedEnumDef { variants })
                    }
                };
                let resolved = ResolvedType {
                    generic_count,
                    def: Rc::new(def),
                    module,
                    methods,
                };
                self.types[ty.idx()].resolved.put(resolved)
            }
        }
    }

    pub fn get_checked_global(&mut self, module: ModuleId, id: GlobalId) -> &(Type, ConstValue) {
        let parsed = self.get_module_ast_and_symbols(module);
        let ast = parsed.ast.clone();
        match &parsed.symbols.globals[id.idx()] {
            Resolvable::Resolved(_) => {
                let Resolvable::Resolved(global) =
                    &self.get_module_ast_and_symbols(module).symbols.globals[id.idx()]
                else {
                    unreachable!()
                };
                global
            }
            Resolvable::Resolving => {
                let span = ast[id].span.in_mod(module);
                self.errors
                    .emit_err(Error::RecursiveDefinition.at_span(span));
                self.get_module_ast_and_symbols(module).symbols.globals[id.idx()]
                    .put((Type::Invalid, ConstValue::Undefined))
            }
            Resolvable::Unresolved => {
                parsed.symbols.globals[id.idx()] = Resolvable::Resolving;
                let global = &ast[id];
                let (val, ty) = if let Some(val) = global.val {
                    let const_value = match eval::def_expr(
                        self,
                        module,
                        global.scope,
                        &ast,
                        val,
                        &global.name,
                        &global.ty,
                    ) {
                        Def::ConstValue(id) => self.const_values[id.idx()].clone(),
                        _ => {
                            let error =
                                Error::ExpectedValue.at_span(ast[val].span_in(&ast, module));
                            self.errors.emit_err(error);
                            ConstValue::Undefined
                        }
                    };
                    let value = const_value.check_with_type(module, global.scope, self, &global.ty);
                    let val = match value {
                        Ok(None) => const_value,
                        Ok(Some(value)) => value,
                        Err(found) => {
                            let mut expected = String::new();
                            global.ty.to_string(&mut expected, ast.src());
                            self.errors.emit_err(
                                Error::MismatchedType {
                                    expected,
                                    found: found.to_owned(),
                                }
                                .at_span(ast[val].span(&ast).in_mod(module)),
                            );
                            ConstValue::Undefined
                        }
                    };
                    let ty = val.ty();
                    (val, ty)
                } else {
                    (
                        ConstValue::Undefined,
                        self.resolve_type(&global.ty, module, global.scope),
                    )
                };
                self.modules[module.idx()]
                    .ast
                    .as_mut()
                    .unwrap()
                    .symbols
                    .globals[id.idx()]
                .put((ty, val))
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
                    match def {
                        &ast::Definition::Path(path) => {
                            // TODO: cache results
                            self.resolve_path(module, scope, path);
                        }
                        ast::Definition::Expr { value, ty } => {
                            // TODO: cache results
                            eval::def_expr(self, module, scope, &ast, *value, name, ty);
                        }
                        &ast::Definition::Module(id) => {
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

            for id in ast.function_ids() {
                self.get_hir(module, id);
            }

            for id in ast.type_ids() {
                let id = match &mut self.modules[module.idx()]
                    .ast
                    .as_mut()
                    .unwrap()
                    .symbols
                    .types[id.idx()]
                {
                    Some(id) => *id,
                    ty @ None => {
                        let id = Self::add_type_def_to_types(
                            module,
                            id,
                            "<anonymous type>".into(),
                            &mut self.types,
                        );
                        *ty = Some(id);
                        id
                    }
                };
                self.get_resolved_type_def(id);
            }

            for id in ast.global_ids() {
                self.get_checked_global(module, id);
            }
        }
    }

    pub fn get_ir_function_id(
        &mut self,
        module: ModuleId,
        function: ast::FunctionId,
        generics: Vec<Type>,
    ) -> ir::FunctionId {
        self.get_module_ast_and_symbols(module);
        let instances = &mut self.modules[module.idx()].ast.as_mut().unwrap().instances;

        let potential_id = ir::FunctionId(self.ir_module.funcs.len() as _);
        match instances.get_or_insert(function, &generics, potential_id) {
            Some(id) => id,
            None => {
                // FIXME: just adding a dummy function right now, stupid solution and might cause issues
                self.ir_module.funcs.push(ir::Function {
                    name: String::new(),
                    types: ir::IrTypes::new(),
                    params: ir::TypeRefs::EMPTY,
                    return_type: ir::IrType::Unit,
                    varargs: false,
                    ir: None,
                });
                let mut to_generate = vec![FunctionToGenerate {
                    ir_id: potential_id,
                    module,
                    ast_function_id: function,
                    generics,
                }];
                while let Some(f) = to_generate.pop() {
                    self.get_hir(f.module, f.ast_function_id);
                    // got checked function above
                    let symbols = &self.modules[f.module.idx()].ast.as_mut().unwrap().symbols;
                    let Resolvable::Resolved(checked) = &symbols.functions[f.ast_function_id.idx()]
                    else {
                        unreachable!()
                    };
                    let checked = Rc::clone(checked);
                    // TODO: generics in function name
                    let mut name = checked.name.clone();
                    if name == "main" {
                        name.clear();
                        name.push_str("eyemain");
                    }
                    if !f.generics.is_empty() {
                        // 2 characters per type because of commas and brackets is the minimum
                        name.reserve(1 + 2 * f.generics.len());
                        name.push('[');
                        let mut first = true;
                        for ty in &f.generics {
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

                    let func =
                        irgen::lower_function(self, &mut to_generate, name, &checked, &f.generics);
                    self.ir_module[f.ir_id] = func;
                }
                potential_id
            }
        }
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
                hir.dump(self);
            }
            module_queue.extend(
                self.get_module_ast_and_symbols(module)
                    .child_modules
                    .iter()
                    .copied(),
            )
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

    /// Emit the ir for all top-level functions in a project and functions called by them.
    pub fn emit_whole_project_ir(&mut self, project: ProjectId) {
        let project = self.get_project(project);
        let mut module_queue = VecDeque::from([project.root_module]);
        while let Some(module) = module_queue.pop_front() {
            let functions = self.get_module_ast(module).function_ids();
            for function in functions {
                self.emit_ir_from_root((module, function));
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
            let main_signature = self.get_signature(main.0, main.1);
            let entry_point = irgen::entry_point(main_ir_id, &main_signature.return_type);
            let id = ir::FunctionId(self.ir_module.funcs.len() as _);
            self.ir_module.funcs.push(entry_point);
            id
        })
    }

    pub fn get_ir_function(&self, id: ir::FunctionId) -> &ir::Function {
        if self.ir_module[id].ir.is_none() {
            // might be a function that is not emitted yet
        }
        &self.ir_module[id]
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
                crate::error::print(
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
}

#[derive(Debug, Default)]
pub enum Resolvable<T> {
    #[default]
    Unresolved,
    Resolving,
    Resolved(T),
}
impl<T> Resolvable<T> {
    fn put(&mut self, resolved: T) -> &mut T {
        *self = Self::Resolved(resolved);
        let Self::Resolved(resolved) = self else {
            // SAFETY: was just set to resolved variant and we have unique access
            unsafe { std::hint::unreachable_unchecked() }
        };
        resolved
    }
}

id::id!(VarId);

pub struct LocalScope<'p> {
    pub parent: Option<&'p LocalScope<'p>>,
    pub variables: DHashMap<String, VarId>,
    pub module: ModuleId,
    /// should only be none if this scope has a parent
    pub static_scope: Option<ScopeId>,
}
pub enum LocalItem {
    Var(VarId),
    Def(Def),
    Invalid,
}
impl<'p> LocalScope<'p> {
    pub fn resolve(&self, name: &str, name_span: TSpan, compiler: &mut Compiler) -> LocalItem {
        if let Some(var) = self.variables.get(name) {
            LocalItem::Var(*var)
        } else if let Some(def) = self
            .static_scope
            .and_then(|static_scope| compiler.get_scope_def(self.module, static_scope, name))
        {
            LocalItem::Def(def)
        } else if let Some(parent) = self.parent {
            parent.resolve(name, name_span, compiler)
        } else if let Some(static_parent) = self
            .static_scope
            .and_then(|static_scope| compiler.get_module_ast(self.module)[static_scope].parent)
        {
            LocalItem::Def(compiler.resolve_in_scope(
                self.module,
                static_parent,
                name,
                name_span.in_mod(self.module),
            ))
        } else {
            compiler
                .errors
                .emit_err(Error::UnknownIdent(name.into()).at_span(name_span.in_mod(self.module)));
            LocalItem::Invalid
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
            current_local = current_local.parent.unwrap();
        }
    }
}

#[derive(Clone, Debug)]
pub enum Def {
    Invalid,
    Function(ModuleId, ast::FunctionId),
    Type(Type),
    Trait(ModuleId, ast::TraitId),
    ConstValue(ConstValueId),
    Module(ModuleId),
    Global(ModuleId, GlobalId),
}
impl Def {
    /// returns a potentially changed Def if the type matches and "found" string on type mismatch
    pub fn check_with_type(
        self,
        module: ModuleId,
        scope: ScopeId,
        compiler: &mut Compiler,
        ty: &UnresolvedType,
    ) -> Result<Def, &'static str> {
        match self {
            Def::Invalid => Ok(Def::Invalid),
            Def::Function(_, _) | Def::Module(_) => match ty {
                UnresolvedType::Infer(_) => Ok(self),
                _ => Err("a function"),
            },
            Def::Type(_) => {
                return compiler
                    .unresolved_matches_primitive(ty, Primitive::Type, module, scope)
                    .then_some(self)
                    .ok_or("type")
            }
            Def::Trait(_, _) => match ty {
                UnresolvedType::Infer(_) => Ok(self),
                _ => Err("a trait"),
            },
            Def::ConstValue(const_val_id) => {
                // PERF: cloning ConstValue but it might be fine
                let const_val = compiler.const_values[const_val_id.idx()].clone();
                match const_val.check_with_type(module, scope, compiler, ty)? {
                    None => Ok(self),
                    Some(new_val) => Ok(Def::ConstValue(compiler.add_const_value(new_val))),
                }
            }
            Def::Global(_, _) => todo!("handle globals in constants"),
        }
    }

    pub fn dump(&self, compiler: &Compiler) {
        match self {
            Self::Invalid => print!("<invalid>"),
            Self::Function(module, id) => print!("Function({}, {})", module.idx(), id.idx()),
            Self::Type(ty) => print!("Type({:?})", ty),
            Self::Trait(module, id) => print!("Trait({}, {})", module.idx(), id.idx()),
            Self::ConstValue(value) => compiler.const_values[value.idx()].dump(),
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
            Self::Type(_ty) => todo!("spans of types"),
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
    pub dependencies: Vec<id::ProjectId>,
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

#[derive(Debug)]
pub struct Signature {
    pub args: Vec<(String, Type)>,
    pub varargs: bool,
    pub return_type: Type,
    pub generics: Vec<String>,
    pub span: TSpan,
}

#[derive(Debug)]
pub struct ResolvedType {
    pub generic_count: u8,
    /// PERF: could put the specific vecs with variants/members into an Rc and avoid one level of
    /// indirection
    pub def: Rc<ResolvedTypeDef>,
    pub module: ModuleId,
    pub methods: DHashMap<String, FunctionId>,
}

#[derive(Debug)]
pub enum ResolvedTypeDef {
    Struct(ResolvedStructDef),
    Enum(ResolvedEnumDef),
}

#[derive(Debug)]
pub struct ResolvedStructDef {
    pub fields: Vec<(String, Type)>,
}
impl ResolvedStructDef {
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
        let elem_types = ctx.hir.types.add_multiple_unknown(self.fields.len() as _);
        let mut indexed_field = None;
        let fields = self.fields.iter().zip(0..).zip(elem_types.iter());
        for (((field_name, ty), index), r) in fields {
            let ty = ctx.type_from_resolved(ty, generics);
            if field_name == name {
                indexed_field = Some((index, r));
            }
            ctx.hir.types.replace(r, ty);
        }
        (indexed_field, elem_types)
    }
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
    module: ModuleId,
    id: ast::TypeId,
    name: Box<str>,
    resolved: Resolvable<ResolvedType>,
}

#[derive(Debug)]
pub struct ModuleSymbols {
    pub function_signatures: Vec<Resolvable<Rc<Signature>>>,
    pub functions: Vec<Resolvable<Rc<CheckedFunction>>>,
    pub types: Vec<Option<TypeId>>,
    pub globals: Vec<Resolvable<(Type, ConstValue)>>,
    pub traits: Vec<Resolvable<Rc<CheckedTrait>>>,
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
            types: vec![None; ast.type_count()],
            globals: (0..ast.global_count())
                .map(|_| Resolvable::Unresolved)
                .collect(),
            traits: (0..ast.trait_count())
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
    pub body: Option<HIR>,
}
impl CheckedFunction {
    pub fn dump(&self, compiler: &Compiler) {
        eprint!("BEGIN HIR {}(", self.name);
        for (i, param) in self.params.iter().enumerate() {
            if i != 0 {
                eprint!(", ");
            }
            self.types.dump_type(compiler, param);
        }
        eprint!(")\n  ");
        match &self.body {
            Some(body) => {
                body.dump(body.root_id(), compiler, &self.types, 1);
            }
            None => {
                eprintln!("  <extern>");
            }
        }
        eprintln!("\nEND HIR\n");
    }
}

#[derive(Debug)]
pub struct CheckedTrait {
    pub generics: u8,
    pub functions: Vec<Signature>,
    pub functions_by_name: DHashMap<String, u16>,
    pub impls: Vec<traits::Impl>,
}

pub struct IrInstances {
    functions: Vec<FunctionInstances>,
    pub globals: Vec<Option<ir::GlobalId>>,
}
impl IrInstances {
    pub fn new(function_count: usize, global_count: usize) -> Self {
        Self {
            functions: vec![FunctionInstances(dmap::new()); function_count],
            globals: vec![None; global_count],
        }
    }

    pub fn get_or_insert(
        &mut self,
        id: FunctionId,
        generics: &[Type],
        potential_ir_id: ir::FunctionId,
    ) -> Option<ir::FunctionId> {
        let instances = &mut self.functions[id.idx()].0;
        match instances.get(generics) {
            None => {
                // PERF: avoid double hashing, maybe with RawEntry
                instances.insert(generics.to_owned(), potential_ir_id);
                None
            }
            Some(id) => Some(*id),
        }
    }
}

pub struct FunctionToGenerate {
    pub ir_id: ir::FunctionId,
    pub module: ModuleId,
    pub ast_function_id: ast::FunctionId,
    pub generics: Vec<Type>,
}

#[derive(Clone)]
struct FunctionInstances(DHashMap<Vec<Type>, ir::FunctionId>);
