use std::{path::PathBuf, rc::Rc, collections::VecDeque};

use dmap::DHashMap;
use id::{ProjectId, ModuleId, TypeId, ConstValueId};
use span::{Span, IdentPath, TSpan};
use types::{UnresolvedType, Type};

use crate::{eval::{ConstValue, self}, error::{CompileError, Errors, Error}, parser::{ast::{self, Ast, ScopeId, GlobalId, FunctionId}, self}, type_table::{LocalTypeId, TypeTable, LocalTypeIds}, irgen, hir::{HIRBuilder, HIR}, check, MainError};

pub struct Compiler {
    projects: Vec<Project>,
    pub modules: Vec<Module>,
    pub const_values: Vec<ConstValue>,
    pub types: Vec<ResolvableTypeDef>,
    pub ir_module: ir::Module,
    pub errors: Errors,
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
            },
            errors: Errors::new(),
        }
    }

    pub fn add_project(&mut self, name: String, root: PathBuf) -> Result<ProjectId, MainError> {
        let root = root.canonicalize().unwrap_or(root);
        if !root.try_exists().map_err(|err| MainError::CantAccessPath(err, root.clone()))? {
            return Err(MainError::NonexistentPath(root));
        }
        let root_module_path = if root.is_file() {
            root.clone()
        } else {
            if !root.is_dir() {
                // We canonicalized the path, this shouldn't really happen. Maybe still add an
                // error for it.
                panic!("project at {} is not a directory or file", root.display());
            }
            let main_path = root.join("main.eye");
            if !main_path.exists() {
                return Err(MainError::NoMainFileInProjectDirectory);
            }
            main_path
        };
        let root_module_id = ModuleId(self.modules.len() as _);
        self.modules.push(Module::at_path(root_module_path, root_module_id, None));

        let project_id = ProjectId(self.projects.len() as _);
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

    pub fn add_type_def(&mut self, module: ModuleId, id: ast::TypeId) -> TypeId {
        Self::add_type_def_to_types(module, id, &mut self.types)
    }
    pub fn add_type_def_to_types(module: ModuleId, id: ast::TypeId, types: &mut Vec<ResolvableTypeDef>) -> TypeId {
        let type_id = TypeId(types.len() as _);
        types.push(ResolvableTypeDef {
            module,
            id,
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

    pub fn get_module_ast(&mut self, module_id: ModuleId) -> &Rc<Ast> {
        self.get_module_ast_and_symbols(module_id).0
    }

    pub fn get_module_ast_and_symbols(&mut self, module_id: ModuleId) -> (&Rc<Ast>, &mut ModuleSymbols) {
        if self.modules[module_id.idx()].ast.is_some() {
            // borrowing bullshit
            let Some((ast, symbols, _)) = &mut self.modules[module_id.idx()].ast else { unreachable!() };
            (ast, symbols)
        } else {

            let module = &mut self.modules[module_id.idx()];
            let source = match std::fs::read_to_string(&module.path) {
                Ok(source) => source,
                Err(err) => panic!(
                    "compiler failed to open the file {}: {:?}",
                    module.path.display(),
                    err,
                ),
            };

            // TODO: handle errors, don't just create them here and ignore them
            let mut errors = Errors::new();
            let ast = parser::parse(source, &mut errors, module_id);
            let Some(ast) = ast else {
                todo!("handle parsing errors properly: {errors:?}");
            };
            let checked = ModuleSymbols::empty(&ast);
            let module = &mut self.modules[module_id.idx()];
            let instances = IrFunctionInstances::new(ast.function_count());
            module.ast = Some((Rc::new(ast), checked, instances));
            let Some((ast, symbols, _)) = module.ast.as_mut() else { unreachable!() };
            (ast, symbols)
        }
    }

    pub fn resolve_in_module(&mut self, module: ModuleId, name: &str, name_span: Span) -> Def {
        let scope = self.get_module_ast(module).top_level_scope_id();
        self.resolve_in_scope(module, scope, name, name_span)
    }

    pub fn resolve_in_scope(&mut self, module: ModuleId, scope: ScopeId, name: &str, name_span: Span) -> Def {
        self.get_scope_def(module, scope, name).unwrap_or_else(|| {
            if let Some(parent) = self.get_module_ast(module)[scope].parent {
                self.resolve_in_scope(module, parent, name, name_span)
            } else {
                self.errors.emit_err(Error::UnknownIdent.at_span(name_span));
                Def::Invalid
            }
        })
    }

    pub fn get_scope_def(&mut self, module: ModuleId, scope: ScopeId, name: &str) -> Option<Def> {
        let ast = self.get_module_ast(module).clone();
        let Some(def) = ast[scope].definitions.get(name) else { return None };
        let def = match def {
            ast::Definition::Expr { value, ty } => {
                assert!(matches!(ty, UnresolvedType::Infer(_)), "TODO: respect type");
                let value = *value;
                // TODO: cache results
                eval::def_expr(self, module, scope, &ast, value)
            }
            &ast::Definition::Path(path) => {
                self.resolve_path(module, scope, path)
            }
            ast::Definition::Global(id) => Def::Global(module, *id),
            &ast::Definition::Generic(_) => todo!("generic defs"),
        };
        Some(def)
    }

    pub fn resolve_path(
        &mut self,
        module: ModuleId,
        scope: ScopeId,
        path: IdentPath,
    ) -> Def {
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
            let scope_id = scope.unwrap_or_else(|| self.get_module_ast(module).top_level_scope_id());
            match self.resolve_in_scope(current_module, scope_id, name, name_span.in_mod(module)) {
                Def::Module(new_mod) => {
                    current_module = new_mod;
                    scope = None;
                }
                Def::Invalid => return Def::Invalid,
                _ => {
                    self.errors.emit_err(Error::ModuleExpected.at_span(name_span.in_mod(module)));
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
                        Type::DefId { id, generics: existing_generics } => {
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
                                    eprintln!("TODO: remove generics assumption");
                                    Some([].into())
                                }
                                (Some(_), Some((_, span))) => {
                                    self.errors.emit_err(
                                        Error::UnexpectedGenerics.at_span(span.in_mod(module))
                                    );
                                    return Type::Invalid;
                                }
                            };
                            Type::DefId { id, generics }
                        }
                        other => {
                            if let Some((_, span)) = generics {
                                self.errors.emit_err(Error::UnexpectedGenerics.at_span(span.in_mod(module)));
                                Type::Invalid
                            } else {
                                other
                            }
                        }
                    }
                    Def::Invalid => Type::Invalid,
                    _ => {
                        self.errors.emit_err(Error::TypeExpected.at_span(ty.span().in_mod(module)));
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
                let Some(size) = *size else { panic!("inferred array size is not allowed here") };
                Type::Array(Box::new((elem_ty, size)))
            }
            _ => todo!("resolve type {ty:?}"),
        }
    }

    pub fn get_signature(&mut self, module: ModuleId, id: ast::FunctionId) -> &Signature {
        let (ast, checked, _) = self.modules[module.idx()].ast.as_ref().unwrap();
        match &checked.function_signatures[id.idx()] {
            Resolvable::Resolved(_) => {
                // borrowing bullshit
                let Resolvable::Resolved(signature) = &self.modules[module.idx()]
                    .ast.as_ref().unwrap().1.function_signatures[id.idx()]
                else { unreachable!() };
                signature
            }
            Resolvable::Resolving => panic!("function signature depends on itself recursively"),
            Resolvable::Unresolved => {
                let ast = ast.clone();
                let function = &ast[id];
                let scope = function.scope;
                let generics = function.generics
                    .iter()
                    .map(|def| ast[def.name].to_owned())
                    .collect();
    
                let args = function.params
                    .clone()
                    .into_iter()
                    .map(|(name_span, ty)| (
                        ast[name_span].to_owned(),
                        self.resolve_type(&ty, module, scope),
                    ))
                    .collect();
                let return_type = self.resolve_type(&function.return_type, module, scope);
                let signature = Signature {
                    args,
                    varargs: function.varargs,
                    return_type,
                    generics,
                    span: function.signature_span,
                };
                self.modules[module.idx()].ast.as_mut().unwrap().1.function_signatures[id.idx()]
                    .put(signature)
            }
        }
    }

    pub fn get_hir(&mut self, module: ModuleId, id: ast::FunctionId) -> &CheckedFunction {
        let checked = &self.modules[module.idx()].ast.as_ref().unwrap().1;
        match &checked.functions[id.idx()] {
            Resolvable::Resolved(_) => {
                // borrowing bullshit
                let Resolvable::Resolved(checked) = &self.modules[module.idx()].ast
                    .as_ref().unwrap().1.functions[id.idx()] else { unreachable!() };
                checked
            }
            Resolvable::Resolving => panic!("checked function depends on itself recursively"),
            Resolvable::Unresolved => {
                let resolving = &mut self.modules[module.idx()].ast
                    .as_mut().unwrap().1.functions[id.idx()];
                *resolving = Resolvable::Resolving;
                let ast = self.modules[module.idx()].ast.as_ref().unwrap().0.clone();
                let function = &ast[id];
                self.get_signature(module, id);
                // signature is resolved above
                let Resolvable::Resolved(signature) = &self.modules[module.idx()].ast
                    .as_ref().unwrap()
                .1.function_signatures[id.idx()] else { unreachable!() };

                let mut types = TypeTable::new();

                // PERF: could pre-reserve in table and put in directly instead of heap allocating
                let params: Vec<_> = signature.args
                    .iter()
                    .map(|(_, param)| types.info_from_resolved(param))
                    .collect();

                let param_types = types.add_multiple(params);
                let varargs = signature.varargs;

                let return_type = types.from_resolved(&signature.return_type);
                let generic_count = signature.generics.len().try_into().unwrap();

                let (body, types) = if let Some(body) = function.body {
                    let mut hir = HIRBuilder::new(types);
                    let parameter_variables = signature.args
                        .iter()
                        .map(|(name, _)| name)
                        .zip(param_types.iter())
                        .map(|(name, ty)| (name.clone(), hir.add_var(ty)))
                        .collect();
                    let mut scope = LocalScope {
                        parent: None,
                        variables: parameter_variables,
                        module,
                        static_scope: function.scope,
                    };
                    let mut check_ctx = check::Ctx {
                        compiler: self,
                        ast: &ast,
                        module,
                        hir,
                        deferred_exhaustions: Vec::new(),
                        deferred_casts: Vec::new(),
                    };
                    let root = check::check_expr(&mut check_ctx, body, &mut scope,
                        return_type, return_type);
                    let (hir, types) = check_ctx.finish(root);
                    (Some(hir), types)
                } else {
                    (None, types)
                };

                let checked = CheckedFunction {
                    types,
                    params: param_types,
                    varargs,
                    return_type,
                    generic_count,
                    body,
                };
                self.modules[module.idx()].ast.as_mut().unwrap().1.functions[id.idx()]
                    .put(checked)
            }
        }
    }

    pub fn get_resolved_type_def(&mut self, ty: TypeId) -> &ResolvedTypeDef {
        match &self.types[ty.idx()].resolved {
            Resolvable::Resolved(_) => {
                // borrowing bullshit
                let Resolvable::Resolved(id) = &self.types[ty.idx()].resolved else { unreachable!() };
                id
            }
            Resolvable::Resolving => panic!("recursive type definition"),
            Resolvable::Unresolved => {
                let resolved_ty = &self.types[ty.idx()];
                let module = resolved_ty.module;
                let ast_id = resolved_ty.id;
                let ast = self.get_module_ast(module).clone();
                let def = &ast[ast_id];
                let resolved = match def {
                    ast::TypeDef::Struct(struct_def) => {
                        let fields = struct_def.members
                            .iter()
                            .map(|(name_span, ty)| (
                                ast[*name_span].to_owned(),
                                self.resolve_type(ty, module, struct_def.scope)
                            ))
                            .collect();
                        ResolvedTypeDef::Struct(ResolvedStructDef { fields })
                    }
                    ast::TypeDef::Enum(_) => todo!(),
                };
                self.types[ty.idx()].resolved.put(resolved)
            }
        }
    }

    pub fn get_checked_global(&mut self, module: ModuleId, id: GlobalId) -> &(Type, ConstValue) {
        let (ast, symbols) = self.get_module_ast_and_symbols(module);
        let ast = ast.clone();
        match &symbols.globals[id.idx()] {
            Resolvable::Resolved(_) => {
                let Resolvable::Resolved(global) = &self.get_module_ast_and_symbols(module).1
                    .globals[id.idx()] else { unreachable!() };
                global
            }
            Resolvable::Resolving => {
                let span = ast[id].span.in_mod(module);
                self.errors.emit_err(Error::RecursiveDefinition.at_span(span));
                self.get_module_ast_and_symbols(module).1.globals[id.idx()]
                    .put((Type::Invalid, ConstValue::Undefined))
            }
            Resolvable::Unresolved => {
                symbols.globals[id.idx()] = Resolvable::Resolving;
                let global = &ast[id];
                let ty = self.resolve_type(&global.ty, module, global.scope);
                let val = if let Some(val) = global.val {
                    match eval::def_expr(self, module, global.scope, &ast, val) {
                        // probably should just store id instead of cloning the value
                        Def::ConstValue(id) => self.const_values[id.idx()].clone(),
                        _ => {
                            let error = Error::ExpectedValue.at_span(ast[val].span_in(&ast, module));
                            self.errors.emit_err(error);
                            ConstValue::Undefined
                        }
                    }
                } else {
                    ConstValue::Undefined
                };
                self.modules[module.idx()].ast.as_mut().unwrap().1
                    .globals[id.idx()].put((ty, val))
            }
        }
    }

    pub fn check_complete_project(&mut self, project: ProjectId) {
        let root = self.projects[project.idx()].root_module;
        let mut modules_to_check = VecDeque::from([root]);
        while let Some(module) = modules_to_check.pop_front() {
            let ast = self.get_module_ast(module).clone();
            for scope in ast.scope_ids() {
                for def in ast[scope].definitions.values() {
                    match def {
                        &ast::Definition::Path(path) => {
                            // TODO: cache results
                            self.resolve_path(module, scope, path);
                        }
                        ast::Definition::Expr { value, ty } => {
                            assert!(matches!(ty, UnresolvedType::Infer(_)), "TODO: def type annotations");
                            // TODO: cache results
                            eval::def_expr(self, module, scope, &ast, *value);
                        }
                        ast::Definition::Global(_) | ast::Definition::Generic(_) => {}
                    }
                }
            }

            for id in ast.function_ids() {
                self.get_hir(module, id);
            }

            for id in ast.type_ids() {
                let id = match &mut self.modules[module.idx()].ast.as_mut().unwrap().1.types[id.idx()] {
                    Some(id) => *id,
                    ty @ None => {
                        let id = Self::add_type_def_to_types(module, id, &mut self.types);
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
        self.get_module_ast(module);
        let instances = &mut self.modules[module.idx()]
            .ast.as_mut().unwrap().2;

        let potential_id = ir::FunctionId(self.ir_module.funcs.len() as _);
        match instances.get_or_insert(function, &generics, potential_id) {
            Some(id) => id,
            None => {
                // FIXME: just adding a dummy function right now, stupid solution and might cause issues
                self.ir_module.funcs.push(ir::Function {
                    name: String::new(),
                    types: ir::IrTypes::new(),
                    params: vec![],
                    return_type: ir::TypeRef::new(0),
                    varargs: false,
                    ir: None,
                });
                let mut to_generate = vec![(potential_id, module, function, generics)];
                while let Some((id, module, function, generics)) = to_generate.pop() {
                    let ast = self.get_module_ast(module).clone();
                    self.get_hir(module, function);
                    // got checked function above
                    let symbols = &self.modules[module.idx()].ast.as_mut().unwrap().1;
                    let Resolvable::Resolved(checked) = &symbols.functions[function.idx()] else { unreachable!() };
                    // PERF: put CheckedFunction behind Rc
                    let checked = checked.clone();
                    let get_ir_id = |module, id, generics: Vec<_>| {
                        self.get_hir(module, id);
                        let instances = &mut self.modules[module.idx()]
                            .ast.as_mut().unwrap().2;

                        let potential_id = ir::FunctionId(self.ir_module.funcs.len() as _);

                        match instances.get_or_insert(id, &generics, potential_id) {
                            Some(id) => id,
                            None => {
                                // FIXME: just adding a dummy function right now, stupid solution and might cause issues
                                self.ir_module.funcs.push(ir::Function {
                                    name: String::new(),
                                    types: ir::IrTypes::new(),
                                    params: vec![],
                                    return_type: ir::TypeRef::new(0),
                                    varargs: false,
                                    ir: None,
                                });
                                to_generate.push((potential_id, module, id, generics));
                                potential_id
                            }
                        }
                    };
                    let name = format!("function_{}_{}", module.idx(), function.idx());

                    let func = irgen::lower_function(ast.src(), name, &checked, &generics, get_ir_id);
                    self.ir_module[id] = func;
                }
                potential_id
            }
        }
    }

    /// Emit project ir. If main function is provided, all functions required by main will also be
    /// returned. For library projects, main can be set to None and all public functions will be
    /// emitted.
    pub fn emit_project_ir(
        &mut self,
        _project: ProjectId,
        main: Option<(ModuleId, FunctionId)>,
    ) -> Vec<ir::FunctionId> {
        let Some(main) = main else { todo!("emitting libraries is not supported right now") };
        let mut functions_to_emit = VecDeque::from([(main.0, main.1, vec![])]);
        let mut finished_functions = Vec::new();
        while let Some((module, function, generics)) = functions_to_emit.pop_front() {
            let id = self.get_ir_function_id(module, function, generics);
            finished_functions.push(id);
        }

        finished_functions
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
                let path = &self.modules[error.span.module.idx()].path;
                crate::error::print(&error.err, TSpan::new(error.span.start, error.span.end), ast.src(), path);
            }
        };
        let err_count = errors.error_count();
        if err_count != 0 {
            cprintln!("#r<Finished with #u;r!<{}> error{}>",
                err_count, if err_count == 1 { "" } else { "s" });
            for error in &errors.errors {
                print(error);
            }
            return true;
        }
        if errors.warning_count() != 0 {
            let c = errors.warning_count();
            cprintln!("#r<Finished with #u;r!<{}> warning{}>",
                c, if c == 1 { "" } else { "s" });
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
    pub static_scope: ScopeId,
}
pub enum LocalItem {
    Var(VarId),
    Def(Def),
    Invalid,
}
impl<'p> LocalScope<'p> {
    pub fn resolve(&self, name: &str, name_span: TSpan, compiler: &mut Compiler) -> LocalItem {
        eprintln!("Resolving {name} in local scope");
        if let Some(var) = self.variables.get(name) {
            LocalItem::Var(*var)
        } else if let Some(def) = compiler.get_scope_def(self.module, self.static_scope, name) {
            LocalItem::Def(def)
        } else if let Some(parent) = self.parent {
            parent.resolve(name, name_span, compiler)
        } else if let Some(static_parent) = compiler.get_module_ast(self.module)[self.static_scope].parent {
            LocalItem::Def(compiler.resolve_in_scope(self.module, static_parent, name, name_span.in_mod(self.module)))
        } else {
            compiler.errors.emit_err(Error::UnknownIdent.at_span(name_span.in_mod(self.module)));
            LocalItem::Invalid
        }
    }
}

#[derive(Clone, Debug)]
pub enum Def {
    Invalid,
    Function(ModuleId, ast::FunctionId),
    Type(Type),
    ConstValue(ConstValueId),
    Module(ModuleId),
    Global(ModuleId, GlobalId),
}
impl Def {
    pub fn dump(&self, compiler: &Compiler) {
        match self {
            Self::Invalid => print!("<invalid>"),
            Self::Function(module, id) => print!("Function({}, {})", module.idx(), id.idx()),
            Self::Type(ty) => print!("Type({:?})", ty),
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
    pub ast: Option<(Rc<Ast>, ModuleSymbols, IrFunctionInstances)>,
    pub root: ModuleId,
    pub parent: Option<ModuleId>,
}
impl Module {
    pub fn at_path(path: PathBuf, root: ModuleId, parent: Option<ModuleId>) -> Self {
        Self {
            path,
            ast: None,
            root,
            parent,
        }
    }
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
pub enum ResolvedTypeDef {
    Struct(ResolvedStructDef),
}

#[derive(Debug)]
pub struct ResolvedStructDef {
    fields: Vec<(String, Type)>,
}

pub struct ResolvableTypeDef {
    module: ModuleId,
    id: ast::TypeId,
    resolved: Resolvable<ResolvedTypeDef>,
}

#[derive(Debug)]
pub struct ModuleSymbols {
    pub function_signatures: Vec<Resolvable<Signature>>,
    pub functions: Vec<Resolvable<CheckedFunction>>,
    pub types: Vec<Option<TypeId>>,
    pub globals: Vec<Resolvable<(Type, ConstValue)>>,
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
            globals: (0..ast.global_count()).map(|_| Resolvable::Unresolved).collect()
        }
    }
}

#[derive(Debug, Clone)]
pub struct CheckedFunction {
    pub types: TypeTable,
    pub params: LocalTypeIds,
    pub varargs: bool,
    pub return_type: LocalTypeId,
    pub generic_count: u8,
    pub body: Option<HIR>,
}

pub struct IrFunctionInstances {
    functions: Vec<FunctionInstances>,
}
impl IrFunctionInstances {
    pub fn new(function_count: usize) -> Self {
        Self {
            functions: vec![FunctionInstances(dmap::new()); function_count],
        }
    }

    pub fn get_or_insert(&mut self, id: FunctionId, generics: &[Type], potential_ir_id: ir::FunctionId) -> Option<ir::FunctionId> {
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

#[derive(Clone)]
struct FunctionInstances(DHashMap<Vec<Type>, ir::FunctionId>);
