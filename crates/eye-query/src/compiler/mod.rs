use std::{io, path::PathBuf, rc::Rc};

use dmap::DHashMap;
use id::{ProjectId, ModuleId, TypeId, ConstValueId};
use span::{Span, IdentPath, TSpan};
use types::{UnresolvedType, Type, Primitive};

use crate::{eval::{ConstValue, self}, error::{CompileError, Errors, Error}, parser::{ast::{self, Ast, ScopeId, Expr, ExprId, GlobalId}, self, token::IntLiteral}, type_table::{LocalTypeId, TypeInfo, TypeTable}};

pub struct Compiler {
    projects: Vec<Project>,
    pub modules: Vec<Module>,
    pub const_values: Vec<ConstValue>,
    pub types: Vec<ResolvableTypeDef>,
    pub errors: Errors,
}
impl Compiler {
    pub fn new() -> Self {
        Self {
            projects: Vec::new(),
            modules: Vec::new(),
            const_values: Vec::new(),
            types: Vec::new(),
            errors: Errors::new(),
        }
    }

    pub fn add_project(&mut self, name: String, root: PathBuf) -> io::Result<ProjectId> {
        if !root.try_exists()? {
            panic!("invalid project path: {}", root.display());
        }
        let root_module_path = if root.is_file() {
            root.clone()
        } else {
            if !root.is_dir() {
                panic!("project at {} is not a directory or file", root.display());
            }
            let main_path = root.join("main.eye");
            if !main_path.try_exists()? {
                panic!();
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
        let type_id = TypeId(self.types.len() as _);
        self.types.push(ResolvableTypeDef {
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
            let Some((ast, symbols)) = &mut self.modules[module_id.idx()].ast else { unreachable!() };
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
            let Some(ast) = ast else { todo!("handle parsing problems") };
            let checked = ModuleSymbols::empty(&ast);
            let module = &mut self.modules[module_id.idx()];
            module.ast = Some((Rc::new(ast), checked));
            let Some((ast, symbols)) = module.ast.as_mut() else { unreachable!() };
            (ast, symbols)
        }
    }

    pub fn emit_error(&mut self, error: CompileError) {
        self.errors.emit_err(error)
    }

    pub fn resolve_in_module(&mut self, module: ModuleId, name: &str, name_span: Span) -> Def {
        let scope = self.get_module_ast(module).top_level_scope_id();
        self.resolve_in_scope(module, scope, name, name_span)
    }

    pub fn resolve_in_scope(&mut self, module: ModuleId, scope: ScopeId, name: &str, name_span: Span) -> Def {
        eprintln!("resolving in scope {module:?}:{scope:?} -> {name}");
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
        let ast = self.get_module_ast(module);
        let Some(def) = ast[scope].definitions.get(name) else { return None };
        let def = match def {
            ast::Definition::Expr { value, ty, counts: _ } => {
                let value = *value;
                // TODO: check type
                eval::def_expr(self, module, scope, value)
            }
            &ast::Definition::Path(path) => {
                self.resolve_path(module, scope, path)
            }
            ast::Definition::Global(id) => Def::Global(*id),
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

    pub fn resolve_type(&mut self, ty: &UnresolvedType, scope: ScopeId) -> Type {
        match ty {
            &UnresolvedType::Primitive { ty, .. } => Type::Primitive(ty),
            UnresolvedType::Unresolved(_path, _generics) => {
                todo!("resolving path requires source access");
                /*
                let mut current_scope = scope;
                // empty paths shouldn't be possible
                let (last, front_segments) = path.split_last().unwrap();
                for part in front_segments {
                    let def = self.resolve_definition(current_scope, part).expect("unresolved module in type path");
                    match def {
                        Def::Module(id) => current_scope = self.get_module_scope(id),
                        _ => panic!("module expected"),
                    }
                }
                let def = self.resolve_definition(current_scope, last).expect("unresolved type");
                match def {
                    Def::ConstValue(_) => todo!("handle type values"),
                    Def::Type(id) => Type::DefId { id, generics: vec![] },
                    _ => panic!("type expected")
                }
                */
            }
            UnresolvedType::Pointer(b) => {
                let (pointee, _) = &**b;
                Type::Pointer(Box::new(self.resolve_type(pointee, scope)))
            }
            UnresolvedType::Array(b) => {
                let (elem_ty, size, _) = &**b;
                let elem_ty = self.resolve_type(elem_ty, scope);
                let Some(size) = *size else { panic!("inferred array size is not allowed here") };
                Type::Array(Box::new((elem_ty, size)))
            }
            _ => todo!("resolve type {ty:?}"),
        }
    }

    pub fn get_signature(&mut self, module: ModuleId, id: ast::FunctionId) -> &Signature {
        let (ast, checked) = self.modules[module.idx()].ast.as_ref().unwrap();
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
                let args = function.params
                    .clone()
                    .into_iter()
                    .map(|(name_span, ty)| (
                        ast[name_span].to_owned(),
                        self.resolve_type(&ty, scope),
                    ))
                    .collect();
                let return_type = self.resolve_type(&function.return_type, scope);
                let signature = Signature {
                    args,
                    return_type,
                };
                self.modules[module.idx()].ast.as_mut().unwrap().1.function_signatures[id.idx()]
                    .put(signature)
            }
        }
    }

    /*
    pub fn get_resolved_type_def(&mut self, module: ModuleId, id: ast::TypeId) -> &ResolvedTypeDef {
        let (ast, symbols) = self.get_module_ast_and_symbols(module);
        if let Some(id)
        let def = &ast[id];
        match &def {
            Resolvable::Unresolved => {
                self.type_defs[id.idx()].resolved = Resolvable::Resolving;
                let resolved_def = eval::type_def(self, id);
                self.type_defs[id.idx()].resolved.put(resolved_def)
            }
            Resolvable::Resolving => panic!("type def depends on itself recursively"),
            Resolvable::Resolved(_) => {
                // borrowing issue
                let Resolvable::Resolved(id) = &self.type_defs[id.idx()].resolved else { unreachable!() };
                id
            }
        }
    }*/

    pub fn get_checked_function(&mut self, module: ModuleId, id: ast::FunctionId) -> &CheckedFunction {
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
                let checked = if let Some(body) = function.body {
                    self.get_signature(module, id);
                    // signature is resolved above
                    let Resolvable::Resolved(signature) = &self.modules[module.idx()].ast
                        .as_ref().unwrap()
                        .1.function_signatures[id.idx()] else { unreachable!() };
                    let mut types = TypeTable::new();
                    let mut vars = Vars::new();
                    let parameter_variables = signature.args
                        .iter()
                        .map(|(name, ty)| (name.clone(), vars.add(types.from_resolved(ty))))
                        .collect();
                    let return_ty = types.from_resolved(&signature.return_type);
                    let mut scope = LocalScope {
                        parent: None,
                        variables: parameter_variables,
                        module,
                        static_scope: function.scope,
                    };
                    self.typecheck_expr(&ast, body, &mut scope, &mut types, &mut vars, return_ty, return_ty);
                    // TODO: proper idents, var_types, probably should unify concepts with `Vars`
                    let idents = Vec::new();
                    let var_types = Vec::new();
                    CheckedFunction { types, idents, var_types }
                } else {
                    CheckedFunction {
                        types: TypeTable::new(),
                        idents: Vec::new(),
                        var_types: Vec::new(),
                    }
                };
                self.modules[module.idx()].ast.as_mut().unwrap().1.functions[id.idx()]
                    .put(checked)
            }
        }
    }

    pub fn print_errors(&mut self) {
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
        } else if errors.warning_count() != 0 {
            let c = errors.warning_count();
            cprintln!("#r<Finished with #u;r!<{}> warning{}>",
                c, if c == 1 { "" } else { "s" });
            for warn in &errors.warnings {
                print(warn);
            }
        }
    }

    fn typecheck_expr(
        &mut self,
        ast: &Ast,
        expr: ExprId,
        scope: &mut LocalScope,
        types: &mut TypeTable,
        vars: &mut Vars,
        expected: LocalTypeId,
        return_ty: LocalTypeId,
    ) {
        match &ast[expr] {
            Expr::IntLiteral(span) => {
                let lit = IntLiteral::parse(&ast.src()[span.range()]);
                let info = lit.ty.map_or(
                    TypeInfo::Integer,
                    |int| TypeInfo::Primitive(int.into()),
                );
                types.specify(expected, info);
            }
            &Expr::Variable { span, id } => {
                // TODO: use id to save info about resolved var
                let name = &ast[span];
                match scope.resolve(name, span, self) {
                    LocalItem::Var(var) => types.unify(expected, vars.get_type(var)),
                    LocalItem::Def(def) => match def {
                        Def::Function(_, _) => todo!("function items"),
                        Def::Type(_) => todo!("type type?"),
                        Def::ConstValue(const_val) => match &self.const_values[const_val.idx()] {
                            ConstValue::Unit => types.specify(expected, TypeInfo::Primitive(Primitive::Unit)),
                            ConstValue::Number(_) => types.specify(expected, TypeInfo::Primitive(Primitive::I32)),
                        }
                        Def::Module(_) => panic!("value expected but found module"),
                        Def::Global(_) => todo!("globals"),
                        Def::Invalid => types.specify(expected, TypeInfo::Invalid),
                    }
                    LocalItem::Invalid => types.specify(expected, TypeInfo::Invalid),
                }
            }
            Expr::ReturnUnit { .. } => {
                types.specify(return_ty, TypeInfo::Primitive(Primitive::Unit));
            }
            &Expr::Return { val, .. } => {
                self.typecheck_expr(ast, val, scope, types, vars, return_ty, return_ty);
            }
            Expr::Function { id: _ } => todo!("function items (+ closures)"),
            Expr::Type { id: _ } => todo!("type type?"),
            &Expr::Block { scope: static_scope, items, span: _ } => {
                let mut scope = LocalScope {
                    parent: Some(scope),
                    variables: dmap::new(),
                    module: scope.module,
                    static_scope,
                };
                for item in items {
                    let unknown = types.add_unknown();
                    self.typecheck_expr(ast, item, &mut scope, types, vars, unknown, return_ty);
                }
            }
            expr => todo!("typecheck {expr:?}")
        }
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
struct Vars {
    vars: Vec<LocalTypeId>,
}
impl Vars {
    pub fn new() -> Self {
        Self {
            vars: Vec::new(),
        }
    }

    pub fn get_type(&self, var: VarId) -> LocalTypeId {
        self.vars[var.idx()]
    }

    pub fn add(&mut self, ty: LocalTypeId) -> VarId {
        let id = VarId(self.vars.len() as _);
        self.vars.push(ty);
        id
    }
}

struct LocalScope<'p> {
    parent: Option<&'p LocalScope<'p>>,
    variables: DHashMap<String, VarId>,
    module: ModuleId,
    static_scope: ScopeId,
}
enum LocalItem {
    Var(VarId),
    Def(Def),
    Invalid,
}
impl<'p> LocalScope<'p> {
    fn resolve(&self, name: &str, name_span: TSpan, compiler: &mut Compiler) -> LocalItem {
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
            compiler.emit_error(Error::UnknownIdent.at_span(name_span.in_mod(self.module)));
            LocalItem::Invalid
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Def {
    Invalid,
    Function(ModuleId, ast::FunctionId),
    Type(TypeId),
    ConstValue(ConstValueId),
    Module(ModuleId),
    Global(GlobalId),
}
impl Def {
    pub fn dump(&self, compiler: &Compiler) {
        match self {
            Self::Invalid => print!("<invalid>"),
            Self::Function(module, id) => print!("Function({}, {})", module.idx(), id.idx()),
            Self::Type(id) => print!("Type({})", id.idx()),
            Self::ConstValue(value) => compiler.const_values[value.idx()].dump(),
            Self::Module(id) => print!("Module({})", id.idx()),
            Self::Global(id) => print!("Global({})", id.idx()),
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
    pub ast: Option<(Rc<Ast>, ModuleSymbols)>,
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

#[derive(Debug, Default)]
pub struct Function {
    signature: Resolvable<Signature>,
    checked: Resolvable<CheckedFunction>,
}

#[derive(Debug)]
struct Signature {
    args: Vec<(String, Type)>,
    return_type: Type,
}

#[derive(Debug)]
enum ResolvedTypeDef {
    Struct(ResolvedStructDef),
}

#[derive(Debug)]
struct ResolvedStructDef {
    fields: Vec<(String, Type)>,
}

struct ResolvableTypeDef {
    module: ModuleId,
    id: ast::TypeId,
    resolved: Resolvable<ResolvedTypeDef>,
}

#[derive(Debug)]
pub struct ModuleSymbols {
    pub function_signatures: Vec<Resolvable<Signature>>,
    pub functions: Vec<Resolvable<CheckedFunction>>,
    pub types: Vec<Option<TypeId>>,
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
        }
    }
}

#[derive(Debug)]
pub struct CheckedFunction {
    types: TypeTable,
    idents: Vec<Ident>,
    var_types: Vec<LocalTypeId>,
}

#[derive(Clone, Copy, Debug)]
pub enum Ident {
    Invalid,
    Var(VarId),
    Global(GlobalId),
    Type(LocalTypeId),
    Function(ModuleId, ast::FunctionId),
    Module(ModuleId),
    Const(ConstValueId),
}

