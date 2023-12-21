use std::{path::PathBuf, io, collections::HashMap};

use error::Errors;
use eval::ConstValue;

mod error;
mod eval;
mod parser;
mod type_table;

use id::{ScopeId, FunctionId, TypeDefId, ModuleId, ConstValueId, ProjectId, TypeId};
use parser::ast::{self, Ast, Expr, ExprId};
use type_table::{TypeTable, LocalTypeId, TypeInfo};
use types::{Type, UnresolvedType, Primitive};


#[derive(Debug)]
enum Resolvable<T> {
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

struct Compiler {
    projects: Vec<Project>,
    modules: Vec<Module>,
    scopes: Vec<ast::Scope>,
    functions: Vec<Function>,
    const_values: Vec<ConstValue>,
    type_defs: Vec<ResolvedTypeDef>,
    types: Vec<Type>,
}
impl Compiler {
    pub fn new() -> Self {
        Self {
            projects: Vec::new(),
            modules: Vec::new(),
            scopes: Vec::new(),
            functions: Vec::new(),
            const_values: Vec::new(),
            type_defs: Vec::new(),
            types: Vec::new(),
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

    pub fn add_scope(&mut self, scope: ast::Scope) -> ScopeId {
        let id = ScopeId(self.scopes.len() as _);
        self.scopes.push(scope);
        id
    }

    pub fn modify_scope(&mut self, id: ScopeId, scope: ast::Scope) {
        self.scopes[id.idx()] = scope;
    }

    /*
    pub fn add_function(&mut self, ast: ast::Function) -> FunctionId {
        let id = FunctionId(self.functions.len() as _);
        self.functions.push(Function {
            ast,
            signature: Resolvable::Unresolved,
        });
        id
    }

    pub fn add_type_def(&mut self, def: ast::TypeDef) -> TypeDefId {
        let id = TypeDefId(self.type_defs.len() as _);
        self.type_defs.push(TypeDef { ast: def, resolved: Resolvable::Unresolved });
        id
    }
    */

    pub fn add_const_value(&mut self, value: ConstValue) -> ConstValueId {
        let id = ConstValueId(self.const_values.len() as _);
        self.const_values.push(value);
        id
    }

    pub fn get_project(&self, id: ProjectId) -> &Project {
        &self.projects[id.idx()]
    }

    pub fn get_module_scope(&mut self, module_id: ModuleId) -> ScopeId {
        if let Some(scope_id) = self.modules[module_id.idx()].scope {
            scope_id
        } else {
            let module = self.modules[module_id.idx()];
            let root = module.root;
            // The parent module has to have been parsed if we are looking at the child scope, so
            // unwrapping the scope should be fine. If this isn't the case anymore, maybe use
            // get_module_scope recursively or think of a new solution
            let parent = module.parent
                .map(|parent_module| self.modules[parent_module.idx()].scope.unwrap());

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
            let scope = parser::parse(&source, &mut errors, module_id);
            self.add_scope(scope)
        }
    }

    pub fn resolve_module_definition(&mut self, module: ModuleId, name: &str) -> Option<Def> {
        self.get_mo
    }

    pub fn resolve_definition(&mut self, scope: ScopeId, name: &str) -> Option<Def> {
        let item = self.scopes[scope.idx()].items.get_mut(name)?;
        match item.resolved {
            Resolvable::Unresolved => {
                item.resolved = Resolvable::Resolving;
                let def = eval::def_expr(item.ast.root(), item.ast.clone(), scope, self);
                // get item again because the borrow expires above
                let item = self.scopes[scope.idx()].items.get_mut(name).unwrap();
                item.resolved = Resolvable::Resolved(def);
                Some(def)
            }
            Resolvable::Resolving => panic!("recursive definition {name}"),
            Resolvable::Resolved(def) => Some(def),
        }
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

    pub fn get_signature(&mut self, id: FunctionId) -> &Signature {
        match &self.functions[id.idx()].signature {
            Resolvable::Resolved(_) => {
                // borrowing bullshit
                let Resolvable::Resolved(signature) = &self.functions[id.idx()].signature else { unreachable!() };
                signature
            }
            Resolvable::Resolving => panic!("function signature depends on itself recursively"),
            Resolvable::Unresolved => {
                let function = &self.functions[id.idx()];
                let scope = function.ast.enclosing_scope;
                // PERF: cloning args/return type here
                let return_type = function.ast.return_type.clone();
                let args = function.ast.args.clone().into_iter()
                    .map(|(name, ty)| (name, self.resolve_type(&ty, scope)))
                    .collect();
                let return_type = self.resolve_type(&return_type, scope);
                let signature = Signature {
                    args,
                    return_type,
                };
                self.functions[id.idx()].signature.put(signature)
            }
        }
    }

    pub fn get_resolved_type_def(&mut self, id: TypeDefId) -> &ResolvedTypeDef {
        let def = &mut self.type_defs[id.idx()];
        match &def.resolved {
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
    }

    pub fn typecheck_function_body(&mut self, id: FunctionId) {
        let function = &self.functions[id.idx()];
        // Ast is reference counted specifically so we can clone it cheaply for resolval
        // resolve_expr still takes a reference to prevent further reference count overhead.
        // PERF: Could maybe define an AstRef type for that to remove one level of indirection.
        if let Some(body) = function.ast.body.clone() {
            self.get_signature(id);
            let function = &self.functions[id.idx()];
            // signature is resolved above
            let Resolvable::Resolved(signature) = &function.signature else { unreachable!() };
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
                static_scope: function.ast.enclosing_scope,
            };
            self.typecheck_expr(&body, body.root(), &mut scope, &mut types, &mut vars, return_ty, return_ty);
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
            &Expr::Number(_) => types.specify(expected, TypeInfo::Primitive(Primitive::I32)),
            Expr::Ident(name) => match scope.resolve(name, self) {
                LocalItem::Var(var) => types.unify(expected, vars.get_type(var)),
                LocalItem::Def(def) => match def {
                    Def::Function(_) => todo!("function items"),
                    Def::Type(_) => todo!("type type?"),
                    Def::ConstValue(const_val) => match &self.const_values[const_val.idx()] {
                        ConstValue::Unit => types.specify(expected, TypeInfo::Primitive(Primitive::Unit)),
                        ConstValue::Number(_) => types.specify(expected, TypeInfo::Primitive(Primitive::I32)),
                    }
                    Def::Module(_) => panic!("value expected but found module"),

                }
            }
            Expr::Return(None) => {
                types.specify(return_ty, TypeInfo::Primitive(Primitive::Unit));
            }
            &Expr::Return(Some(value)) => {
                self.typecheck_expr(ast, value, scope, types, vars, return_ty, return_ty);
            }
            Expr::Function(_) => todo!("function items (+ closures)"),
            Expr::Type(_) => todo!("type type?"),
            Expr::Block { scope, items, span: _ } => {
                let static_scope = self.add_scope(scope);
                let mut scope = LocalScope {
                    parent: Some(scope),
                    variables: HashMap::new(),
                    static_scope,
                };
                for item in items.iter().copied() {
                    let unknown = types.add_unknown();
                    self.typecheck_expr(ast, item, &mut scope, types, vars, unknown, return_ty);
                }
            }

        }
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
    variables: HashMap<String, VarId>,
    static_scope: ScopeId,
}
enum LocalItem {
    Var(VarId),
    Def(Def),
}
impl<'p> LocalScope<'p> {
    fn resolve(&self, name: &str, compiler: &mut Compiler) -> LocalItem {
        if let Some(var) = self.variables.get(name) {
            LocalItem::Var(*var)
        } else if let Some(def) = compiler.resolve_definition(self.static_scope, name) {
            LocalItem::Def(def)
        } else if let Some(parent) = self.parent {
            parent.resolve(name, compiler)
        } else {
            panic!("item or variable {name} not found in scope")
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Def {
    Function(FunctionId),
    Type(TypeDefId),
    ConstValue(ConstValueId),
    Module(ModuleId),
}
impl Def {
    fn dump(&self, compiler: &Compiler) {
        match self {
            Self::Function(id) => print!("Function({})", id.idx()),
            Self::Type(id) => print!("Type({})", id.idx()),
            Self::ConstValue(value) => compiler.const_values[value.idx()].dump(),
            Self::Module(id) => print!("Module({})", id.idx()),
        }
    }
}


struct Project {
    name: String,
    root: PathBuf,
    root_module: id::ModuleId,
    dependencies: Vec<id::ProjectId>,
}
struct Module {
    path: PathBuf,
    ast: Option<Ast>,
    root: ModuleId,
    parent: Option<ModuleId>,
}
impl Module {
    pub fn at_path(path: PathBuf, root: ModuleId, parent: Option<ModuleId>) -> Self {
        Self {
            ast: None,
            path,
            root,
            parent,
        }
    }
}

struct ModuleItem {
    ast: Ast,
    resolved: Resolvable<Def>,
}
impl ModuleItem {
    pub fn new(ast: Ast) -> Self {
        Self {
            ast,
            resolved: Resolvable::Unresolved,
        }
    }
}

#[derive(Debug)]
struct Function {
    module: ModuleId,
    id: ast::FunctionId,
    signature: Resolvable<Signature>,
}

#[derive(Debug)]
struct Signature {
    args: Vec<(String, Type)>,
    return_type: Type,
}

#[derive(Debug)]
struct TypeDef {
    ast: ast::TypeDef,
    resolved: Resolvable<TypeId>,
}

#[derive(Debug)]
enum ResolvedTypeDef {
    Struct(ResolvedStructDef),
}

#[derive(Debug)]
struct ResolvedStructDef {
    fields: Vec<(String, Type)>,
}


fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut compiler = Compiler::new();
    let project = compiler.add_project("test-project".to_owned(), "test-project.eye".into())?;
    let std = compiler.add_project("std".to_owned(), "std".into())?;
    compiler.add_dependency(project, std);

    let root = compiler.get_project(project).root_module;
    let root = compiler.get_module_scope(root);
    let main_def = compiler.resolve_definition(root, "main").expect("missing main");
    let Def::Function(main_id) = main_def else {
        panic!("main should be a function");
    };
    let main = &compiler.functions[main_id.idx()];
    let body = main.ast.body.as_ref().unwrap().clone();
    print!("Main function {main:?} returned ");
    let main_result = eval::def_expr(body.root(), body, root, &mut compiler);
    main_result.dump(&mut compiler);
    println!();
    /*
    let Type::DefId { id: vec2, generics } = compiler.resolve_type(&UnresolvedType::Path(vec!["Vec2".to_owned()]), root) else { panic!() };
    assert!(generics.is_empty());
    dbg!(&compiler.type_defs[vec2.idx()]);
    let resolved_vec2 = compiler.get_resolved_type_def(vec2);
    dbg!(&compiler.types[resolved_vec2.idx()]);
    */
    Ok(())
}
