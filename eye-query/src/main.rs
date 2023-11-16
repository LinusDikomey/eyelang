use std::{path::{PathBuf, Path}, io, collections::HashMap, ops::Index, rc::Rc};

use eval::ConstValue;

mod eval;
mod type_table;

macro_rules! id {
    ($name: ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct $name(u32);
        impl $name {
            pub fn idx(self) -> usize {
                self.0 as usize
            }
        }
    };
}
pub(crate) use id;
use type_table::{TypeTable, LocalTypeId, TypeInfo};

fn parse(_path: &Path, compiler: &mut Compiler, scope: ScopeId) -> HashMap<String, ModuleItem> {
    let main_func_id = {
        let block_scope = compiler.add_scope(Scope {
            parent: Some(scope),
            items: HashMap::new(),
        });
        let mut ast = AstBuilder::new();
        let answer = ast.add(Expr::Ident("ANSWER".to_owned()));
        let return_answer = ast.add(Expr::Return(Some(answer)));
        let ast = ast.finish_with_root(Expr::Block {
            static_scope: block_scope,
            items: vec![return_answer],
        });

        compiler.add_function(FunctionAst {
            args: vec![],
            return_type: UnresolvedType::Path(vec!["Vec2".to_owned()]),
            body: Some(ast),
            var_count: 0,
            enclosing_scope: scope,
        })
    };

    let def = StructDef {
        fields: vec![
            ("x".to_owned(), UnresolvedType::Primitive(Primitive::I32)),
            ("y".to_owned(), UnresolvedType::Pointer(Box::new(UnresolvedType::Path(vec!["Vec2".to_owned()])))),
        ]
    };
    let vec2_def = compiler.add_type_def(TypeDefAst::Struct { def, enclosing_scope: scope });
    let vec2 = AstBuilder::new().finish_with_root(Expr::Type(vec2_def));

    let main = AstBuilder::new().finish_with_root(Expr::Ident("main_function".to_owned()));

    let main_function = AstBuilder::new().finish_with_root(Expr::Function(main_func_id));

    let answer = AstBuilder::new().finish_with_root(Expr::Number(42));

    HashMap::from([
        ("Vec2".to_owned(), ModuleItem::new(vec2)),
        ("main".to_owned(), ModuleItem::new(main)),
        ("main_function".to_owned(), ModuleItem::new(main_function)),
        ("ANSWER".to_owned(), ModuleItem::new(answer)),
    ])
}

id!(ProjectId);
id!(ModuleId);
id!(ScopeId);
id!(ExprId);
id!(FunctionId);
id!(TypeDefId);
id!(TypeId);
id!(ConstValueId);

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

struct AstBuilder {
    exprs: Vec<Expr>,
}
impl AstBuilder {
    pub fn new() -> Self {
        Self {
            exprs: Vec::new(),
        }
    }

    pub fn add(&mut self, expr: Expr) -> ExprId {
        let id = ExprId(self.exprs.len() as _);
        self.exprs.push(expr);
        id
    }

    pub fn finish_with_root(mut self, root_expr: Expr) -> Ast {
        self.exprs.push(root_expr);
        Ast { exprs: Rc::from(self.exprs) }
    }
}

#[derive(Debug, Clone)]
struct Ast {
    exprs: Rc<[Expr]>,
}
impl Ast {
    pub fn root(&self) -> ExprId {
        ExprId((self.exprs.len() - 1) as _)
    }
}
impl Index<ExprId> for Ast {
    type Output = Expr;

    fn index(&self, index: ExprId) -> &Self::Output {
        &self.exprs[index.idx()]
    }
}

struct Compiler {
    projects: Vec<Project>,
    modules: Vec<Module>,
    scopes: Vec<Scope>,
    functions: Vec<Function>,
    const_values: Vec<ConstValue>,
    type_defs: Vec<TypeDef>,
    types: Vec<ResolvedTypeDef>,
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
        let root_module = if root.is_file() {
            Module::at_path(root.clone(), None)

        } else {
            if !root.is_dir() {
                panic!("project at {} is not a directory or file", root.display());
            }
            let main_path = root.join("main.eye");
            if !main_path.try_exists()? {
                panic!();
            }
            Module::at_path(main_path, None)
        };
        let project_id = ProjectId(self.projects.len() as _);
        let root_module_id = ModuleId(self.modules.len() as _);
        self.modules.push(root_module);
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

    pub fn add_scope(&mut self, scope: Scope) -> ScopeId {
        let id = ScopeId(self.scopes.len() as _);
        self.scopes.push(scope);
        id
    }

    pub fn add_function(&mut self, ast: FunctionAst) -> FunctionId {
        let id = FunctionId(self.functions.len() as _);
        self.functions.push(Function {
            ast,
            signature: Resolvable::Unresolved,
        });
        id
    }

    pub fn add_type_def(&mut self, def: TypeDefAst) -> TypeDefId {
        let id = TypeDefId(self.type_defs.len() as _);
        self.type_defs.push(TypeDef { ast: def, resolved: Resolvable::Unresolved });
        id
    }

    pub fn add_const_value(&mut self, value: ConstValue) -> ConstValueId {
        let id = ConstValueId(self.const_values.len() as _);
        self.const_values.push(value);
        id
    }

    pub fn add_type(&mut self, ty: ResolvedTypeDef) -> TypeId {
        let id = TypeId(self.types.len() as _);
        self.types.push(ty);
        id
    }

    pub fn get_project(&self, id: ProjectId) -> &Project {
        &self.projects[id.idx()]
    }

    pub fn get_module_scope(&mut self, module: ModuleId) -> ScopeId {
        if let Some(scope_id) = self.modules[module.idx()].scope {
            scope_id
        } else {
            // stupid borrowing issue prevents this from being an if let without unwrap
            
            // create placeholder scope for now
            let scope_id = self.add_scope(Scope { parent: None, items: HashMap::new() });
            let items = parse(&self.modules[module.idx()].path.clone(), self, scope_id);
            // The parent module has to have been parsed if we are looking at the child scope, so
            // unwrapping the scope should be fine. If this isn't the case anymore, maybe use
            // get_module_scope recursively or think of a new solution
            let parent = self.modules[module.idx()].parent.map(|parent_module| self.modules[parent_module.idx()].scope.unwrap());
            self.scopes[scope_id.idx()] = Scope {
                parent,
                items,
            };
            scope_id
        }
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

    pub fn resolve_type(&mut self, ty: &UnresolvedType, scope: ScopeId) -> ResolvedType {
        match ty {
            UnresolvedType::Primitive(p) => ResolvedType::Primitive(*p),
            UnresolvedType::Path(path) => {
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
                    Def::Type(id) => ResolvedType::Def { id, generics: vec![] },
                    _ => panic!("type expected")
                }
            }
            UnresolvedType::Array(b) => {
                let (elem_ty, size) = &**b;
                let elem_ty = self.resolve_type(elem_ty, scope);
                ResolvedType::Array(Box::new((elem_ty, *size)))
            }
            UnresolvedType::Pointer(pointee) => ResolvedType::Pointer(Box::new(self.resolve_type(pointee, scope))),
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

    pub fn get_resolved_type_def(&mut self, id: TypeDefId) -> TypeId {
        let def = &mut self.type_defs[id.idx()];
        match &def.resolved {
            Resolvable::Unresolved => {
                def.resolved = Resolvable::Resolving;
                let ty = eval::type_def(self, id);
                self.type_defs[id.idx()].resolved = Resolvable::Resolved(ty);
                ty 
            }
            Resolvable::Resolving => panic!("type def depends on itself recursively"),
            &Resolvable::Resolved(id) => id,
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
            Expr::Block { static_scope, items } => {
                let mut scope = LocalScope {
                    parent: Some(scope),
                    variables: HashMap::new(),
                    static_scope: *static_scope,
                };
                for item in items.iter().copied() {
                    let unknown = types.add_unknown();
                    self.typecheck_expr(ast, item, &mut scope, types, vars, unknown, return_ty);
                }
            }

        }
    }
}

id!(VarId);
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
    root_module: ModuleId,
    dependencies: Vec<ProjectId>,
}
struct Module {
    path: PathBuf,
    /// None means the file hasn't been parsed yet. Not using Resolvable since Resolving is not a
    /// valid state.
    scope: Option<ScopeId>,
    parent: Option<ModuleId>,
}
impl Module {
    pub fn at_path(path: PathBuf, parent: Option<ModuleId>) -> Self {
        Self {
            scope: None,
            path,
            parent,
        }
    }
}

struct Scope {
    parent: Option<ScopeId>,
    items: HashMap<String, ModuleItem>,
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
    ast: FunctionAst,
    signature: Resolvable<Signature>,
}

#[derive(Debug)]
struct Signature {
    args: Vec<(String, ResolvedType)>,
    return_type: ResolvedType,
}

#[derive(Debug)]
struct FunctionAst {
    args: Vec<(String, UnresolvedType)>,
    return_type: UnresolvedType,
    /// Number of vars bound in the function. Includes parameters.
    var_count: usize,
    body: Option<Ast>,
    enclosing_scope: ScopeId,
}

#[derive(Debug)]
struct TypeDef {
    ast: TypeDefAst,
    resolved: Resolvable<TypeId>,
}

#[derive(Debug, Clone)]
enum UnresolvedType {
    Primitive(Primitive),
    Path(Vec<String>),
    Array(Box<(UnresolvedType, u64)>),
    Pointer(Box<UnresolvedType>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Primitive {
    Unit,
    I32,
}

#[derive(Debug)]
enum ResolvedType {
    Primitive(Primitive),
    Def {
        id: TypeDefId,
        generics: Vec<ResolvedType>,
    },
    Array(Box<(ResolvedType, u64)>),
    Pointer(Box<ResolvedType>),
}

#[derive(Debug)]
enum Expr {
    Number(u64),
    Ident(String),
    Return(Option<ExprId>),
    Function(FunctionId),
    Type(TypeDefId),
    Block {
        static_scope: ScopeId,
        items: Vec<ExprId>, // TODO: make this ExprIdRange
    },
}

#[derive(Debug)]
enum TypeDefAst {
    Struct { def: StructDef, enclosing_scope: ScopeId },
}

#[derive(Debug)]
struct StructDef {
    fields: Vec<(String, UnresolvedType)>,
}

#[derive(Debug)]
enum ResolvedTypeDef {
    Struct(ResolvedStructDef),
}

#[derive(Debug)]
struct ResolvedStructDef {
    fields: Vec<(String, ResolvedType)>,
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
    let ResolvedType::Def { id: vec2, generics } = compiler.resolve_type(&UnresolvedType::Path(vec!["Vec2".to_owned()]), root) else { panic!() };
    assert!(generics.is_empty());
    dbg!(&compiler.type_defs[vec2.idx()]);
    let resolved_vec2 = compiler.get_resolved_type_def(vec2);
    dbg!(&compiler.types[resolved_vec2.idx()]);
    Ok(())
}
