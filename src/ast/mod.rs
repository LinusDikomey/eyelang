use std::{collections::HashMap, fmt, ops::{Index, IndexMut}, path::{PathBuf, Path}};
use crate::{lexer::tokens::{FloatLiteral, IntLiteral, Operator}, types::Primitive};
use self::repr::{Representer, Repr};

pub mod repr;

pub struct Modules {
    modules: Vec<Module>,
    sources: Vec<(String, PathBuf)>
}
impl Modules {
    pub fn new() -> Self {
        Self { modules: Vec::new(), sources: Vec::new() }
    }

    pub fn len(&self) -> usize {
        self.modules.len()
    }

    pub fn add(&mut self, module: Module, src: String, path: PathBuf) -> ModuleId {
        let id = ModuleId(self.modules.len() as u32);
        self.modules.push(module);
        self.sources.push((src, path));
        id
    }

    pub fn update(&mut self, id: ModuleId, module: Module, src: String, path: PathBuf) {
        self.modules[id.0 as usize] = module;
        self.sources[id.0 as usize] = (src, path);
    }
    
    pub fn src(&self, id: ModuleId) -> (&str, &Path) {
        let t = &self.sources[id.0 as usize];
        (&t.0, &t.1)
    }

    pub fn iter(&self) -> impl Iterator<Item = (ModuleId, &Module)> {
        self.modules.iter()
            .enumerate()
            .map(|(i, m)| (ModuleId(i as u32), m))
    }
}
impl Index<ModuleId> for Modules {
    type Output = Module;

    fn index(&self, index: ModuleId) -> &Self::Output {
        &self.modules[index.0 as usize]
    }
}
impl IndexMut<ModuleId> for Modules {
    fn index_mut(&mut self, index: ModuleId) -> &mut Self::Output {
        &mut self.modules[index.0 as usize]
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ModuleId(u32);
impl ModuleId {
    pub const ROOT: Self = Self(0);
    pub fn idx(self) -> usize { self.0 as usize }
}

#[derive(Debug, Clone)]
pub struct Module {
    pub definitions: HashMap<String, Definition>,
    pub uses: Vec<IdentPath>
}
impl Module {
    pub fn empty() -> Self {
        Self { definitions: HashMap::new(), uses: Vec::new() }
    }
}

#[derive(Debug, Clone)]
pub enum Item {
    Definition(String, Definition),
    Block(BlockItem)
}

#[derive(Debug, Clone)]
pub enum Definition {
    Function(Function),
    Struct(StructDefinition),
    Module(ModuleId),
    Use(IdentPath)
}

#[derive(Debug, Clone)]
pub struct StructDefinition {
    pub members: Vec<(String, UnresolvedType, u32, u32)>,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub params: Vec<(String, UnresolvedType, u32, u32)>,
    //pub vararg: Option<(String, UnresolvedType, u32, u32)>,
    pub varargs: bool,
    pub return_type: (UnresolvedType, u32, u32),
    pub body: Option<BlockOrExpr>,
}

#[derive(Debug, Clone)]
pub enum BlockOrExpr {
    Block(Block),
    Expr(Expr)
}
impl<C: Representer> Repr<C> for BlockOrExpr {
    fn repr(&self, c: &C) {
        match self {
            BlockOrExpr::Block(block) => block.repr(c),
            BlockOrExpr::Expr(expr) => expr.repr(c)
        }
    }
}

#[derive(Debug, Clone)]
pub struct Block {
    pub items: Vec<BlockItem>,
    pub defs: HashMap<String, Definition>,
    pub uses: Vec<IdentPath>
}

#[derive(Debug, Clone)]
pub enum BlockItem {
    Block(Block),
    Declare(String, Option<UnresolvedType>, Option<Expr>),
    Expr(Expr),
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub ty: ExprTy,
    pub start: u32,
    pub end: u32
}

#[derive(Debug, Clone)]
pub enum ExprTy {
    Return(Box<Expr>),
    IntLiteral(IntLiteral),
    FloatLiteral(FloatLiteral),
    StringLiteral(String),
    BoolLiteral(bool),
    Nested(Box<Expr>),
    Unit,
    Variable(String),
    If(Box<If>),
    While(Box<While>),
    FunctionCall(Box<(Expr, Vec<Expr>)>),
    UnOp(Box<(UnOp, Expr)>),
    BinOp(Box<(Operator, Expr, Expr)>),
    MemberAccess(Box<(Expr, String)>),
    Cast(Box<(UnresolvedType, Expr)>),
    Root
}

#[derive(Debug, Clone, Copy)]
pub enum UnOp {
    Neg,
    Not,
    Ref,
    Deref,
}

#[derive(Debug, Clone)]
pub struct If {
    pub cond: Expr,
    pub then: BlockOrExpr,
    pub else_: Option<BlockOrExpr>
}

#[derive(Debug, Clone)]
pub struct While {
    pub cond: Expr,
    pub body: BlockOrExpr
}

#[derive(Debug, Clone)]
pub enum IdentPath {
    Root,
    Single(String),
    Path { starts_with_root: bool, segments: Vec<String> }
}

impl IdentPath {
    pub fn push(&mut self, segment: String) {
        match self {
            Self::Root => *self = Self::Path { starts_with_root: true, segments: vec![segment] },
            Self::Single(first) => *self = Self::Path { 
                starts_with_root: false,
                segments: vec![std::mem::take(first), segment]
            },
            Self::Path { segments, .. } => segments.push(segment)
        }
    }
    
    /// Returns: (`root`, `segments_without_last`, `last_segment`)
    /// `last_segment` will only be None if the path is a single root item
    pub fn segments(&self) -> (bool, std::slice::Iter<String>, Option<&String>) {
        match self {
            Self::Root => (true, (&[]).iter(), None),
            Self::Single(s) => (false, (&[]).iter(), Some(s)),
            Self::Path { starts_with_root, segments } => (
                *starts_with_root,
                if segments.is_empty() { &[] } else { &segments[..segments.len() - 1] }.iter(),
                segments.last()
            )
        }
    }
}
impl fmt::Display for IdentPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Root => write!(f, "root"),
            Self::Single(s) => write!(f, "{s}"),
            Self::Path { starts_with_root, segments } => {
                if *starts_with_root {
                    write!(f, "root")?;
                    if !segments.is_empty() {
                        write!(f, ".")?;
                    }
                }
                for (i, segment) in segments.iter().enumerate() {
                    if i != 0 { write!(f, ".")?; }
                    write!(f, "{segment}")?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum UnresolvedType {
    Primitive(Primitive),
    Unresolved(IdentPath),
    Pointer(Box<UnresolvedType>),
    Infer,
}
impl fmt::Display for UnresolvedType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnresolvedType::Primitive(p) => p.fmt(f),
            UnresolvedType::Unresolved(path) => write!(f, "{path}"),
            UnresolvedType::Pointer(inner) => write!(f, "*{inner}"),
            UnresolvedType::Infer => write!(f, "_")
        }
    }
}
