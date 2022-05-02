use std::{collections::HashMap, fmt, ops::{Index, IndexMut}, path::{PathBuf, Path}};
use crate::{lexer::tokens::Operator, types::Primitive};

pub mod repr;

pub struct Ast {
    pub modules: Vec<Module>,
    pub sources: Vec<(String, PathBuf)>,
    pub exprs: Vec<Expr>,
}
impl Ast {
    pub fn new() -> Self {
        Self {
            modules: Vec::new(),
            sources: Vec::new(),
            exprs: Vec::new()
        }
    }
    pub fn sources(&self) -> &[(String, PathBuf)] {
        &self.sources
    }
    pub fn add_expr(&mut self, expr: Expr) -> ExprRef {
        let r = ExprRef(self.exprs.len() as u32);
        self.exprs.push(expr);
        r
    }
}
impl Index<ExprRef> for Ast {
    type Output = Expr;

    fn index(&self, index: ExprRef) -> &Self::Output {
        &self.exprs[index.0 as usize]    
    }
    
}


#[derive(Debug, Clone, Copy)]
pub struct ExprRef(u32);

impl Ast {
    pub fn add_module(&mut self, module: Module, src: String, path: PathBuf) -> ModuleId {
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
}
impl Index<ModuleId> for Ast {
    type Output = Module;

    fn index(&self, index: ModuleId) -> &Self::Output {
        &self.modules[index.0 as usize]
    }
}
impl IndexMut<ModuleId> for Ast {
    fn index_mut(&mut self, index: ModuleId) -> &mut Self::Output {
        &mut self.modules[index.0 as usize]
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ModuleId(u32);
impl ModuleId {
    pub fn new(id: u32) -> Self {
        Self(id)
    }
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
    Expr(ExprRef)
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
    pub body: Option<ExprRef>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Block {
        span: TSpan,
        items: Vec<ExprRef>,
        defs: HashMap<String, Definition>
    },
    Declare {
        name: TSpan,
        end: u32,
        annotated_ty:
        UnresolvedType,
        val: Option<ExprRef>
    },
    Return { start: u32, val: ExprRef },
    IntLiteral(TSpan),
    FloatLiteral(TSpan),
    StringLiteral(TSpan),
    BoolLiteral { start: u32, val: bool },
    Nested(TSpan, ExprRef),
    Unit(TSpan),
    Variable(TSpan),
    If {
        span: TSpan,
        cond: ExprRef,
        then: ExprRef,
        else_: Option<ExprRef>
    },
    While(Box<While>), //TODO: no more boxing
    FunctionCall(ExprRef, Vec<ExprRef>, u32),
    UnOp(u32, UnOp, ExprRef),
    BinOp(Operator, ExprRef, ExprRef),
    MemberAccess(ExprRef, TSpan),
    Cast(TSpan, UnresolvedType, ExprRef),
    Root(u32)
}
impl Expr {
    pub fn is_block(&self) -> bool {
        matches!(self, Self::Block { .. })
    }
    pub fn span(&self, ast: &Ast) -> TSpan {
        match self {
            Expr::Block { span, .. } => *span,
            Expr::Declare { name, end, .. } => TSpan::new(name.start, *end),
            Expr::Return { start, val } => TSpan::new(*start, ast[*val].end(ast)),
            Expr::IntLiteral(span) | Expr::FloatLiteral(span) => *span,
            Expr::StringLiteral(span) => *span,
            Expr::BoolLiteral { start, val } => TSpan::new(*start, start + if *val {4} else {5}),
            Expr::Nested(span, _) => *span,
            Expr::Unit(span) => *span,
            Expr::Variable(span) => *span,
            Expr::If { span, .. } => *span,
            Expr::While(box while_) => while_.span,
            Expr::FunctionCall(inner, _, end) => TSpan::new(ast[*inner].start(ast), *end),
            Expr::UnOp(start_or_end, un_op, expr) => if un_op.postfix() {
                TSpan::new(ast[*expr].start(ast), *start_or_end)
            } else {
                TSpan::new(*start_or_end, ast[*expr].end(ast))
            }
            Expr::BinOp(_, l, r) => TSpan::new(ast[*l].start(ast), ast[*r].end(ast)),
            Expr::MemberAccess(expr, span) => TSpan::new(ast[*expr].start(ast), span.end),
            Expr::Cast(span, _, _) => *span,
            Expr::Root(start) => TSpan::new(*start, *start + 4),
        }
    }
    pub fn start(&self, ast: &Ast) -> u32 {
        //TODO: more efficient implementation
        self.span(ast).start
    }
    pub fn end(&self, ast: &Ast) -> u32 {
        //TODO: more efficient implementation
        self.span(ast).end
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TSpan {
    pub start: u32,
    pub end: u32
}
impl TSpan {
    pub fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum UnOp {
    Neg,
    Not,
    Ref,
    Deref,
}
impl UnOp {
    pub fn postfix(self) -> bool {
        matches!(self, UnOp::Deref)
    }
}

#[derive(Debug, Clone)]
pub struct While {
    pub span: TSpan,
    pub cond: ExprRef,
    pub body: ExprRef
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
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
