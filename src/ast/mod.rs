use std::{collections::HashMap, ops::{Index, IndexMut}, path::{PathBuf, Path}};
use crate::{lexer::tokens::Operator, types::Primitive};

pub mod repr;

pub struct Ast {
    pub modules: Vec<Module>,
    pub sources: Vec<(String, PathBuf)>,
    pub expr_builder: ExprBuilder
}
impl Ast {
    pub fn new() -> Self {
        Self {
            modules: Vec::new(),
            sources: Vec::new(),
            expr_builder: ExprBuilder {
                exprs: Vec::new(),
                extra: Vec::new(),
                defs: Vec::new()
            }
        }
    }
    pub fn sources(&self) -> &[(String, PathBuf)] {
        &self.sources
    }
    pub fn add_expr(&mut self, expr: Expr) -> ExprRef {
        self.expr_builder.add(expr)
    }
    pub fn extra(&mut self, extra: &[ExprRef]) -> ExprExtra {
        self.expr_builder.extra(extra)
    }
    pub fn get_extra(&self, idx: ExprExtra) -> &[ExprRef] {
        &self.expr_builder.extra[idx.0 as usize .. idx.0 as usize + idx.1 as usize]
    }
}
impl Index<ExprRef> for Ast {
    type Output = Expr;

    fn index(&self, index: ExprRef) -> &Self::Output {
        &self.expr_builder.exprs[index.0 as usize]    
    }
    
}

pub struct ExprBuilder {
    exprs: Vec<Expr>,
    extra: Vec<ExprRef>,
    defs: Vec<HashMap<String, Definition>>
}
impl ExprBuilder {
    pub fn add(&mut self, expr: Expr) -> ExprRef {
        let r = ExprRef(self.exprs.len() as u32);
        self.exprs.push(expr);
        r
    }
    pub fn extra(&mut self, extra: &[ExprRef]) -> ExprExtra {
        let idx = ExprExtra(self.extra.len() as u32, extra.len() as u32);
        self.extra.extend(extra);
        idx
    }
    pub fn defs(&mut self, defs: HashMap<String, Definition>) -> Defs {
        let idx = self.defs.len();
        self.defs.push(defs);
        Defs(idx as u32)
    }
}
impl Index<Defs> for ExprBuilder {
    type Output = HashMap<String, Definition>;

    fn index(&self, index: Defs) -> &Self::Output {
        &self.defs[index.0 as usize]
    }
}


#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
pub struct ExprRef(u32);

#[derive(Debug, Clone, Copy)]
pub struct ExprExtra(u32, u32);

#[derive(Debug, Clone, Copy)]
pub struct ExprExtraSpans(u32, u32);

#[derive(Debug, Clone, Copy)]
pub struct Defs(u32);

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

#[derive(Debug, Clone, eye_derive::EnumSizeDebug)]
pub enum Expr {
    Block {
        span: TSpan,
        items: ExprExtra,
        defs: Defs
    },
    Declare {
        name: TSpan,
        annotated_ty: UnresolvedType,
        end: u32
    },
    DeclareWithVal {
        name: TSpan,
        annotated_ty: UnresolvedType,
        val: ExprRef
    },
    Return { start: u32, val: ExprRef },
    IntLiteral(TSpan),
    FloatLiteral(TSpan),
    StringLiteral(TSpan),
    BoolLiteral { start: u32, val: bool },
    Nested(TSpan, ExprRef),
    Unit(TSpan),
    Variable(TSpan),
    Array(TSpan, Vec<ExprRef>),
    If {
        start: u32,
        cond: ExprRef,
        then: ExprRef,
    },
    IfElse {
        start: u32,
        cond: ExprRef,
        then: ExprRef,
        else_: ExprRef
    },
    While {
        start: u32,
        cond: ExprRef,
        body: ExprRef
    },
    FunctionCall { func: ExprRef, args: Vec<ExprRef>, end: u32 },
    UnOp(u32, UnOp, ExprRef),
    BinOp(Operator, ExprRef, ExprRef),
    MemberAccess { left: ExprRef, name: TSpan },
    Cast(TSpan, UnresolvedType, ExprRef),
    Root(u32)
}
impl Expr {
    pub fn is_block(&self) -> bool {
        matches!(self, Self::Block { .. })
    }
    pub fn span(&self, ast: &Ast) -> TSpan {
        // shorthands for getting start and end position of an ExprRef
        let s = |r: &ExprRef| ast[*r].start(ast);
        let e = |r: &ExprRef| ast[*r].end(ast);

        match self {
            Expr::Block { span, .. }
                | Expr::StringLiteral(span) | Expr::IntLiteral(span) | Expr::FloatLiteral(span)
                | Expr::Nested(span, _) 
                | Expr::Unit(span)
                | Expr::Variable(span)
                | Expr::Array(span, _)
                | Expr::Cast(span, _, _)
                => *span,
            Expr::Declare { name, end, .. } => TSpan::new(name.start, *end),
            Expr::DeclareWithVal { name, val, .. } => TSpan::new(name.start, e(val)),
            Expr::Return { start, val } => TSpan::new(*start, e(val)),
            Expr::BoolLiteral { start, val } => TSpan::new(*start, start + if *val {4} else {5}),
            Expr::If { start, cond: _, then } => TSpan::new(*start, e(then) ),
            Expr::IfElse { start, cond: _, then: _, else_ } => TSpan::new(*start, e(else_) ),
            Expr::While { start, cond: _, body } => TSpan::new(*start, e(body)),
            Expr::FunctionCall { func, args: _, end } => TSpan::new(s(func), *end),
            Expr::UnOp(start_or_end, un_op, expr) => if un_op.postfix() {
                TSpan::new(s(expr), *start_or_end)
            } else {
                TSpan::new(*start_or_end, e(expr))
            }
            Expr::BinOp(_, l, r) => TSpan::new(s(l), e(r)),
            Expr::MemberAccess { left, name } => TSpan::new(s(left), name.end),
            Expr::Root(start) => TSpan::new(*start, *start + 3),
        }
    }
    pub fn span_in(&self, ast: &Ast, module: ModuleId) -> crate::lexer::Span {
        self.span(ast).in_mod(module)
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
        debug_assert!(start-1 <= end, "Invalid span constructed");
        Self { start, end }
    }
    pub fn in_mod(self, module: ModuleId) -> crate::lexer::Span {
        crate::lexer::Span::new(self.start, self.end, module)
    }
    pub fn range(self) -> std::ops::RangeInclusive<usize> {
        self.start as usize ..= self.end as usize
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
pub struct IdentPath(TSpan); // just save the span and reparse when it is resolved

impl IdentPath {
    pub fn new(span: TSpan) -> Self {
        debug_assert!(!span.range().is_empty(), "Tried to construct empty path");
        Self(span)
    }
    /// Returns: (`root`, `segments_without_last`, `last_segment`)
    /// `last_segment` will only be None if the path is a single root item
    pub fn segments<'a>(&'a self, src: &'a str)
    -> (Option<TSpan>, impl Iterator<Item = (&str, TSpan)>, Option<(&str, TSpan)>) {
        let start_addr = src.as_ptr() as usize;

        let s = &src[self.0.range()];

        let mut split = s.split('.').map(move |segment| {
            let trimmed = segment.trim();
            let idx = (trimmed.as_ptr() as usize - start_addr) as u32;
            (trimmed, TSpan::new(idx, idx + trimmed.len() as u32 - 1))
        }).peekable();
        let first = split.peek().cloned();
        let last = split.next_back().unwrap();
        if let Some(("root", first_span)) = first {
            split.next();
            let last = if last.0 == "root" { None } else { Some(last) };
            (Some(first_span), split, last)
        } else {
            (None, split, Some(last))
        }
    }

    pub fn span(&self) -> TSpan {
        self.0
    }
}
/*
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
*/

#[derive(Debug, Clone)]
pub enum UnresolvedType {
    Primitive(Primitive, TSpan),
    Unresolved(IdentPath),
    Pointer(Box<(UnresolvedType, u32)>),
    Infer(u32),
}
impl UnresolvedType {
    pub fn span(&self, expr_builder: &ExprBuilder) -> TSpan {
        match self {
            UnresolvedType::Primitive(_, span) => *span,
            UnresolvedType::Unresolved(path) => path.span(),
            UnresolvedType::Pointer(box (inner, start)) => TSpan::new(*start, inner.span(expr_builder).end),
            UnresolvedType::Infer(s) => TSpan::new(*s, *s),
        }
    }
}
/*
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
*/