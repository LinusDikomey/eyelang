use std::ops::Index;
use id::{TypeId, TraitId, ModuleId, TypeDefId};
use span::{TSpan, Span, IdentPath};
use dmap::{self, DHashMap};
use types::{Primitive, UnresolvedType};

use crate::{parser::{Counts, token::Operator}, Resolvable, Def};

pub mod repr;

id::id!(ScopeId);
id::id!(ExprId);
id::id!(CallId);
id::id!(FunctionId);
id::id!(GlobalId);

id::id!(
    /// Identifiers inside ASTs all get assigned unique ids.
    /// Inner functions inside functions will have indiviual identifier scopes meaning ids can and
    /// will repeat.
    IdentId
);

/// Ast for a single file
#[derive(Debug)]
pub struct Ast {
    scopes: Vec<Scope>,
    exprs: Vec<Expr>,
    calls: Vec<Call>,
    functions: Vec<Function>,
    globals: Vec<Global>,
}
impl Ast {
    fn new() -> Self {
        Self {
            scopes: Vec::new(),
            exprs: Vec::new(),
            calls: Vec::new(),
            functions: Vec::new(),
            globals: Vec::new(),

        }
    }

    fn top_level_scope_id(&self) -> ScopeId {
        ScopeId((self.scopes.len() - 1) as _)
    }
    
    fn top_level_scope(&self) -> &Scope {
        // the last scope is guaranteed to exist and to represent the top level scope of this Ast
        self.scopes.last().unwrap()
    }
}
impl Index<ScopeId> for Ast {
    type Output = Scope;
    fn index(&self, index: ScopeId) -> &Self::Output {
        &self.scopes[index.idx()]
    }
}
impl Index<ExprId> for Ast {
    type Output = Expr;
    fn index(&self, index: ExprId) -> &Self::Output {
        &self.exprs[index.idx()]
    }
}
impl Index<CallId> for Ast {
    type Output = Call;
    fn index(&self, index: CallId) -> &Self::Output {
        &self.calls[index.idx()]
    }
}
impl Index<FunctionId> for Ast {
    type Output = Function;
    fn index(&self, index: FunctionId) -> &Self::Output {
        &self.functions[index.idx()]
    }
}
impl Index<GlobalId> for Ast {
    type Output = Global;
    fn index(&self, index: GlobalId) -> &Self::Output {
        &self.globals[index.idx()]
    }
}

pub struct AstBuilder {
    scopes: Vec<Scope>,
    exprs: Vec<Expr>,
    calls: Vec<Call>,
    functions: Vec<Function>,
    globals: Vec<Global>,
}
impl AstBuilder {
    pub fn new() -> Self {
        Self {
            exprs: Vec::new(),
            calls: Vec::new(),
            functions: Vec::new(),
            scopes: Vec::new(),
            globals: Vec::new(),
        }
    }

    pub fn scope(&mut self, scope: Scope) -> ScopeId {
        let id = ScopeId(self.scopes.len() as _);
        self.scopes.push(scope);
        id
    }

    pub fn expr(&mut self, expr: Expr) -> ExprId {
        let id = ExprId(self.exprs.len() as _);
        self.exprs.push(expr);
        id
    }

    pub fn exprs(&mut self, exprs: impl IntoIterator<Item = Expr>) -> ExprExtra {
        let idx = self.exprs.len();
        self.exprs.extend(exprs);
        let count = self.exprs.len() - idx;
        ExprExtra { idx: idx as _, count: count as _ }
    }

    pub fn call(&mut self, call: Call) -> CallId {
        let id = CallId(self.calls.len() as _);
        self.calls.push(call);
        id
    }

    pub fn function(&mut self, function: Function) -> FunctionId {
        let id = FunctionId(self.functions.len() as _);
        self.functions.push(function);
        id
    }

    pub fn global(&mut self, global: Global) -> GlobalId {
        let id = GlobalId(self.globals.len() as _);
        self.globals.push(global);
        id
    }

    pub fn get_expr(&self, expr: ExprId) -> &Expr {
        &self.exprs[expr.idx()]
    }

    pub fn finish_with_top_level_scope(mut self, top_level_scope: Scope) -> Ast {
        self.scopes.push(top_level_scope);
        Ast {
            exprs: self.exprs,
            calls: self.calls,
            functions: self.functions,
            scopes: self.scopes,
            globals: self.globals,
        }
    }
}

#[derive(Debug)]
pub enum TypeDef {
    Struct(StructDefinition),
    Enum(EnumDefinition),
}
impl TypeDef {
    pub fn name(&self) -> &str {
        match self {
            TypeDef::Struct(s) => &s.name,
            TypeDef::Enum(e) => &e.name,
        }
    }
    pub fn generic_count(&self) -> u8 {
        match self {
            TypeDef::Struct(s) => s.generic_count(),
            TypeDef::Enum(e) => e.generic_count(),
        }
    }
}

#[derive(Debug)]
pub struct Scope {
    pub definitions: DHashMap<String, (ExprId, Counts)>,
    pub impls: Vec<TraitImpl>,
}
impl Scope {
    pub fn empty() -> Self {
        Self {
            definitions: dmap::new(),
            impls: Vec::new(),
        }
    }
}

#[derive(Debug)]
pub struct ModuleItem {
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

#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
pub struct DeclId(u32);

#[derive(Debug, Clone, Copy)]
pub struct ExprExtra { pub idx: u32, pub count: u32 }

#[derive(Debug, Clone, Copy)]
pub struct ExprExtraSpans(u32, u32);

#[derive(Debug, Clone, Copy)]
pub struct Defs(u32);


#[derive(Debug, Clone)]
pub enum Item {
    Definition {
        name: String,
        name_span: TSpan,
        value: ExprId,
        counts: Counts,
    },
    Use(IdentPath),
    Impl(TraitImpl),
    Expr(Expr),
}

#[derive(Debug, Clone)]
pub struct TraitImpl {
    pub impl_generics: Vec<GenericDef>,
    pub trait_path: IdentPath,
    pub trait_generics: Option<(Vec<UnresolvedType>, TSpan)>,
    pub ty: UnresolvedType,
    pub functions: DHashMap<String, FunctionId>,
    pub impl_keyword_start: u32,
}
impl TraitImpl {
    pub fn header_span(&self) -> TSpan {
        TSpan::new(self.impl_keyword_start, self.ty.span().end)
    }
}

/*
#[derive(Debug, Clone)]
pub enum Definition {
    Function(FunctionId),
    Type(TypeId),
    Trait(TraitId),
    Module(ModuleId),
    Use(IdentPath),
    Const {
        ty: UnresolvedType,
        val: ExprId,
        counts: Counts,
    },
    Global(GlobalId),
}

impl Definition {
    /// Returns `true` if the definition is [`Trait`].
    ///
    /// [`Trait`]: Definition::Trait
    #[must_use]
    pub fn is_trait(&self) -> bool {
        matches!(self, Self::Trait(..))
    }
}
*/

// id!(u64, 8: FunctionId TypeId TraitId GlobalId CallId ConstId MemberAccessId);
// id!(u16, 2: VariantId);

#[derive(Debug, Clone)]
pub struct StructDefinition {
    pub name: String,
    pub generics: Vec<GenericDef>,
    pub members: Vec<(String, UnresolvedType, u32, u32)>,
    pub methods: DHashMap<String, FunctionId>
}
impl StructDefinition {
    pub fn generic_count(&self) -> u8 {
        self.generics.len() as u8
    }
}

#[derive(Debug, Clone)]
pub struct EnumDefinition {
    pub name: String,
    pub generics: Vec<GenericDef>,
    pub variants: Vec<(TSpan, String, Vec<UnresolvedType>)>,
    pub methods: DHashMap<String, FunctionId>,
}
impl EnumDefinition {
    pub fn generic_count(&self) -> u8 {
        self.generics.len() as u8
    }
}

#[derive(Debug)]
pub struct TraitDefinition {
    pub generics: Vec<GenericDef>,
    pub functions: DHashMap<String, (TSpan, Function)>,
}

#[derive(Debug)]
pub struct Global {
    pub ty: UnresolvedType,
    pub val: Option<(ExprId, Counts)>,
}

#[derive(Debug)]
pub struct Function {
    pub generics: Vec<GenericDef>,
    pub params: Vec<(String, UnresolvedType, u32, u32)>,
    pub varargs: bool,
    pub return_type: UnresolvedType,
    pub body: Option<ExprId>,
    pub counts: Counts,
    pub span: TSpan,
}

#[derive(Clone, Debug)]
pub struct GenericDef {
    pub name: TSpan,
    pub requirements: Vec<IdentPath>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Block {
        scope: ScopeId,
        items: ExprExtra,
        span: TSpan,
    },
    Declare {
        pat: ExprId,
        annotated_ty: UnresolvedType,
    },
    DeclareWithVal {
        pat: ExprId,
        annotated_ty: UnresolvedType,
        val: ExprId,
    },
    Function {
        id: FunctionId,
    },
    Type {
        id: TypeDefId,
    },
    Return {
        start: u32,
        val: ExprId,
    },
    ReturnUnit {
        start: u32,
    },
    IntLiteral(TSpan),
    FloatLiteral(TSpan),
    StringLiteral(TSpan),
    BoolLiteral {
        start: u32,
        val: bool,
    },
    EnumLiteral {
        span: TSpan,
        ident: TSpan,
        args: ExprExtra,
    },
    Record {
        span: TSpan,
        names: Vec<TSpan>,
        values: u32, // multiple values: expr extra (count of names)
    },
    Nested(TSpan, ExprId),
    Unit(TSpan),
    Variable {
        span: TSpan,
        id: IdentId,
    },
    Hole(u32), // underscore: _
    Array(TSpan, ExprExtra),
    Tuple(TSpan, ExprExtra),
    If {
        start: u32,
        cond: ExprId,
        then: ExprId,
    },
    IfElse {
        start: u32,
        cond: ExprId,
        then: ExprId,
        else_: ExprId
    },
    IfPat {
        start: u32,
        pat: ExprId,
        value: ExprId,
        then: ExprId,
    },
    IfPatElse {
        start: u32,
        pat: ExprId,
        value: ExprId,
        then: ExprId,
        else_: ExprId,
    },
    Match {
        span: TSpan,
        val: ExprId,
        extra_branches: u32, // each branch consists of a pat expr and a branch expr
        branch_count: u32,
    },
    While {
        start: u32,
        cond: ExprId,
        body: ExprId
    },
    /// while ... := ...
    WhilePat {
        start: u32,
        pat: ExprId,
        val: ExprId,
        body: ExprId,
    },
    FunctionCall(CallId),
    UnOp(u32, UnOp, ExprId),
    BinOp(Operator, ExprId, ExprId),
    MemberAccess {
        left: ExprId,
        name: TSpan,
        // id: MemberAccessId,
    },
    Index {
        expr: ExprId,
        idx: ExprId,
        end: u32,
    },
    TupleIdx {
        expr: ExprId,
        idx: u32,
        end: u32,
    },
    As(ExprId, UnresolvedType),
    Root(u32),
    Asm {
        span: TSpan,
        asm_str_span: TSpan,
        args: ExprExtra,
    },
}
impl Expr {
    pub fn is_block(&self) -> bool {
        matches!(self, Self::Block { .. })
    }
    pub fn span(&self, ast: &Ast) -> TSpan {
        // shorthands for getting start and end position of an ExprId
        let s = |r: &ExprId| ast[*r].start(ast);
        let e = |r: &ExprId| ast[*r].end(ast);

        match self {
            Expr::Block { span, .. }
            | Expr::StringLiteral(span) | Expr::IntLiteral(span) | Expr::FloatLiteral(span)
            | Expr::Record { span, .. }
            | Expr::Nested(span, _) 
            | Expr::Unit(span)
            | Expr::Variable { span, .. }
            | Expr::Array(span, _)
            | Expr::Tuple(span, _)
            | Expr::Match { span, .. }
            | Expr::EnumLiteral { span, .. }
            => *span,
            Expr::Function { id } => ast[*id].span,
            Expr::Declare { pat, annotated_ty, .. } => TSpan::new(s(pat), annotated_ty.span().end),
            Expr::DeclareWithVal { pat, val, .. } => TSpan::new(s(pat), e(val)),
            Expr::Return { start, val } => TSpan::new(*start, e(val)),
            Expr::ReturnUnit { start } => TSpan::new(*start, start+2),
            Expr::BoolLiteral { start, val } => TSpan::new(*start, start + if *val {4} else {5}),
            &Expr::Hole(start) => TSpan::new(start, start),
            Expr::If { start, then, .. }
            | Expr::IfPat { start, then, .. }
            => TSpan::new(*start, e(then) ),
            Expr::IfElse { start, else_, .. }
            | Expr::IfPatElse { start, else_, .. }
            => TSpan::new(*start, e(else_) ),
            Expr::While { start, body, .. }
            | Expr::WhilePat { start, body, .. }
            => TSpan::new(*start, e(body)),
            Expr::FunctionCall(call_id) => {
                let Call { called_expr, args: _, end } = &ast[*call_id];
                TSpan::new(s(called_expr), *end)
            }
            Expr::UnOp(start_or_end, un_op, expr) => if un_op.postfix() {
                TSpan::new(s(expr), *start_or_end)
            } else {
                TSpan::new(*start_or_end, e(expr))
            }
            Expr::BinOp(_, l, r) => TSpan::new(s(l), e(r)),
            Expr::MemberAccess { left, name, .. } => TSpan::new(s(left), name.end),
            Expr::Index { expr, idx: _, end } => TSpan::new(s(expr), *end),
            Expr::TupleIdx { expr, idx: _, end } => TSpan { start: s(expr), end: *end },
            Expr::As(val, ty) => TSpan::new(s(val), ty.span().end),
            Expr::Root(start) => TSpan::new(*start, *start + 3),
            Expr::Asm { span, .. } => *span
        }
    }
    pub fn span_in(&self, ast: &Ast, module: ModuleId) -> Span {
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

#[derive(Debug)]
pub struct Call {
    pub called_expr: ExprId,
    pub args: ExprExtra,
    pub end: u32,
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

