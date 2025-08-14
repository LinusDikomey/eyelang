use dmap::{self, DHashMap};
use id::ModuleId;
use span::{Span, TSpan};
use std::{fmt::Debug, ops::Index};

pub use span::IdentPath;
pub use token::{AssignType, FloatLiteral, IntLiteral, Operator, Token, TokenType};
pub use types::{Primitive, UnresolvedType};

pub mod repr;

// All of these ids are local to their ast

id::id!(ScopeId);
id::id!(ExprId);
id::id!(CallId);
id::id!(FunctionId);
id::id!(TypeId);
id::id!(TraitId);
id::id!(GlobalId);
id::id!(IdentId);
id::id!(MemberAccessId);
id::id!(DefExprId);

/// Ast for a single file
#[derive(Debug)]
pub struct Ast<T: TreeToken = ()> {
    src: Box<str>,
    top_level_scope: ScopeId,
    scopes: Box<[Scope<T>]>,
    pub exprs: Box<[Expr<T>]>,
    def_exprs: Box<[(ExprId, UnresolvedType)]>,
    calls: Box<[Call<T>]>,
    functions: Box<[Function<T>]>,
    types: Box<[TypeDef<T>]>,
    traits: Box<[TraitDefinition<T>]>,
    globals: Box<[Global<T>]>,
}
impl<T: TreeToken> Ast<T> {
    pub fn src(&self) -> &str {
        &self.src
    }

    pub fn scope_ids(&self) -> impl Iterator<Item = ScopeId> {
        (0..self.scopes.len() as _).map(ScopeId)
    }

    pub fn scopes(&self) -> &[Scope<T>] {
        &self.scopes
    }

    pub fn function_ids(&self) -> impl Iterator<Item = FunctionId> + use<T> {
        (0..self.functions.len() as _).map(FunctionId)
    }

    pub fn type_ids(&self) -> impl Iterator<Item = TypeId> {
        (0..self.types.len() as _).map(TypeId)
    }

    pub fn global_ids(&self) -> impl Iterator<Item = GlobalId> {
        (0..self.globals.len() as _).map(GlobalId)
    }

    pub fn trait_ids(&self) -> impl Iterator<Item = TraitId> {
        (0..self.traits.len() as _).map(TraitId)
    }

    pub fn top_level_scope_id(&self) -> ScopeId {
        self.top_level_scope
    }

    pub fn top_level_scope(&self) -> &Scope<T> {
        // the last scope is guaranteed to exist and to represent the top level scope of this Ast
        &self[self.top_level_scope]
    }

    pub fn def_expr_count(&self) -> u32 {
        self.def_exprs.len() as _
    }

    pub fn function_count(&self) -> usize {
        self.functions.len()
    }

    pub fn type_count(&self) -> usize {
        self.types.len()
    }

    pub fn global_count(&self) -> usize {
        self.globals.len()
    }

    pub fn trait_count(&self) -> usize {
        self.traits.len()
    }
}
impl<T: TreeToken> Index<TSpan> for Ast<T> {
    type Output = str;
    fn index(&self, index: TSpan) -> &Self::Output {
        &self.src[index.range()]
    }
}
impl<T: TreeToken> Index<ScopeId> for Ast<T> {
    type Output = Scope<T>;
    fn index(&self, index: ScopeId) -> &Self::Output {
        &self.scopes[index.idx()]
    }
}
impl<T: TreeToken> Index<ExprId> for Ast<T> {
    type Output = Expr<T>;
    fn index(&self, index: ExprId) -> &Self::Output {
        &self.exprs[index.idx()]
    }
}
impl<T: TreeToken> Index<DefExprId> for Ast<T> {
    type Output = (ExprId, UnresolvedType);
    fn index(&self, index: DefExprId) -> &Self::Output {
        &self.def_exprs[index.0 as usize]
    }
}
impl<T: TreeToken> Index<ExprIds> for Ast<T> {
    type Output = [Expr<T>];

    fn index(&self, index: ExprIds) -> &Self::Output {
        &self.exprs[index.idx as usize..index.idx as usize + index.count as usize]
    }
}
impl<T: TreeToken> Index<CallId> for Ast<T> {
    type Output = Call<T>;
    fn index(&self, index: CallId) -> &Self::Output {
        &self.calls[index.idx()]
    }
}
impl<T: TreeToken> Index<FunctionId> for Ast<T> {
    type Output = Function<T>;

    fn index(&self, index: FunctionId) -> &Self::Output {
        &self.functions[index.idx()]
    }
}
impl<T: TreeToken> Index<TypeId> for Ast<T> {
    type Output = TypeDef<T>;

    fn index(&self, index: TypeId) -> &Self::Output {
        &self.types[index.idx()]
    }
}
impl<T: TreeToken> Index<TraitId> for Ast<T> {
    type Output = TraitDefinition<T>;

    fn index(&self, index: TraitId) -> &Self::Output {
        &self.traits[index.idx()]
    }
}
impl<T: TreeToken> Index<GlobalId> for Ast<T> {
    type Output = Global<T>;
    fn index(&self, index: GlobalId) -> &Self::Output {
        &self.globals[index.idx()]
    }
}

pub struct AstBuilder<T: TreeToken> {
    scopes: Vec<Scope<T>>,
    exprs: Vec<Expr<T>>,
    def_exprs: Vec<(ExprId, UnresolvedType)>,
    calls: Vec<Call<T>>,
    functions: Vec<Function<T>>,
    types: Vec<TypeDef<T>>,
    traits: Vec<TraitDefinition<T>>,
    globals: Vec<Global<T>>,
}
impl<T: TreeToken> Default for AstBuilder<T> {
    fn default() -> Self {
        Self {
            scopes: Vec::new(),
            exprs: Vec::new(),
            def_exprs: Vec::new(),
            calls: Vec::new(),
            functions: Vec::new(),
            types: Vec::new(),
            traits: Vec::new(),
            globals: Vec::new(),
        }
    }
}
impl<T: TreeToken> AstBuilder<T> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn scope(&mut self, scope: Scope<T>) -> ScopeId {
        let id = ScopeId(self.scopes.len() as _);
        self.scopes.push(scope);
        id
    }

    pub fn get_scope_mut(&mut self, id: ScopeId) -> &mut Scope<T> {
        &mut self.scopes[id.idx()]
    }

    pub fn expr(&mut self, expr: Expr<T>) -> ExprId {
        let id = ExprId(self.exprs.len() as _);
        self.exprs.push(expr);
        id
    }

    pub fn def_expr(&mut self, value: ExprId, ty: UnresolvedType) -> DefExprId {
        let id = DefExprId(self.def_exprs.len() as _);
        self.def_exprs.push((value, ty));
        id
    }

    pub fn exprs(&mut self, exprs: impl IntoIterator<Item = Expr<T>>) -> ExprIds {
        let idx = self.exprs.len();
        self.exprs.extend(exprs);
        let count = self.exprs.len() - idx;
        ExprIds {
            idx: idx as _,
            count: count as _,
        }
    }

    pub fn call(&mut self, call: Call<T>) -> CallId {
        let id = CallId(self.calls.len() as _);
        self.calls.push(call);
        id
    }

    pub fn function(&mut self, function: Function<T>) -> FunctionId {
        let id = FunctionId(self.functions.len() as _);
        self.functions.push(function);
        id
    }

    pub fn type_def(&mut self, type_def: TypeDef<T>) -> TypeId {
        let id = TypeId(self.types.len() as _);
        self.types.push(type_def);
        id
    }

    pub fn trait_def(&mut self, trait_def: TraitDefinition<T>) -> TraitId {
        let id = TraitId(self.traits.len() as _);
        self.traits.push(trait_def);
        id
    }

    pub fn global(&mut self, global: Global<T>) -> GlobalId {
        let id = GlobalId(self.globals.len() as _);
        self.globals.push(global);
        id
    }

    pub fn get_expr(&self, expr: ExprId) -> &Expr<T> {
        &self.exprs[expr.idx()]
    }

    pub fn finish_with_top_level_scope(self, src: Box<str>, top_level_scope: ScopeId) -> Ast<T> {
        Ast {
            src,
            top_level_scope,
            scopes: self.scopes.into_boxed_slice(),
            exprs: self.exprs.into_boxed_slice(),
            def_exprs: self.def_exprs.into_boxed_slice(),
            calls: self.calls.into_boxed_slice(),
            functions: self.functions.into_boxed_slice(),
            types: self.types.into_boxed_slice(),
            traits: self.traits.into_boxed_slice(),
            globals: self.globals.into_boxed_slice(),
        }
    }

    pub(super) fn assign_function_name(&mut self, id: FunctionId, associated_name: TSpan) {
        self.functions[id.idx()].associated_name = associated_name;
    }

    pub(super) fn assign_trait_name(&mut self, id: TraitId, associated_name: TSpan) {
        self.traits[id.idx()].associated_name = associated_name;
    }
}

pub trait TreeToken: Debug + Clone {
    type Opt<T: Debug + Clone>: Debug + Clone;
    type Either<A: Debug + Clone, B: Debug + Clone>: Debug + Clone;
    fn t(token: Token) -> Self;
    fn opt<T: Debug + Clone>(t: T) -> Self::Opt<T>;
    fn opt_none<T: Debug + Clone>() -> Self::Opt<T>;
    fn either_a<A: Debug + Clone, B: Debug + Clone>(a: A) -> Self::Either<A, B>;
    fn either_b<A: Debug + Clone, B: Debug + Clone>(b: B) -> Self::Either<A, B>;
}
impl TreeToken for () {
    type Opt<T: Debug + Clone> = ();
    type Either<A: Debug + Clone, B: Debug + Clone> = ();
    fn t(_token: Token) -> Self {}
    fn opt<T: Debug + Clone>(_t: T) -> Self::Opt<T> {}
    fn opt_none<T: Debug + Clone>() -> Self::Opt<T> {}
    fn either_a<A: Debug + Clone, B: Debug + Clone>(_a: A) -> Self::Either<A, B> {}
    fn either_b<A: Debug + Clone, B: Debug + Clone>(_b: B) -> Self::Either<A, B> {}
}
impl TreeToken for Token {
    type Opt<T: Debug + Clone> = Option<T>;
    type Either<A: Debug + Clone, B: Debug + Clone> = Either<A, B>;
    fn t(token: Token) -> Self {
        token
    }

    fn opt<T: Debug + Clone>(t: T) -> Self::Opt<T> {
        Some(t)
    }

    fn opt_none<T: Debug + Clone>() -> Self::Opt<T> {
        None
    }

    fn either_a<A: Debug + Clone, B: Debug + Clone>(a: A) -> Self::Either<A, B> {
        Either::A(a)
    }

    fn either_b<A: Debug + Clone, B: Debug + Clone>(b: B) -> Self::Either<A, B> {
        Either::B(b)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Either<A, B> {
    A(A),
    B(B),
}

#[derive(Debug)]
pub struct TypeDef<T: TreeToken = ()> {
    pub t_introducer: T,
    pub generics: Box<[GenericDef<T>]>,
    pub scope: ScopeId,
    pub methods: DHashMap<String, FunctionId>,
    pub impls: Box<[InherentImpl<T>]>,
    pub content: TypeContent,
}
impl<T: TreeToken> TypeDef<T> {
    pub fn generic_count(&self) -> u8 {
        self.generics.len() as u8
    }
    pub fn span(&self, scopes: &[Scope<T>]) -> TSpan {
        scopes[self.scope.idx()].span
    }
}

#[derive(Debug)]
pub enum TypeContent {
    Struct {
        members: Vec<StructMember>,
    },
    Enum {
        variants: Box<[EnumVariantDefinition]>,
    },
}

#[derive(Debug)]
pub struct StructMember {
    pub attributes: Box<[Attribute]>,
    pub name: TSpan,
    pub ty: UnresolvedType,
}

#[derive(Debug)]
pub struct Scope<T: TreeToken = ()> {
    pub parent: Option<ScopeId>,
    pub braces: T::Opt<(T, T)>,
    pub definitions: DHashMap<String, Definition<T>>,
    pub span: TSpan,
    pub has_errors: bool,
}
impl<T: TreeToken> Scope<T> {
    pub fn missing() -> Self {
        Self {
            parent: None,
            braces: T::opt_none(),
            definitions: dmap::new(),
            span: TSpan::MISSING,
            has_errors: true,
        }
    }

    pub fn from_generics(
        parent: ScopeId,
        src: &str,
        generics: &[GenericDef<T>],
        span: TSpan,
        parens: Option<(Token, Token)>,
    ) -> Self {
        Self {
            parent: Some(parent),
            braces: parens.map_or_else(T::opt_none, |(l, r)| T::opt((T::t(l), T::t(r)))),
            definitions: generics
                .iter()
                .enumerate()
                .map(|(i, generic)| (generic.name(src).to_owned(), Definition::Generic(i as u8)))
                .collect(),
            span,
            has_errors: false,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Definition<T: TreeToken = ()> {
    Expr {
        t_name: T,
        t_colon_colon: T::Either<T, (T, T)>,
        id: DefExprId,
    },
    Use {
        t_use: T,
        path: IdentPath,
    },
    Global(GlobalId),
    Module(ModuleId),
    Generic(u8),
}

#[derive(Debug, Clone, Copy)]
pub struct ExprIds {
    pub idx: u32,
    pub count: u32,
}
impl ExprIds {
    pub const EMPTY: Self = Self { idx: 0, count: 0 };
}
impl Iterator for ExprIds {
    type Item = ExprId;

    fn next(&mut self) -> Option<Self::Item> {
        self.count.checked_sub(1).map(|count| {
            self.count = count;
            let idx = self.idx;
            self.idx += 1;
            ExprId(idx)
        })
    }
}
impl ExactSizeIterator for ExprIds {
    fn len(&self) -> usize {
        self.count as usize
    }
}

pub struct Item<T: TreeToken> {
    #[allow(unused)] // TODO: remove when using attributes
    pub attributes: Box<[Attribute]>,
    pub value: ItemValue<T>,
}

pub enum ItemValue<T: TreeToken> {
    Definition {
        t_name: T,
        name: String,
        name_span: TSpan,
        t_colon_colon: T::Either<T, (T, T)>,
        annotated_ty: UnresolvedType,
        value: ExprId,
    },
    Use {
        t_use: T,
        path: IdentPath,
    },
    Expr(Expr<T>),
}

#[derive(Debug)]
pub struct Attribute {
    pub path: IdentPath,
    pub args: ExprIds,
    pub span: TSpan,
}

#[derive(Debug)]
pub struct EnumVariantDefinition {
    pub name_span: TSpan,
    pub args: Box<[UnresolvedType]>,
    pub end: u32,
}
impl EnumVariantDefinition {
    pub fn span(&self) -> TSpan {
        TSpan::new(self.name_span.start, self.end)
    }
}

#[derive(Debug)]
pub struct TraitDefinition<T: TreeToken = ()> {
    pub generics: Box<[GenericDef<T>]>,
    pub scope: ScopeId,
    pub functions: Vec<(TSpan, Function<T>)>,
    pub impls: Box<[Impl<T>]>,
    pub associated_name: TSpan,
}
impl<T: TreeToken> TraitDefinition<T> {
    pub fn span(&self, scopes: &[Scope<T>]) -> TSpan {
        scopes[self.scope.idx()].span
    }
}

pub type TraitFunctions = Box<[(TSpan, FunctionId)]>;

#[derive(Debug)]
pub struct Impl<T: TreeToken = ()> {
    pub t_impl: T,
    pub implemented_type: UnresolvedType,
    pub t_for: T,
    pub base: BaseImpl<T>,
}

#[derive(Debug)]
pub struct InherentImpl<T: TreeToken = ()> {
    pub implemented_trait: IdentPath,
    pub base: BaseImpl<T>,
}

#[derive(Debug)]
pub struct BaseImpl<T: TreeToken = ()> {
    pub scope: ScopeId,
    pub generics: Box<[GenericDef<T>]>,
    pub trait_generics: (Box<[UnresolvedType]>, TSpan),
    pub functions: TraitFunctions,
}

#[derive(Debug)]
pub struct Global<T: TreeToken = ()> {
    pub name: Box<str>,
    pub t_name: T,
    pub scope: ScopeId,
    pub t_colon_and_equals_or_colon_equals: T::Either<(T, T), T>,
    pub ty: UnresolvedType,
    pub val: ExprId,
    pub span: TSpan,
}

#[derive(Debug)]
pub struct Function<T: TreeToken = ()> {
    pub t_fn: T,
    pub generics: Box<[GenericDef<T>]>,
    pub t_parens: T::Opt<(T, T)>,
    pub params: Box<[(TSpan, UnresolvedType)]>,
    pub named_params: Box<[(TSpan, UnresolvedType, Option<ExprId>)]>,
    pub varargs: bool,
    pub t_varargs: T::Opt<T>,
    pub t_arrow: T::Opt<T>,
    pub return_type: UnresolvedType,
    pub t_colon: T::Opt<T>,
    pub t_extern: T::Opt<T>,
    pub body: Option<ExprId>,
    pub scope: ScopeId,
    pub signature_span: TSpan,
    pub associated_name: TSpan,
}

#[derive(Clone, Debug)]
pub struct GenericDef<T: TreeToken = ()> {
    /// missing span indicates that this is a `Self` type in a trait definition
    pub(super) name: TSpan,
    pub t_name: T::Opt<T>,
    pub bounds: Box<[TraitBound]>,
}
impl<T: TreeToken> GenericDef<T> {
    pub fn span(&self) -> TSpan {
        TSpan::new(
            self.name.start,
            self.bounds
                .last()
                .map_or(self.name.end, |bound| bound.generics_span.end),
        )
    }

    pub fn name<'s>(&self, src: &'s str) -> &'s str {
        if self.name == TSpan::MISSING {
            "Self"
        } else {
            &src[self.name.range()]
        }
    }
}

#[derive(Clone, Debug)]
pub struct TraitBound {
    pub path: IdentPath,
    pub generics: Box<[UnresolvedType]>,
    pub generics_span: TSpan,
}

#[derive(Debug)]
pub enum Expr<T: TreeToken = ()> {
    Error(TSpan),
    Block {
        t_open: T,
        scope: ScopeId,
        items: ExprIds,
        t_close: T,
    },
    Nested {
        span: TSpan,
        t_lparen: T,
        inner: ExprId,
        t_rparen: T,
    },

    // ---------- value literals ----------
    IntLiteral {
        span: TSpan,
        t: T,
    },
    FloatLiteral {
        span: TSpan,
        t: T,
    },
    StringLiteral {
        span: TSpan,
        t: T,
    },
    Array {
        span: TSpan,
        t_lbracket: T,
        elements: ExprIds,
        t_rbracket: T,
    },
    Tuple {
        span: TSpan,
        t_lparen: T,
        elements: ExprIds,
        t_rparen: T,
    },
    EnumLiteral {
        span: TSpan,
        t_dot: T,
        ident: TSpan,
        t_ident: T,
        t_parens: T::Opt<(T, T)>,
        args: ExprIds,
    },

    // ---------- definition literals ----------
    Function {
        id: FunctionId,
    },
    Primitive {
        primitive: Primitive,
        start: u32,
        t: T,
    },
    Type {
        id: TypeId,
    },
    Trait {
        id: TraitId,
    },

    // ---------- variables and names ----------
    Ident {
        span: TSpan,
        t: T,
    },
    Declare {
        pat: ExprId,
        t_colon: T,
        annotated_ty: UnresolvedType,
    },
    DeclareWithVal {
        pat: ExprId,
        t_colon_and_equals_or_colon_equals: T::Either<(T, T), T>,
        annotated_ty: UnresolvedType,
        val: ExprId,
    },
    /// underscore: _ for ignoring values
    Hole {
        loc: u32,
        t: T,
    },

    // ---------- operations ----------
    UnOp(u32, UnOp, ExprId),
    BinOp {
        t_op: T,
        op: Operator,
        l: ExprId,
        r: ExprId,
    },
    As(ExprId, UnresolvedType),
    Root(u32),

    // ---------- members and paths ----------
    MemberAccess {
        left: ExprId,
        name: TSpan,
    },
    Index {
        expr: ExprId,
        idx: ExprId,
        end: u32,
    },
    TupleIdx {
        left: ExprId,
        idx: u32,
        end: u32,
    },

    // ---------- return ----------
    ReturnUnit {
        start: u32,
    },
    Return {
        start: u32,
        t_ret: T,
        val: ExprId,
    },

    // ---------- control flow ----------
    If {
        start: u32,
        cond: ExprId,
        then: ExprId,
    },
    IfElse {
        start: u32,
        cond: ExprId,
        then: ExprId,
        else_: ExprId,
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
        body: ExprId,
    },
    /// while ... := ...
    WhilePat {
        start: u32,
        pat: ExprId,
        val: ExprId,
        body: ExprId,
    },
    For {
        start: u32,
        pat: ExprId,
        iter: ExprId,
        body: ExprId,
    },
    FunctionCall(CallId),

    // ---------- other ----------
    Asm {
        span: TSpan,
        asm_str_span: TSpan,
        args: ExprIds,
    },
    Break {
        start: u32,
    },
    Continue {
        start: u32,
    },
}
impl<T: TreeToken> Expr<T> {
    pub fn is_block(&self) -> bool {
        matches!(self, Self::Block { .. })
    }

    pub fn span(&self, ast: &Ast<T>) -> TSpan {
        self.span_inner(
            &ast.exprs,
            &ast.functions,
            &ast.types,
            &ast.traits,
            &ast.calls,
            &ast.scopes,
        )
    }

    pub fn span_builder(&self, ast: &AstBuilder<T>) -> TSpan {
        self.span_inner(
            &ast.exprs,
            &ast.functions,
            &ast.types,
            &ast.traits,
            &ast.calls,
            &ast.scopes,
        )
    }

    fn span_inner(
        &self,
        exprs: &[Self],
        functions: &[Function<T>],
        types: &[TypeDef<T>],
        traits: &[TraitDefinition<T>],
        calls: &[Call<T>],
        scopes: &[Scope<T>],
    ) -> TSpan {
        // shorthands for getting start and end position of an ExprId
        let s =
            |r: &ExprId| exprs[r.idx()].start_inner(exprs, functions, types, traits, calls, scopes);
        let e =
            |r: &ExprId| exprs[r.idx()].end_inner(exprs, functions, types, traits, calls, scopes);

        match self {
            Expr::Error(span)
            | Expr::StringLiteral { span, .. }
            | Expr::IntLiteral { span, .. }
            | Expr::FloatLiteral { span, .. }
            | Expr::Nested { span, .. }
            | Expr::Ident { span, .. }
            | Expr::Array { span, .. }
            | Expr::Tuple { span, .. }
            | Expr::Match { span, .. }
            | Expr::EnumLiteral { span, .. } => *span,
            Expr::Block { scope, .. } => scopes[scope.idx()].span,
            Expr::Function { id } => scopes[functions[id.idx()].scope.idx()].span,
            Expr::Type { id } => types[id.idx()].span(scopes),
            Expr::Trait { id } => traits[id.idx()].span(scopes),
            Expr::Declare {
                pat, annotated_ty, ..
            } => TSpan::new(s(pat), annotated_ty.span().end),
            Expr::DeclareWithVal { pat, val, .. } => TSpan::new(s(pat), e(val)),
            Expr::Return { start, val, .. } => TSpan::new(*start, e(val)),
            Expr::ReturnUnit { start } => TSpan::new(*start, start + 3),
            &Expr::Hole { loc, .. } => TSpan::new(loc, loc + 1),
            Expr::If { start, then, .. } | Expr::IfPat { start, then, .. } => {
                TSpan::new(*start, e(then))
            }
            Expr::IfElse { start, else_, .. } | Expr::IfPatElse { start, else_, .. } => {
                TSpan::new(*start, e(else_))
            }
            Expr::While { start, body, .. }
            | Expr::WhilePat { start, body, .. }
            | Expr::For { start, body, .. } => TSpan::new(*start, e(body)),
            Expr::FunctionCall(call_id) => {
                let Call {
                    called_expr, end, ..
                } = &calls[call_id.idx()];
                TSpan::new(s(called_expr), *end)
            }
            Expr::UnOp(start_or_end, un_op, expr) => {
                if un_op.postfix() {
                    TSpan::new(s(expr), *start_or_end)
                } else {
                    TSpan::new(*start_or_end, e(expr))
                }
            }
            Expr::BinOp { l, r, .. } => TSpan::new(s(l), e(r)),
            Expr::MemberAccess { left, name, .. } => TSpan::new(s(left), name.end),
            Expr::Index { expr, idx: _, end } => TSpan::new(s(expr), *end),
            Expr::TupleIdx {
                left: expr,
                idx: _,
                end,
            } => TSpan::new(s(expr), *end),
            Expr::As(val, ty) => TSpan::new(s(val), ty.span().end),
            Expr::Root(start) => TSpan::new(*start, *start + 3),
            Expr::Asm { span, .. } => *span,
            &Expr::Primitive {
                primitive, start, ..
            } => TSpan::new(start, start + <&str>::from(primitive).len() as u32 - 1),
            &Expr::Break { start } => TSpan::new(start, start + 4),
            &Expr::Continue { start } => TSpan::new(start, start + 7),
        }
    }

    pub fn span_in(&self, ast: &Ast<T>, module: ModuleId) -> Span {
        self.span(ast).in_mod(module)
    }

    pub fn start(&self, ast: &Ast<T>) -> u32 {
        self.start_inner(
            &ast.exprs,
            &ast.functions,
            &ast.types,
            &ast.traits,
            &ast.calls,
            &ast.scopes,
        )
    }

    pub fn end(&self, ast: &Ast<T>) -> u32 {
        self.end_inner(
            &ast.exprs,
            &ast.functions,
            &ast.types,
            &ast.traits,
            &ast.calls,
            &ast.scopes,
        )
    }

    pub fn start_inner(
        &self,
        exprs: &[Self],
        functions: &[Function<T>],
        types: &[TypeDef<T>],
        traits: &[TraitDefinition<T>],
        calls: &[Call<T>],
        scopes: &[Scope<T>],
    ) -> u32 {
        //TODO: more efficient implementation
        self.span_inner(exprs, functions, types, traits, calls, scopes)
            .start
    }

    pub fn end_inner(
        &self,
        exprs: &[Self],
        functions: &[Function<T>],
        types: &[TypeDef<T>],
        traits: &[TraitDefinition<T>],
        calls: &[Call<T>],
        scopes: &[Scope<T>],
    ) -> u32 {
        //TODO: more efficient implementation
        self.span_inner(exprs, functions, types, traits, calls, scopes)
            .end
    }
}

#[derive(Debug)]
pub struct Call<T: TreeToken = ()> {
    pub called_expr: ExprId,
    pub t_lparen: T,
    pub open_paren_start: u32,
    pub args: ExprIds,
    pub named_args: Vec<(TSpan, ExprId)>,
    pub t_rparen: T,
    pub end: u32,
}
impl Call {
    pub fn total_arg_count(&self) -> u32 {
        self.args.count + self.named_args.len() as u32
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
