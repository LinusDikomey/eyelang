use dmap::{self, DHashMap};
use id::ModuleId;
use span::{IdentPath, Span, TSpan};
use std::ops::Index;
use types::{Primitive, UnresolvedType};

use crate::parser::token::Operator;

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

/// Ast for a single file
#[derive(Debug)]
pub struct Ast {
    src: String,
    scopes: Vec<Scope>,
    top_level_scope: ScopeId,
    pub exprs: Vec<Expr>,
    calls: Vec<Call>,
    functions: Vec<Function>,
    types: Vec<TypeDef>,
    traits: Vec<TraitDefinition>,
    globals: Vec<Global>,
}
impl Ast {
    pub fn src(&self) -> &str {
        &self.src
    }

    pub fn scope_ids(&self) -> impl Iterator<Item = ScopeId> {
        (0..self.scopes.len()).map(|i| ScopeId(i as _))
    }

    pub fn scopes(&self) -> &[Scope] {
        &self.scopes
    }

    pub fn function_ids(&self) -> impl Iterator<Item = FunctionId> {
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

    pub fn top_level_scope(&self) -> &Scope {
        // the last scope is guaranteed to exist and to represent the top level scope of this Ast
        &self[self.top_level_scope]
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
impl Index<TSpan> for Ast {
    type Output = str;
    fn index(&self, index: TSpan) -> &Self::Output {
        &self.src[index.range()]
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
impl Index<ExprExtra> for Ast {
    type Output = [Expr];

    fn index(&self, index: ExprExtra) -> &Self::Output {
        &self.exprs[index.idx as usize..index.idx as usize + index.count as usize]
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
impl Index<TypeId> for Ast {
    type Output = TypeDef;

    fn index(&self, index: TypeId) -> &Self::Output {
        &self.types[index.idx()]
    }
}
impl Index<TraitId> for Ast {
    type Output = TraitDefinition;

    fn index(&self, index: TraitId) -> &Self::Output {
        &self.traits[index.idx()]
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
    types: Vec<TypeDef>,
    traits: Vec<TraitDefinition>,
    globals: Vec<Global>,
}
impl AstBuilder {
    pub fn new() -> Self {
        Self {
            scopes: Vec::new(),
            exprs: Vec::new(),
            calls: Vec::new(),
            functions: Vec::new(),
            types: Vec::new(),
            traits: Vec::new(),
            globals: Vec::new(),
        }
    }

    pub fn scope(&mut self, scope: Scope) -> ScopeId {
        let id = ScopeId(self.scopes.len() as _);
        self.scopes.push(scope);
        id
    }

    pub fn get_scope_mut(&mut self, id: ScopeId) -> &mut Scope {
        &mut self.scopes[id.idx()]
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
        ExprExtra {
            idx: idx as _,
            count: count as _,
        }
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

    pub fn type_def(&mut self, type_def: TypeDef) -> TypeId {
        let id = TypeId(self.types.len() as _);
        self.types.push(type_def);
        id
    }

    pub fn trait_def(&mut self, trait_def: TraitDefinition) -> TraitId {
        let id = TraitId(self.traits.len() as _);
        self.traits.push(trait_def);
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

    pub fn finish_with_top_level_scope(self, src: String, top_level_scope: ScopeId) -> Ast {
        Ast {
            src,
            scopes: self.scopes,
            top_level_scope,
            exprs: self.exprs,
            calls: self.calls,
            functions: self.functions,
            types: self.types,
            traits: self.traits,
            globals: self.globals,
        }
    }

    pub(super) fn assign_function_name(&mut self, id: FunctionId, associated_name: TSpan) {
        self.functions[id.idx()].associated_name = associated_name;
    }
}

#[derive(Debug)]
pub enum TypeDef {
    Struct(StructDefinition),
    Enum(EnumDefinition),
}
impl TypeDef {
    pub fn generic_count(&self) -> u8 {
        match self {
            TypeDef::Struct(s) => s.generic_count(),
            TypeDef::Enum(e) => e.generic_count(),
        }
    }
    pub fn span(&self, scopes: &[Scope]) -> TSpan {
        match self {
            Self::Struct(struct_def) => scopes[struct_def.scope.idx()].span,
            Self::Enum(enum_def) => scopes[enum_def.scope.idx()].span,
        }
    }
}

#[derive(Debug)]
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub definitions: DHashMap<String, Definition>,
    pub span: TSpan,
}
impl Scope {
    pub fn missing() -> Self {
        Self {
            parent: None,
            definitions: dmap::new(),
            span: TSpan::MISSING,
        }
    }

    pub fn from_generics(parent: ScopeId, src: &str, generics: &[GenericDef], span: TSpan) -> Self {
        Self {
            parent: Some(parent),
            definitions: generics
                .iter()
                .enumerate()
                .map(|(i, generic)| (generic.name(src).to_owned(), Definition::Generic(i as u8)))
                .collect(),
            span,
        }
    }
}

#[derive(Debug)]
pub enum Definition {
    Expr { value: ExprId, ty: UnresolvedType },
    Path(IdentPath),
    Global(GlobalId),
    Module(ModuleId),
    Generic(u8),
}

#[derive(Debug, Clone, Copy)]
pub struct ExprExtra {
    pub idx: u32,
    pub count: u32,
}
impl Iterator for ExprExtra {
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

#[derive(Debug, Clone)]
pub enum Item {
    Definition {
        name: String,
        name_span: TSpan,
        annotated_ty: UnresolvedType,
        value: ExprId,
    },
    Use(IdentPath),
    Expr(Expr),
}

/*
#[derive(Debug, Clone)]
pub struct TraitImpl {
    pub impl_generics: Box<[GenericDef]>,
    pub trait_path: IdentPath,
    pub trait_generics: Option<(Box<[UnresolvedType]>, TSpan)>,
    pub ty: UnresolvedType,
    pub functions: DHashMap<String, FunctionId>,
    pub impl_keyword_start: u32,
}
impl TraitImpl {
    pub fn header_span(&self) -> TSpan {
        TSpan::new(self.impl_keyword_start, self.ty.span().end)
    }
}
*/

#[derive(Debug, Clone)]
pub struct StructDefinition {
    pub generics: Box<[GenericDef]>,
    pub scope: ScopeId,
    pub members: Vec<(TSpan, UnresolvedType)>,
    pub methods: DHashMap<String, FunctionId>,
}
impl StructDefinition {
    pub fn generic_count(&self) -> u8 {
        self.generics.len() as u8
    }
}

#[derive(Debug, Clone)]
pub struct EnumDefinition {
    pub generics: Box<[GenericDef]>,
    pub scope: ScopeId,
    pub variants: Box<[EnumVariantDefinition]>,
    pub methods: DHashMap<String, FunctionId>,
}
impl EnumDefinition {
    pub fn generic_count(&self) -> u8 {
        self.generics.len() as u8
    }
}

#[derive(Debug, Clone)]
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
pub struct TraitDefinition {
    pub generics: Box<[GenericDef]>,
    pub scope: ScopeId,
    pub functions: Vec<(TSpan, Function)>,
    pub impls: Box<[Impl]>,
    pub associated_name: TSpan,
}
impl TraitDefinition {
    pub fn span(&self, scopes: &[Scope]) -> TSpan {
        scopes[self.scope.idx()].span
    }
}

#[derive(Debug)]
pub struct Impl {
    pub scope: ScopeId,
    pub generics: Box<[GenericDef]>,
    pub trait_generics: (Box<[UnresolvedType]>, TSpan),
    pub implemented_type: UnresolvedType,
    pub functions: Box<[(TSpan, FunctionId)]>,
}

#[derive(Debug)]
pub struct Global {
    pub name: Box<str>,
    pub scope: ScopeId,
    pub ty: UnresolvedType,
    pub val: Option<ExprId>,
    pub span: TSpan,
}

#[derive(Debug)]
pub struct Function {
    pub generics: Box<[GenericDef]>,
    pub params: Vec<(TSpan, UnresolvedType)>,
    pub varargs: bool,
    pub return_type: UnresolvedType,
    pub body: Option<ExprId>,
    pub scope: ScopeId,
    pub signature_span: TSpan,
    pub associated_name: TSpan,
}

#[derive(Clone, Debug)]
pub struct GenericDef {
    /// missing span indicates that this is a `Self` type in a trait definition
    pub(super) name: TSpan,
    pub bounds: Box<[TraitBound]>,
}
impl GenericDef {
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

#[derive(Debug, Clone)]
pub enum Expr {
    Block {
        scope: ScopeId,
        items: ExprExtra,
    },
    Nested(TSpan, ExprId),

    // ---------- value literals ----------
    Unit(TSpan),
    IntLiteral(TSpan),
    FloatLiteral(TSpan),
    BoolLiteral {
        start: u32,
        val: bool,
    },
    StringLiteral(TSpan),
    Array(TSpan, ExprExtra),
    Tuple(TSpan, ExprExtra),
    EnumLiteral {
        span: TSpan,
        ident: TSpan,
        args: ExprExtra,
    },

    // ---------- definition literals ----------
    Function {
        id: FunctionId,
    },
    Primitive {
        primitive: Primitive,
        start: u32,
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
    /// underscore: _ for ignoring values
    Hole(u32),

    // ---------- operations ----------
    UnOp(u32, UnOp, ExprId),
    BinOp(Operator, ExprId, ExprId),
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
    FunctionCall(CallId),

    // ---------- other ----------
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
        self.span_inner(
            &ast.exprs,
            &ast.functions,
            &ast.types,
            &ast.traits,
            &ast.calls,
            &ast.scopes,
        )
    }

    pub fn span_builder(&self, ast: &AstBuilder) -> TSpan {
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
        exprs: &[Expr],
        functions: &[Function],
        types: &[TypeDef],
        traits: &[TraitDefinition],
        calls: &[Call],
        scopes: &[Scope],
    ) -> TSpan {
        // shorthands for getting start and end position of an ExprId
        let s =
            |r: &ExprId| exprs[r.idx()].start_inner(exprs, functions, types, traits, calls, scopes);
        let e =
            |r: &ExprId| exprs[r.idx()].end_inner(exprs, functions, types, traits, calls, scopes);

        match self {
            Expr::StringLiteral(span)
            | Expr::IntLiteral(span)
            | Expr::FloatLiteral(span)
            | Expr::Nested(span, _)
            | Expr::Unit(span)
            | Expr::Ident { span, .. }
            | Expr::Array(span, _)
            | Expr::Tuple(span, _)
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
            Expr::Return { start, val } => TSpan::new(*start, e(val)),
            Expr::ReturnUnit { start } => TSpan::new(*start, start + 2),
            Expr::BoolLiteral { start, val } => {
                TSpan::new(*start, start + if *val { 4 } else { 5 })
            }
            &Expr::Hole(start) => TSpan::new(start, start),
            Expr::If { start, then, .. } | Expr::IfPat { start, then, .. } => {
                TSpan::new(*start, e(then))
            }
            Expr::IfElse { start, else_, .. } | Expr::IfPatElse { start, else_, .. } => {
                TSpan::new(*start, e(else_))
            }
            Expr::While { start, body, .. } | Expr::WhilePat { start, body, .. } => {
                TSpan::new(*start, e(body))
            }
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
            Expr::BinOp(_, l, r) => TSpan::new(s(l), e(r)),
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
            &Expr::Primitive { primitive, start } => {
                TSpan::new(start, start + <&str>::from(primitive).len() as u32 - 1)
            }
        }
    }

    pub fn span_in(&self, ast: &Ast, module: ModuleId) -> Span {
        self.span(ast).in_mod(module)
    }

    pub fn start(&self, ast: &Ast) -> u32 {
        self.start_inner(
            &ast.exprs,
            &ast.functions,
            &ast.types,
            &ast.traits,
            &ast.calls,
            &ast.scopes,
        )
    }

    pub fn end(&self, ast: &Ast) -> u32 {
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
        exprs: &[Expr],
        functions: &[Function],
        types: &[TypeDef],
        traits: &[TraitDefinition],
        calls: &[Call],
        scopes: &[Scope],
    ) -> u32 {
        //TODO: more efficient implementation
        self.span_inner(exprs, functions, types, traits, calls, scopes)
            .start
    }

    pub fn end_inner(
        &self,
        exprs: &[Expr],
        functions: &[Function],
        types: &[TypeDef],
        traits: &[TraitDefinition],
        calls: &[Call],
        scopes: &[Scope],
    ) -> u32 {
        //TODO: more efficient implementation
        self.span_inner(exprs, functions, types, traits, calls, scopes)
            .end
    }
}

#[derive(Debug)]
pub struct Call {
    pub called_expr: ExprId,
    pub open_paren_start: u32,
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
