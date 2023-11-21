use std::ops::Index;
use id::{FunctionId, TypeId, TraitId, GlobalId, ScopeId, ModuleId, TypeDefId};
use span::{TSpan, Span, IdentPath};
use dmap::{self, DHashMap};
use types::{Primitive, UnresolvedType};

use crate::{parser::{IdentId, Counts, token::Operator}, Resolvable, Def};

pub mod repr;

id::id!(ExprId);
id::id!(CallId);

/// Ast for a single item
pub struct Ast {
    exprs: Vec<Expr>,
    calls: Vec<Call>
}
impl Ast {
    fn new() -> Self {
        Self {
            exprs: Vec::new(),
            calls: Vec::new(),
        }
    }
}
impl Index<ExprId> for Ast {
    type Output = Expr;
    fn index(&self, index: ExprId) -> &Self::Output {
        &self.exprs[index.idx()]
    }
}

/*
pub struct Ast {
    pub modules: Vec<Module>,
    pub sources: Vec<(String, PathBuf)>,
    exprs: Vec<Expr>,
    extra: Vec<ExprId>,
    defs: Vec<DHashMap<String, Definition>>,
    pub functions: Vec<Function>,
    pub types: Vec<TypeDef>,
    pub traits: Vec<TraitDefinition>,
    pub globals: Vec<GlobalDefinition>,
    pub calls: Vec<Call>,
    pub member_access_count: u64,
}
impl Ast {
    pub fn new() -> Self {
        Self {
            modules: Vec::new(),
            sources: Vec::new(),
            exprs: Vec::new(),
            extra: Vec::new(),
            defs: Vec::new(),
            functions: Vec::new(),
            types: Vec::new(),
            traits: Vec::new(),
            globals: Vec::new(),
            calls: Vec::new(),
            member_access_count: 0,
        }
    }
    pub fn expr_count(&self) -> usize {
        self.exprs.len()
    }
    pub fn add_expr(&mut self, expr: Expr) -> ExprId {
        let r = ExprId(self.exprs.len() as u32);
        self.exprs.push(expr);
        r
    }
    pub fn add_defs(&mut self, defs: DHashMap<String, Definition>) -> Defs {
        //defs.shrink_to_fit(); //PERF: test performance gains/losses of this
        let idx = self.defs.len();
        self.defs.push(defs);
        Defs(idx as u32)
    }

    pub fn add_extra(&mut self, extra: &[ExprId]) -> ExprExtra {
        let idx = ExprExtra { idx: self.extra.len() as u32, count: extra.len() as u32 };
        self.extra.extend(extra);
        idx
    }

    pub fn add_module(&mut self, module: Module, src: String, path: PathBuf) -> ModuleId {
        let id = ModuleId(self.modules.len() as u32);
        self.modules.push(module);
        self.sources.push((src, path));
        id
    }

    pub fn add_empty_module(&mut self, path: PathBuf, root_module: ModuleId) -> ModuleId {
        let empty = Module::empty(self, root_module);
        self.add_module(empty, String::new(), path)
    }

    pub fn add_empty_root_module(&mut self, path: PathBuf) -> ModuleId {
        let empty = Module::empty(self, ModuleId(0)); // the zero id is replaced right below
        let id = self.add_module(empty, String::new(), path);
        self[id].root_module = id;
        id
    }

    pub fn update(&mut self, id: ModuleId, module: Module, src: String, path: PathBuf) {
        self.modules[id.0 as usize] = module;
        self.sources[id.0 as usize] = (src, path);
    }

    pub fn add_func(&mut self, function: Function) -> FunctionId {
        self.functions.push(function);
        FunctionId((self.functions.len() - 1) as _)
    }

    pub fn add_type(&mut self, ty: TypeDef) -> TypeId {
        self.types.push(ty);
        TypeId((self.types.len() - 1) as _)
    }

    pub fn add_trait(&mut self, trait_def: TraitDefinition) -> TraitId {
        self.traits.push(trait_def);
        TraitId((self.traits.len() - 1) as _)
    }

    pub fn add_global(&mut self, global: GlobalDefinition) -> GlobalId {
        self.globals.push(global);
        GlobalId((self.globals.len() - 1) as _)
    }
    
    /*
    pub fn add_call(&mut self, call: Call) -> CallId {
        self.calls.push(call);
        CallId((self.calls.len() - 1) as _)
    }

    pub fn member_access_id(&mut self) -> MemberAccessId {
        self.member_access_count += 1;
        MemberAccessId(self.member_access_count - 1)
    }
    */
    
    pub fn src(&self, id: ModuleId) -> (&str, &Path) {
        let t = &self.sources[id.0 as usize];
        (&t.0, &t.1)
    }
}
impl Index<ExprId> for Ast {
    type Output = Expr;

    fn index(&self, index: ExprId) -> &Self::Output {
        &self.exprs[index.0 as usize]    
    }   
}
impl IndexMut<ExprId> for Ast {
    fn index_mut(&mut self, index: ExprId) -> &mut Self::Output {
        &mut self.exprs[index.0 as usize]
    }
}
impl Index<Defs> for Ast {
    type Output = DHashMap<String, Definition>;

    fn index(&self, index: Defs) -> &Self::Output {
        &self.defs[index.0 as usize]
    }
}
impl IndexMut<Defs> for Ast {
    fn index_mut(&mut self, index: Defs) -> &mut Self::Output {
        &mut self.defs[index.0 as usize]
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
impl Index<ExprExtra> for Ast {
    type Output = [ExprId];

    fn index(&self, index: ExprExtra) -> &Self::Output {
        &self.extra[index.idx as usize .. index.idx as usize + index.count as usize]
    }
}
impl Index<FunctionId> for Ast {
    type Output = Function;

    fn index(&self, id: FunctionId) -> &Self::Output {
        &self.functions[id.idx()]
    }
}
impl Index<TypeId> for Ast {
    type Output = TypeDef;

    fn index(&self, id: TypeId) -> &Self::Output {
        &self.types[id.idx()]
    }
}
impl Index<TraitId> for Ast {
    type Output = TraitDefinition;

    fn index(&self, id: TraitId) -> &Self::Output {
        &self.traits[id.idx()]
    }
}
impl Index<GlobalId> for Ast {
    type Output = GlobalDefinition;

    fn index(&self, id: GlobalId) -> &Self::Output {
        &self.globals[id.idx()]
    }
}
impl Index<CallId> for Ast {
    type Output = Call;

    fn index(&self, index: CallId) -> &Self::Output {
        &self.calls[index.idx()]
    }
}
*/

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

#[derive(Debug, Clone)]
pub struct Scope {
    pub definitions: DHashMap<String, ModuleItem>,
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
    Definition { name: String, name_span: TSpan, def: Definition },
    Impl(TraitImpl),
    Expr(ExprId)
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

#[derive(Debug, Clone)]
pub struct TraitDefinition {
    pub generics: Vec<GenericDef>,
    pub functions: DHashMap<String, (TSpan, Function)>,
}

pub struct GlobalDefinition {
    pub ty: UnresolvedType,
    pub val: Option<(ExprId, Counts)>,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub generics: Vec<GenericDef>,
    pub params: Vec<(String, UnresolvedType, u32, u32)>,
    //pub vararg: Option<(String, UnresolvedType, u32, u32)>,
    pub varargs: bool,
    pub return_type: UnresolvedType,
    pub body: Option<Ast>,
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
        scope: Scope,
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
    Cast(TSpan, UnresolvedType, ExprId),
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
            | Expr::Cast(span, _, _)    
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

