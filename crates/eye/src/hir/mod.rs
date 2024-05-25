use std::ops::{Index, IndexMut};

use id::{id, ConstValueId, ModuleId};
use types::{FloatType, IntType, Primitive};

use crate::{
    compiler::VarId,
    parser::ast::{FunctionId, GlobalId},
    type_table::{LocalTypeId, LocalTypeIds, TypeInfo, TypeTable, VariantId},
};

/// High-level intermediate representation for a function. It is created during type checking and
/// contains all resolved identifiers and type information.
/// nodes must be non-empty and the last node is the root node
#[derive(Debug, Clone)]
pub struct HIR {
    nodes: Vec<Node>,
    lvalues: Vec<LValue>,
    patterns: Vec<Pattern>,
    pub vars: Vec<LocalTypeId>,
    casts: Vec<Cast>,
}
impl HIR {
    pub fn root_id(&self) -> NodeId {
        NodeId((self.nodes.len() - 1) as _)
    }

    pub fn dump(&self, node: NodeId, types: &TypeTable, indent_count: usize) {
        fn indent_n(n: usize) {
            for _ in 0..n {
                eprint!("  ");
            }
        }
        let indent = || indent_n(indent_count);
        match &self[node] {
            Node::Invalid => eprint!("(invalid)"),
            &Node::CheckPattern(pat, val) => {
                eprint!("(is ");
                self.dump(val, types, indent_count);
                eprint!(" ");
                self.dump_pattern(pat, types);
                eprint!(")");
            }
            Node::Block(ids) => {
                eprintln!("(");
                for id in ids.iter() {
                    indent_n(indent_count + 1);
                    self.dump(id, types, indent_count + 1);
                    eprintln!();
                }
                indent();
                eprint!(")");
            }
            Node::Unit => eprint!("(unit)"),
            &Node::IntLiteral { val, ty } => {
                eprint!("(int {val}): ");
                types.dump_type(ty);
            }
            &Node::FloatLiteral { val, ty } => {
                eprint!("(float {val}): ");
                types.dump_type(ty);
            }
            Node::BoolLiteral(b) => {
                eprint!("{b}")
            }
            &Node::ArrayLiteral { elems, array_ty } => {
                eprint!("(array ");
                for (i, elem) in elems.iter().enumerate() {
                    if i != 0 {
                        eprint!(" ");
                    }
                    self.dump(elem, types, indent_count);
                }
                eprint!("): [");
                types.dump_type(array_ty);
                eprint!("; {}]", elems.count);
            }
            Node::TupleLiteral { elems, elem_types } => {
                eprint!("(tuple ");
                for (i, (elem, ty)) in elems.iter().zip(elem_types.iter()).enumerate() {
                    if i != 0 {
                        eprint!(" ");
                    }
                    self.dump(elem, types, indent_count);
                    eprint!(": ");
                    types.dump_type(ty);
                }
                eprint!(")");
            }
            Node::StringLiteral(s) => eprint!("(string {s:?})"),
            Node::InferredEnumOrdinal(id) => eprint!("(enum-ordinal {})", id.0),
            &Node::Declare { pattern } => {
                eprint!("(decl ");
                self.dump_pattern(pattern, types);
                eprint!(")");
            }
            &Node::DeclareWithVal { pattern, val } => {
                eprint!("(decl ");
                self.dump_pattern(pattern, types);
                eprint!(" ");
                self.dump(val, types, indent_count);
                eprint!(")");
            }
            Node::Variable(id) => eprint!("(var {})", id.0),
            &Node::Assign(lval, val) => {
                eprint!("(assign ");
                self.dump_lvalue(lval, types, indent_count);
                eprint!(" ");
                self.dump(val, types, indent_count);
                eprint!(")");
            }
            &Node::Const { id, ty } => {
                eprint!("(const {}): ", id.0);
                types.dump_type(ty);
            }
            &Node::Negate(id, ty) => {
                eprint!("(neg");
                self.dump(id, types, indent_count);
                eprint!("): ");
                types.dump_type(ty);
            }
            &Node::Not(id) => {
                eprint!("(not ");
                self.dump(id, types, indent_count);
                eprint!(")");
            }
            &Node::AddressOf { inner, value_ty } => {
                eprint!("(addr ");
                self.dump(inner, types, indent_count);
                eprint!(": ");
                types.dump_type(value_ty);
                eprint!(")");
            }
            &Node::Deref { value, deref_ty } => {
                eprint!("(addr ");
                self.dump(value, types, indent_count);
                eprint!("): ");
                types.dump_type(deref_ty);
            }
            &Node::Cast(id) => {
                let cast = &self[id];
                eprint!("(cast ");
                match cast.cast_ty {
                    CastType::Invalid => eprint!("invalid"),
                    CastType::Noop => eprint!("noop"),
                    CastType::Int { from, to } => eprint!(
                        "(int {} {})",
                        <&str>::from(Primitive::from(from)),
                        <&str>::from(Primitive::from(to)),
                    ),
                    CastType::Float { from, to } => eprint!(
                        "(float {} {})",
                        <&str>::from(Primitive::from(from)),
                        <&str>::from(Primitive::from(to)),
                    ),
                    CastType::IntToFloat { from, to } => eprint!(
                        "(int-float {} {})",
                        <&str>::from(Primitive::from(from)),
                        <&str>::from(Primitive::from(to)),
                    ),
                    CastType::FloatToInt { from, to } => eprint!(
                        "(float-int {} {})",
                        <&str>::from(Primitive::from(from)),
                        <&str>::from(Primitive::from(to)),
                    ),
                    CastType::IntToPtr { from } => {
                        eprint!("(int-ptr {})", <&str>::from(Primitive::from(from)))
                    }
                    CastType::PtrToInt { to } => {
                        eprint!("(ptr-int {})", <&str>::from(Primitive::from(to)))
                    }
                    CastType::EnumToInt { from, to } => {
                        eprint!("(enum-int ");
                        types.dump_type(from);
                        eprint!(" {})", <&str>::from(Primitive::from(to)));
                    }
                }
                eprint!(" ");
                self.dump(cast.val, types, indent_count);
            }
            &Node::Comparison(l, r, cmp) => {
                let cmp = match cmp {
                    Comparison::Eq => "==",
                    Comparison::NE => "!=",
                    Comparison::LT => "<",
                    Comparison::GT => ">",
                    Comparison::LE => "<=",
                    Comparison::GE => ">=",
                    Comparison::And => "and",
                    Comparison::Or => "or",
                };
                eprint!("({cmp} ");
                self.dump(l, types, indent_count);
                eprint!(" ");
                self.dump(r, types, indent_count);
                eprint!(")");
            }
            &Node::Arithmetic(l, r, op, ty) => {
                let op = match op {
                    Arithmetic::Add => "+",
                    Arithmetic::Sub => "-",
                    Arithmetic::Mul => "*",
                    Arithmetic::Div => "/",
                    Arithmetic::Mod => "%",
                };
                eprint!("({op} ");
                self.dump(l, types, indent_count);
                eprint!(" ");
                self.dump(r, types, indent_count);
                eprint!("): ");
                types.dump_type(ty);
            }
            &Node::Element {
                tuple_value,
                index,
                elem_types,
            } => {
                eprint!("(element {index} ");
                self.dump(tuple_value, types, indent_count);
                eprint!(": (");
                for (i, elem) in elem_types.iter().enumerate() {
                    if i != 0 {
                        eprint!(", ");
                    }
                    types.dump_type(elem);
                }
                eprint!(")");
            }
            &Node::ArrayIndex {
                array,
                index,
                elem_ty,
            } => {
                eprint!(" ");
                self.dump(array, types, indent_count);
                eprint!("(index ");
                self.dump(index, types, indent_count);
                eprint!("): ");
                types.dump_type(elem_ty);
            }
            &Node::Return(val) => {
                eprint!("(return ");
                self.dump(val, types, indent_count);
                eprint!(")");
            }
            &Node::IfElse {
                cond,
                then,
                else_,
                resulting_ty,
            } => {
                eprint!("(if ");
                self.dump(cond, types, indent_count);
                eprintln!("");
                indent_n(indent_count + 1);
                self.dump(then, types, indent_count + 1);
                eprintln!();
                indent_n(indent_count + 1);
                self.dump(else_, types, indent_count + 1);
                eprintln!();
                indent();
                eprint!("): ");
                types.dump_type(resulting_ty);
            }
            &Node::Match {
                value,
                branch_index,
                pattern_index,
                branch_count,
            } => {
                eprint!("(match ");
                self.dump(value, types, indent_count);
                for i in 0..branch_count {
                    eprintln!();
                    indent();
                    let pattern = PatternId(pattern_index + i);
                    let branch = NodeId(branch_index + i);
                    self.dump_pattern(pattern, types);
                    eprint!(" ");
                    self.dump(branch, types, indent_count + 1);
                }
                eprint!("\n)")
            }
            &Node::While { cond, body } => {
                eprint!("(while ");
                self.dump(cond, types, indent_count);
                eprint!(" ");
                self.dump(body, types, indent_count);
                eprint!(")");
            }
            &Node::Call {
                function,
                generics,
                args,
                return_ty,
            } => {
                eprint!("(call {}:{} (", function.0 .0, function.1 .0);
                for (i, generic) in generics.iter().enumerate() {
                    if i != 0 {
                        eprint!(" ");
                    }
                    types.dump_type(generic);
                }
                eprint!(") ");
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        eprint!(" ");
                    }
                    self.dump(arg, types, indent_count);
                }
                eprint!("): ");
                types.dump_type(return_ty);
            }
            &Node::TypeProperty(ty, property) => {
                let prop = match property {
                    TypeProperty::Size => "size",
                    TypeProperty::Align => "align",
                    TypeProperty::Stride => "stride",
                };
                eprint!("(type_prop {prop} ");
                types.dump_type(ty);
                eprint!(")");
            }
        }
    }

    fn dump_pattern(&self, pattern: PatternId, types: &TypeTable) {
        match self[pattern] {
            Pattern::Invalid => eprint!("<invalid>"),
            Pattern::Variable(id) => {
                eprint!("(var {}): ", id.0);
                let var_ty = self.vars[id.idx()];
                types.dump_type(var_ty);
            }
            Pattern::Ignore => eprint!("_"),
            Pattern::Tuple(ids) => {
                eprint!("(");
                for (i, id) in ids.iter().enumerate() {
                    if i != 0 {
                        eprint!(" ");
                    }
                    self.dump_pattern(id, types);
                }
                eprint!(")");
            }
            Pattern::Int(signed, unsigned_val, ty) => {
                eprint!("(int ");
                if signed {
                    eprint!("-");
                }
                eprint!("{unsigned_val}): ");
                types.dump_type(ty);
            }
            Pattern::Bool(b) => eprint!("{b}"),
            Pattern::Range {
                min_max,
                ty: _,
                min_max_signs,
                inclusive,
            } => {
                if min_max_signs.0 {
                    eprint!("-")
                }
                eprint!("{} ", min_max.0);
                if min_max_signs.1 {
                    eprint!("-")
                }
                eprint!("{}", min_max.1);
                if inclusive {
                    eprint!(" inclusive");
                }
                eprint!(")");
            }
        }
    }

    fn dump_lvalue(&self, lval: LValueId, types: &TypeTable, indent_count: usize) {
        match self[lval] {
            LValue::Invalid => eprint!("(invalid)"),
            LValue::Variable(id) => eprint!("(var {})", id.0),
            LValue::Ignore => eprint!("(ignore)"),
            LValue::Global(module, id) => eprint!("(global {} {})", module.0, id.0),
            LValue::Deref(val) => {
                eprint!("(deref ");
                self.dump(val, types, indent_count);
                eprint!(")");
            }
            LValue::Member {
                ptr,
                index,
                elem_types,
            } => {
                eprint!("(member {index} ");
                self.dump(ptr, types, indent_count);
                eprint!("): (");
                for (i, elem) in elem_types.iter().enumerate() {
                    if i != 0 {
                        eprint!(", ");
                    }
                    types.dump_type(elem);
                }
                eprint!(")");
            }
        }
    }
}
id!(NodeId);
impl Index<NodeId> for HIR {
    type Output = Node;

    fn index(&self, index: NodeId) -> &Self::Output {
        &self.nodes[index.idx()]
    }
}
id!(CastId);
impl Index<CastId> for HIR {
    type Output = Cast;

    fn index(&self, index: CastId) -> &Self::Output {
        &self.casts[index.idx()]
    }
}
impl IndexMut<CastId> for HIR {
    fn index_mut(&mut self, index: CastId) -> &mut Self::Output {
        &mut self.casts[index.idx()]
    }
}
#[derive(Debug, Clone, Copy)]
pub struct NodeIds {
    pub index: u32,
    pub count: u32,
}
impl NodeIds {
    pub const EMPTY: Self = Self { index: 0, count: 0 };

    pub fn iter(self) -> impl Iterator<Item = NodeId> {
        (self.index..self.index + self.count).map(NodeId)
    }
}
impl Index<NodeIds> for HIR {
    type Output = [Node];
    fn index(&self, index: NodeIds) -> &Self::Output {
        &self.nodes[index.index as usize..index.index as usize + index.count as usize]
    }
}
id!(LValueId);
impl Index<LValueId> for HIR {
    type Output = LValue;
    fn index(&self, index: LValueId) -> &Self::Output {
        &self.lvalues[index.idx()]
    }
}
id!(PatternId);
impl Index<PatternId> for HIR {
    type Output = Pattern;

    fn index(&self, index: PatternId) -> &Self::Output {
        &self.patterns[index.idx()]
    }
}
#[derive(Debug, Clone, Copy)]
pub struct PatternIds {
    index: u32,
    count: u32,
}
impl PatternIds {
    pub fn iter(self) -> impl Iterator<Item = PatternId> {
        (self.index..self.count).map(PatternId)
    }
}

#[derive(Debug, Clone)]
pub enum Node {
    Invalid,

    /// used for places where patterns lead to conditional code.
    /// Checks the pattern against the value.
    CheckPattern(PatternId, NodeId),

    Block(NodeIds),

    Unit,
    IntLiteral {
        val: u128,
        ty: LocalTypeId,
    },
    FloatLiteral {
        val: f64,
        ty: LocalTypeId,
    },
    BoolLiteral(bool),
    ArrayLiteral {
        elems: NodeIds,
        array_ty: LocalTypeId,
    },
    TupleLiteral {
        // PERF(size): length has to match anyways, could only store it once
        elems: NodeIds,
        elem_types: LocalTypeIds,
    },
    StringLiteral(String),
    InferredEnumOrdinal(VariantId),

    Declare {
        pattern: PatternId,
    },
    DeclareWithVal {
        pattern: PatternId,
        val: NodeId,
    },
    Variable(VarId),
    Assign(LValueId, NodeId),

    Const {
        id: ConstValueId,
        ty: LocalTypeId,
    },

    Negate(NodeId, LocalTypeId),
    Not(NodeId),
    AddressOf {
        inner: NodeId,
        value_ty: LocalTypeId,
    },
    Deref {
        value: NodeId,
        deref_ty: LocalTypeId,
    },

    Cast(CastId),
    Comparison(NodeId, NodeId, Comparison),
    Arithmetic(NodeId, NodeId, Arithmetic, LocalTypeId),

    Element {
        tuple_value: NodeId,
        index: u32,
        elem_types: LocalTypeIds,
    },
    ArrayIndex {
        array: NodeId,
        index: NodeId,
        elem_ty: LocalTypeId,
    },

    Return(NodeId),
    IfElse {
        cond: NodeId,
        then: NodeId,
        else_: NodeId,
        resulting_ty: LocalTypeId,
    },
    Match {
        value: NodeId,
        branch_index: u32,
        pattern_index: u32,
        branch_count: u32,
    },
    While {
        cond: NodeId,
        body: NodeId,
    },
    Call {
        function: (ModuleId, FunctionId),
        generics: LocalTypeIds,
        args: NodeIds,
        return_ty: LocalTypeId,
    },
    TypeProperty(LocalTypeId, TypeProperty),
}

#[derive(Debug, Clone)]
pub enum LValue {
    Invalid,
    Variable(VarId),
    Ignore,
    Global(ModuleId, GlobalId),
    Deref(NodeId),
    Member {
        ptr: NodeId,
        index: u32,
        elem_types: LocalTypeIds,
    },
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Invalid,
    Variable(VarId),
    Ignore,
    Tuple(PatternIds),
    Int(bool, u128, LocalTypeId),
    Bool(bool),
    Range {
        min_max: (u128, u128),
        ty: LocalTypeId,
        min_max_signs: (bool, bool),
        inclusive: bool,
    },
}

#[derive(Debug, Clone)]
pub struct Cast {
    pub val: NodeId,
    pub cast_ty: CastType,
}

#[derive(Debug, Clone)]
pub enum CastType {
    Invalid,
    Noop,
    Int { from: IntType, to: IntType },
    Float { from: FloatType, to: FloatType },
    IntToFloat { from: IntType, to: FloatType },
    FloatToInt { from: FloatType, to: IntType },
    IntToPtr { from: IntType },
    PtrToInt { to: IntType },
    EnumToInt { from: LocalTypeId, to: IntType },
}

#[derive(Debug, Clone, Copy)]
pub enum Comparison {
    Eq,
    NE,
    LT,
    GT,
    LE,
    GE,
    And,
    Or,
}

#[derive(Debug, Clone, Copy)]
pub enum Arithmetic {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeProperty {
    Size,
    Align,
    Stride,
}

pub struct HIRBuilder {
    nodes: Vec<Node>,
    lvalues: Vec<LValue>,
    patterns: Vec<Pattern>,
    pub types: TypeTable,
    vars: Vec<LocalTypeId>,
    casts: Vec<Cast>,
}
impl HIRBuilder {
    pub fn new(types: TypeTable) -> Self {
        Self {
            nodes: Vec::new(),
            lvalues: Vec::new(),
            patterns: Vec::new(),
            types,
            vars: Vec::new(),
            casts: Vec::new(),
        }
    }

    pub fn finish(mut self, root: Node) -> (HIR, TypeTable) {
        self.nodes.push(root);
        for ty in self.types.type_infos_mut() {
            match ty {
                TypeInfo::Unknown => *ty = TypeInfo::Primitive(Primitive::Unit),
                TypeInfo::Integer => *ty = TypeInfo::Primitive(Primitive::I32),
                TypeInfo::Float => *ty = TypeInfo::Primitive(Primitive::F32),
                TypeInfo::Array {
                    element: _,
                    count: count @ None,
                } => *count = Some(0),
                _ => {}
            }
        }
        (
            HIR {
                nodes: self.nodes,
                lvalues: self.lvalues,
                patterns: self.patterns,
                vars: self.vars,
                casts: self.casts,
            },
            self.types,
        )
    }

    pub fn add(&mut self, node: Node) -> NodeId {
        let id = NodeId(self.nodes.len() as _);
        self.nodes.push(node);
        id
    }

    pub fn add_nodes(&mut self, nodes: impl IntoIterator<Item = Node>) -> NodeIds {
        let start = self.nodes.len();
        self.nodes.extend(nodes);
        let count = self.nodes.len() - start;
        NodeIds {
            index: start as _,
            count: count as _,
        }
    }

    pub fn add_lvalue(&mut self, lvalue: LValue) -> LValueId {
        let id = LValueId(self.lvalues.len() as _);
        self.lvalues.push(lvalue);
        id
    }

    pub fn add_invalid_nodes(&mut self, count: u32) -> NodeIds {
        let start = self.nodes.len();
        self.nodes.extend((0..count).map(|_| Node::Invalid));
        NodeIds {
            index: start as _,
            count,
        }
    }

    pub fn modify_node(&mut self, node_id: NodeId, node: Node) {
        self.nodes[node_id.0 as usize] = node;
    }

    pub fn add_pattern(&mut self, pattern: Pattern) -> PatternId {
        let id = PatternId(self.patterns.len() as _);
        self.patterns.push(pattern);
        id
    }

    pub fn add_var(&mut self, ty: LocalTypeId) -> VarId {
        let id = VarId(self.vars.len() as _);
        self.vars.push(ty);
        id
    }

    pub fn get_var(&mut self, id: VarId) -> LocalTypeId {
        self.vars[id.idx()]
    }

    pub fn add_patterns(&mut self, patterns: impl IntoIterator<Item = Pattern>) -> PatternIds {
        let start = self.patterns.len();
        self.patterns.extend(patterns);
        let count = self.patterns.len() - start;
        PatternIds {
            index: start as _,
            count: count as _,
        }
    }

    pub fn add_cast(&mut self, cast: Cast) -> CastId {
        let id = CastId(self.casts.len() as _);
        self.casts.push(cast);
        id
    }
}