use std::ops::{Index, IndexMut};

use id::{id, ConstValueId, ModuleId};
use span::TSpan;
use types::{Primitive, IntType, FloatType};

use crate::{compiler::VarId, type_table::{LocalTypeId, TypeTable, LocalTypeIds, TypeInfo}, parser::ast::{FunctionId, GlobalId}};


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
        (self.index .. self.index + self.count).map(NodeId)
    }
}
impl Index<NodeIds> for HIR {
    type Output = [Node];
    fn index(&self, index: NodeIds) -> &Self::Output {
        &self.nodes[index.index as usize .. index.index as usize + index.count as usize]
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

#[derive(Debug, Clone, Copy)]
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
    StringLiteral(TSpan),

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
    AddressOf { inner: NodeId, value_ty: LocalTypeId },
    Deref { value: NodeId, deref_ty: LocalTypeId },

    Cast(CastId),
    Comparison(NodeId, NodeId, Comparison),
    Arithmetic(NodeId, NodeId, Arithmetic, LocalTypeId),

    TupleIndex {
        tuple_value: NodeId,
        index: u32,
        elem_ty: LocalTypeId,
    },
    ArrayIndex {
        array: NodeId,
        index: NodeId,
        elem_ty: LocalTypeId,
    },

    Return(NodeId),
    IfElse { cond: NodeId, then: NodeId, else_: NodeId, resulting_ty: LocalTypeId },
    Match { value: NodeId, branch_index: u32, pattern_index: u32, branch_count: u32 },
    While { cond: NodeId, body: NodeId },
    Call {
        function: (ModuleId, FunctionId),
        generics: LocalTypeIds,
        args: NodeIds,
        return_ty: LocalTypeId,
    },
}

#[derive(Debug, Clone)]
pub enum LValue {
    Invalid,
    Variable(VarId),
    Global(ModuleId, GlobalId),
    Deref(NodeId),
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
                TypeInfo::Array { element: _, count: count @ None } => *count = Some(0),
                _ => {}
            }
        }
        (HIR {
            nodes: self.nodes,
            lvalues: self.lvalues,
            patterns: self.patterns,
            vars: self.vars,
            casts: self.casts,
        }, self.types)
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
