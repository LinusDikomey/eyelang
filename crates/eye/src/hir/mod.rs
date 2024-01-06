use std::ops::Index;

use id::{id, ConstValueId};
use span::TSpan;

use crate::{compiler::VarId, type_table::{LocalTypeId, TypeTable}};

/// High-level intermediate representation for a function. It is created during type checking and
/// contains all resolved identifiers and type information.
/// nodes must be non-empty and the last node is the root node
#[derive(Debug)]
pub struct HIR {
    nodes: Vec<Node>,
    patterns: Vec<Pattern>,
    pub vars: Vec<LocalTypeId>,
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
#[derive(Debug, Clone, Copy)]
pub struct NodeIds {
    index: u32,
    count: u32,
}
impl NodeIds {
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
id!(PatternId);
impl Index<PatternId> for HIR {
    type Output = Pattern;

    fn index(&self, index: PatternId) -> &Self::Output {
        &self.patterns[index.idx()]
    }
}
#[derive(Debug)]
pub struct PatternIds {
    index: u32,
    count: u32,
}

#[derive(Debug)]
pub enum Node {
    Invalid,
    Block(NodeIds),
    Declare {
        pattern: PatternId,
    },
    DeclareWithVal {
        pattern: PatternId,
        val: NodeId,
    },
    Variable(VarId),
    Const(ConstValueId),
    Return(NodeId),
    IntLiteral {
        val: u128,
        ty: LocalTypeId,
    },
    FloatLiteral {
        val: f64,
        ty: LocalTypeId,
    },
    StringLiteral(TSpan),
    BoolLiteral(bool),
    Unit,
    Array(NodeIds),
}

#[derive(Debug)]
pub enum Pattern {
    Invalid,
    Variable(VarId),
    Ignore,
    Tuple(PatternIds),
    Int(bool, u128),
    Range {
        min_max: (u128, u128),
        min_max_signs: (bool, bool),
        inclusive: bool,
    },
}

pub struct HIRBuilder {
    nodes: Vec<Node>,
    patterns: Vec<Pattern>,
    pub types: TypeTable,
    vars: Vec<LocalTypeId>,
}
impl HIRBuilder {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            patterns: Vec::new(),
            types: TypeTable::new(),
            vars: Vec::new(),
        }
    }

    pub fn finish(mut self, root: Node) -> (HIR, TypeTable) {
        self.nodes.push(root);
        (HIR {
            nodes: self.nodes,
            patterns: self.patterns,
            vars: self.vars,
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
}
