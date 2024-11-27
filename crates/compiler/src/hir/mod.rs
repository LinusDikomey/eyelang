use std::ops::{Index, IndexMut};

use id::{id, ConstValueId, ModuleId};
use types::{FloatType, IntType, Primitive};

use crate::{
    compiler::{Generics, VarId},
    parser::{
        ast::{FunctionId, GlobalId, TraitId},
        token::AssignType,
    },
    types::{LocalTypeId, LocalTypeIds, OrdinalType, TypeTable, VariantId},
    Compiler,
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
    pub trait_calls: Vec<Option<(ModuleId, FunctionId)>>,
}
impl HIR {
    pub fn root_id(&self) -> NodeId {
        NodeId((self.nodes.len() - 1) as _)
    }

    pub fn dump(&self, node: NodeId, compiler: &Compiler, types: &TypeTable, indent_count: usize) {
        fn indent_n(n: usize) {
            for _ in 0..n {
                eprint!("  ");
            }
        }
        let indent = || indent_n(indent_count);
        match &self[node] {
            Node::Invalid => eprint!("(invalid)"),
            Node::Block(ids) => {
                eprintln!("(");
                for id in ids.iter() {
                    indent_n(indent_count + 1);
                    self.dump(id, compiler, types, indent_count + 1);
                    eprintln!();
                }
                indent();
                eprint!(")");
            }
            Node::Unit => eprint!("(unit)"),
            &Node::IntLiteral { val, ty } => {
                eprint!("(int {val}): ");
                types.dump_type(compiler, ty);
            }
            &Node::FloatLiteral { val, ty } => {
                eprint!("(float {val}): ");
                types.dump_type(compiler, ty);
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
                    self.dump(elem, compiler, types, indent_count);
                }
                eprint!("): [");
                types.dump_type(compiler, array_ty);
                eprint!("; {}]", elems.count);
            }
            Node::TupleLiteral { elems, elem_types } => {
                eprint!("(tuple ");
                for (i, (elem, ty)) in elems.iter().zip(elem_types.iter()).enumerate() {
                    if i != 0 {
                        eprint!(" ");
                    }
                    self.dump(elem, compiler, types, indent_count);
                    eprint!(": ");
                    types.dump_type(compiler, ty);
                }
                eprint!(")");
            }
            &Node::EnumLiteral {
                elems,
                elem_types,
                enum_ty,
            } => {
                eprint!("enum-literal ");
                for (i, (elem, ty)) in elems.iter().zip(elem_types.iter()).enumerate() {
                    if i != 0 {
                        eprint!(" ");
                    }
                    self.dump(elem, compiler, types, indent_count);
                    eprint!(": ");
                    types.dump_type(compiler, ty);
                }
                eprint!("): ");
                types.dump_type(compiler, enum_ty);
            }
            Node::StringLiteral(s) => eprint!("(string {s:?})"),
            Node::InferredEnumOrdinal(id) => eprint!("(enum-ordinal {})", id.0),
            &Node::Declare { pattern } => {
                eprint!("(decl ");
                self.dump_pattern(pattern, compiler, types);
                eprint!(")");
            }
            &Node::DeclareWithVal { pattern, val } => {
                eprint!("(decl ");
                self.dump_pattern(pattern, compiler, types);
                eprint!(" ");
                self.dump(val, compiler, types, indent_count);
                eprint!(")");
            }
            Node::Variable(id) => eprint!("(var {})", id.0),
            &Node::Global(module, id, ty) => {
                eprint!("(global {}:{}): ", module.0, id.0);
                types.dump_type(compiler, ty);
            }
            &Node::Assign(lval, val, assign_ty, ty) => {
                let op = match assign_ty {
                    AssignType::Assign => "",
                    AssignType::AddAssign => "-add",
                    AssignType::SubAssign => "-sub",
                    AssignType::MulAssign => "-mul",
                    AssignType::DivAssign => "-div",
                    AssignType::ModAssign => "-mod",
                };
                eprint!("(assign{op} ");
                self.dump_lvalue(lval, compiler, types, indent_count);
                eprint!(": ");
                types.dump_type(compiler, ty);
                eprint!(" ");
                self.dump(val, compiler, types, indent_count);
                eprint!(")");
            }
            &Node::Const { id, ty } => {
                eprint!("(const {}): ", id.0);
                types.dump_type(compiler, ty);
            }
            &Node::Negate(id, ty) => {
                eprint!("(neg");
                self.dump(id, compiler, types, indent_count);
                eprint!("): ");
                types.dump_type(compiler, ty);
            }
            &Node::Not(id) => {
                eprint!("(not ");
                self.dump(id, compiler, types, indent_count);
                eprint!(")");
            }
            &Node::AddressOf { value, value_ty } => {
                eprint!("(addr ");
                self.dump_lvalue(value, compiler, types, indent_count);
                eprint!(": ");
                types.dump_type(compiler, value_ty);
                eprint!(")");
            }
            &Node::Deref { value, deref_ty } => {
                eprint!("(deref ");
                self.dump(value, compiler, types, indent_count);
                eprint!("): ");
                types.dump_type(compiler, deref_ty);
            }
            &Node::Promote { value, variable } => {
                eprint!("(promote ");
                self.dump(value, compiler, types, indent_count);
                eprint!(" into (var {}))", variable.0);
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
                        types.dump_type(compiler, from);
                        eprint!(" {})", <&str>::from(Primitive::from(to)));
                    }
                }
                eprint!(" ");
                self.dump(cast.val, compiler, types, indent_count);
            }
            &Node::Comparison {
                l,
                r,
                cmp,
                compared: _,
            } => {
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
                self.dump(l, compiler, types, indent_count);
                eprint!(" ");
                self.dump(r, compiler, types, indent_count);
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
                self.dump(l, compiler, types, indent_count);
                eprint!(" ");
                self.dump(r, compiler, types, indent_count);
                eprint!("): ");
                types.dump_type(compiler, ty);
            }
            &Node::Element {
                tuple_value,
                index,
                elem_types,
            } => {
                eprint!("(element {index} ");
                self.dump(tuple_value, compiler, types, indent_count);
                eprint!(": (");
                for (i, elem) in elem_types.iter().enumerate() {
                    if i != 0 {
                        eprint!(", ");
                    }
                    types.dump_type(compiler, elem);
                }
                eprint!(")");
            }
            &Node::ArrayIndex {
                array,
                index,
                elem_ty,
            } => {
                eprint!(" ");
                self.dump(array, compiler, types, indent_count);
                eprint!("(index ");
                self.dump(index, compiler, types, indent_count);
                eprint!("): ");
                types.dump_type(compiler, elem_ty);
            }
            &Node::Return(val) => {
                eprint!("(return ");
                self.dump(val, compiler, types, indent_count);
                eprint!(")");
            }
            &Node::IfElse {
                cond,
                then,
                else_,
                resulting_ty,
            } => {
                eprint!("(if ");
                self.dump(cond, compiler, types, indent_count);
                eprintln!();
                indent_n(indent_count + 1);
                self.dump(then, compiler, types, indent_count + 1);
                eprintln!();
                indent_n(indent_count + 1);
                self.dump(else_, compiler, types, indent_count + 1);
                eprintln!();
                indent();
                eprint!("): ");
                types.dump_type(compiler, resulting_ty);
            }
            &Node::IfPatElse {
                pat,
                val,
                then,
                else_,
                resulting_ty,
            } => {
                eprint!("(if-pat ");
                self.dump_pattern(pat, compiler, types);
                eprint!(" ");
                self.dump(val, compiler, types, indent_count);
                eprintln!();
                indent_n(indent_count + 1);
                self.dump(then, compiler, types, indent_count + 1);
                eprintln!();
                indent_n(indent_count + 1);
                self.dump(else_, compiler, types, indent_count + 1);
                eprintln!();
                indent();
                eprint!("): ");
                types.dump_type(compiler, resulting_ty);
            }
            &Node::Match {
                value,
                branch_index,
                pattern_index,
                branch_count,
                resulting_ty,
            } => {
                eprint!("(match ");
                self.dump(value, compiler, types, indent_count);
                for i in 0..branch_count {
                    eprintln!();
                    indent_n(indent_count + 1);
                    let pattern = PatternId(pattern_index + i);
                    let branch = NodeId(branch_index + i);
                    self.dump_pattern(pattern, compiler, types);
                    eprint!(" ");
                    self.dump(branch, compiler, types, indent_count + 1);
                }
                eprintln!();
                indent();
                eprint!("): ");
                types.dump_type(compiler, resulting_ty);
            }
            &Node::While { cond, body } => {
                eprint!("(while ");
                self.dump(cond, compiler, types, indent_count);
                eprint!(" ");
                self.dump(body, compiler, types, indent_count);
                eprint!(")");
            }
            &Node::WhilePat { pat, val, body } => {
                eprint!("(while ");
                self.dump_pattern(pat, compiler, types);
                eprint!(" ");
                self.dump(val, compiler, types, indent_count);
                eprint!(" ");
                self.dump(body, compiler, types, indent_count);
                eprint!(")");
            }
            &Node::Call {
                function,
                generics,
                args,
                return_ty,
                noreturn: _,
            } => {
                let name = compiler.get_function_name(function.0, function.1);
                eprint!("(call {name} (");
                for (i, generic) in generics.iter().enumerate() {
                    if i != 0 {
                        eprint!(" ");
                    }
                    types.dump_type(compiler, generic);
                }
                eprint!(")");
                for arg in args.iter() {
                    eprint!(" ");
                    self.dump(arg, compiler, types, indent_count);
                }
                eprint!("): ");
                types.dump_type(compiler, return_ty);
            }
            &Node::TraitCall {
                trait_id,
                trait_generics,
                method_index,
                self_ty,
                args,
                return_ty,
                noreturn: _,
            } => {
                eprint!(
                    "(call-trait-method <trait {}:{}",
                    trait_id.0 .0, trait_id.1 .0
                );
                if trait_generics.count > 0 {
                    eprint!("[");
                    for generic in trait_generics.iter() {
                        types.dump_type(compiler, generic);
                    }
                    eprint!("]");
                }
                eprint!(" as ");
                types.dump_type(compiler, self_ty);
                eprint!(">.{method_index}");
                for arg in args.iter() {
                    eprint!(" ");
                    self.dump(arg, compiler, types, indent_count);
                }
                eprint!("): ");
                types.dump_type(compiler, return_ty);
            }
            &Node::TypeProperty(ty, property) => {
                let prop = match property {
                    TypeProperty::Size => "size",
                    TypeProperty::Align => "align",
                    TypeProperty::Stride => "stride",
                };
                eprint!("(type_prop {prop} ");
                types.dump_type(compiler, ty);
                eprint!(")");
            }
        }
    }

    fn dump_pattern(&self, pattern: PatternId, compiler: &Compiler, types: &TypeTable) {
        match &self[pattern] {
            Pattern::Invalid => eprint!("<invalid>"),
            Pattern::Variable(id) => {
                eprint!("(var {}): ", id.0);
                let var_ty = self.vars[id.idx()];
                types.dump_type(compiler, var_ty);
            }
            Pattern::Ignore => eprint!("_"),
            &Pattern::Tuple {
                member_count,
                patterns,
                types: type_ids,
            } => {
                eprint!("(");
                let pats = PatternIds {
                    index: patterns,
                    count: member_count,
                };
                let type_ids = LocalTypeIds {
                    idx: type_ids,
                    count: member_count,
                };
                for (i, pat) in pats.iter().enumerate() {
                    if i != 0 {
                        eprint!(" ");
                    }
                    self.dump_pattern(pat, compiler, types);
                }
                eprint!("): (");
                for (i, ty) in type_ids.iter().enumerate() {
                    if i != 0 {
                        eprint!(" ");
                    }
                    types.dump_type(compiler, ty);
                }
                eprint!(")");
            }
            &Pattern::Int(signed, unsigned_val, ty) => {
                eprint!("(int ");
                if signed {
                    eprint!("-");
                }
                eprint!("{unsigned_val}): ");
                types.dump_type(compiler, ty);
            }
            Pattern::Bool(b) => eprint!("{b}"),
            Pattern::String(s) => eprint!("(string {s:?})"),
            &Pattern::Range {
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
            &Pattern::EnumVariant {
                ordinal,
                types: enum_types,
                args,
            } => {
                eprint!("(enum-variant {ordinal:?}: ");
                types.dump_type(compiler, LocalTypeId(enum_types));
                for (arg, ty) in args.iter().zip(
                    LocalTypeIds {
                        idx: enum_types + 1,
                        count: args.count,
                    }
                    .iter(),
                ) {
                    eprint!(" ");
                    self.dump_pattern(arg, compiler, types);
                    eprint!(": ");
                    types.dump_type(compiler, ty);
                }
                eprint!(")");
            }
        }
    }

    fn dump_lvalue(
        &self,
        lval: LValueId,
        compiler: &Compiler,
        types: &TypeTable,
        indent_count: usize,
    ) {
        match self[lval] {
            LValue::Invalid => eprint!("(invalid)"),
            LValue::Variable(id) => eprint!("(var {})", id.0),
            LValue::Global(module, id) => eprint!("(global {} {})", module.0, id.0),
            LValue::Deref(val) => {
                eprint!("(deref ");
                self.dump(val, compiler, types, indent_count);
                eprint!(")");
            }
            LValue::Member {
                tuple,
                index,
                elem_types,
            } => {
                eprint!("(member {index} ");
                self.dump_lvalue(tuple, compiler, types, indent_count);
                eprint!(": (");
                for (i, elem) in elem_types.iter().enumerate() {
                    if i != 0 {
                        eprint!(", ");
                    }
                    types.dump_type(compiler, elem);
                }
                eprint!("))");
            }
            LValue::ArrayIndex {
                array,
                index,
                elem_ty: element_type,
            } => {
                eprint!("(index ");
                self.dump_lvalue(array, compiler, types, indent_count);
                eprint!(" ");
                self.dump(index, compiler, types, indent_count);
                eprint!("): ");
                types.dump_type(compiler, element_type);
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

    pub fn skip(self, i: u32) -> NodeIds {
        Self {
            index: self.index + i,
            count: self.count - i,
        }
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
    pub index: u32,
    pub count: u32,
}
impl PatternIds {
    pub fn iter(self) -> impl Iterator<Item = PatternId> {
        (self.index..self.index + self.count).map(PatternId)
    }
}

#[derive(Debug, Clone)]
pub enum Node {
    Invalid,
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
    StringLiteral(Box<str>),
    EnumLiteral {
        // PERF(size): length has to match anyways, could only store it once
        elems: NodeIds,
        elem_types: LocalTypeIds,
        enum_ty: LocalTypeId,
    },
    InferredEnumOrdinal(VariantId),

    Declare {
        pattern: PatternId,
    },
    DeclareWithVal {
        pattern: PatternId,
        val: NodeId,
    },
    Variable(VarId),
    Global(ModuleId, GlobalId, LocalTypeId),
    Assign(LValueId, NodeId, AssignType, LocalTypeId),

    Const {
        id: ConstValueId,
        ty: LocalTypeId,
    },

    Negate(NodeId, LocalTypeId),
    Not(NodeId),
    AddressOf {
        value: LValueId,
        value_ty: LocalTypeId,
    },
    Deref {
        value: NodeId,
        deref_ty: LocalTypeId,
    },
    Promote {
        value: NodeId,
        variable: VarId,
    },

    Cast(CastId),
    Comparison {
        l: NodeId,
        r: NodeId,
        cmp: Comparison,
        compared: LocalTypeId,
    },
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
    IfPatElse {
        pat: PatternId,
        val: NodeId,
        then: NodeId,
        else_: NodeId,
        resulting_ty: LocalTypeId,
    },
    Match {
        value: NodeId,
        branch_index: u32,
        pattern_index: u32,
        branch_count: u32,
        resulting_ty: LocalTypeId,
    },
    While {
        cond: NodeId,
        body: NodeId,
    },
    WhilePat {
        pat: PatternId,
        val: NodeId,
        body: NodeId,
    },
    Call {
        function: (ModuleId, FunctionId),
        generics: LocalTypeIds,
        args: NodeIds,
        return_ty: LocalTypeId,
        noreturn: bool,
    },
    TraitCall {
        trait_id: (ModuleId, TraitId),
        trait_generics: LocalTypeIds,
        method_index: u16,
        self_ty: LocalTypeId,
        args: NodeIds,
        return_ty: LocalTypeId,
        noreturn: bool,
    },
    TypeProperty(LocalTypeId, TypeProperty),
}

#[derive(Debug, Clone)]
pub enum LValue {
    Invalid,
    Variable(VarId),
    Global(ModuleId, GlobalId),
    Deref(NodeId),
    Member {
        tuple: LValueId,
        index: u32,
        elem_types: LocalTypeIds,
    },
    ArrayIndex {
        array: LValueId,
        index: NodeId,
        elem_ty: LocalTypeId,
    },
}
impl LValue {
    pub fn try_from_node(node: &Node, hir: &mut HIRBuilder) -> Option<Self> {
        Some(match *node {
            Node::Invalid => Self::Invalid,
            Node::Variable(id) => Self::Variable(id),
            Node::Global(module, id, _) => Self::Global(module, id),
            Node::Deref { value, deref_ty: _ } => Self::Deref(value),
            Node::Element {
                tuple_value,
                index,
                elem_types,
            } => {
                let tuple = Self::try_from_node(&hir[tuple_value].clone(), hir)?;
                Self::Member {
                    tuple: hir.add_lvalue(tuple),
                    index,
                    elem_types,
                }
            }
            Node::ArrayIndex {
                array,
                index,
                elem_ty,
            } => {
                let array = Self::try_from_node(&hir[array].clone(), hir)?;
                Self::ArrayIndex {
                    array: hir.add_lvalue(array),
                    index,
                    elem_ty,
                }
            }
            _ => return None,
        })
    }
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Invalid,
    Variable(VarId),
    Ignore,
    Tuple {
        member_count: u32,
        /// member_count Patterns start index
        patterns: u32,
        /// member_count LocalTypeIds start index
        types: u32,
    },
    Int(bool, u128, LocalTypeId),
    Bool(bool),
    String(Box<str>),
    Range {
        min_max: (u128, u128),
        ty: LocalTypeId,
        min_max_signs: (bool, bool),
        inclusive: bool,
    },
    EnumVariant {
        ordinal: OrdinalType,
        /// always one more than args because it contains the ordinal type first
        types: u32,
        args: PatternIds,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
impl Index<NodeId> for HIRBuilder {
    type Output = Node;
    fn index(&self, index: NodeId) -> &Self::Output {
        &self.nodes[index.0 as usize]
    }
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

    pub fn finish(
        mut self,
        root: Node,
        compiler: &mut Compiler,
        generics: &Generics,
        module: ModuleId,
    ) -> (HIR, TypeTable) {
        self.nodes.push(root);
        self.types.finish(compiler, generics, module);
        (
            HIR {
                nodes: self.nodes,
                lvalues: self.lvalues,
                patterns: self.patterns,
                vars: self.vars,
                casts: self.casts,
                trait_calls: Vec::new(),
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

    pub fn modify_pattern(&mut self, pattern_id: PatternId, pattern: Pattern) {
        self.patterns[pattern_id.0 as usize] = pattern;
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

    pub fn add_invalid_patterns(&mut self, count: u32) -> PatternIds {
        self.add_patterns((0..count).map(|_| Pattern::Invalid))
    }

    pub fn add_cast(&mut self, cast: Cast) -> CastId {
        let id = CastId(self.casts.len() as _);
        self.casts.push(cast);
        id
    }
}
