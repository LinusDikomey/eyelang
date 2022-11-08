use std::borrow::Borrow;
use crate::{types::*, token::AssignType};

use super::*;


/// Represent ast nodes as the original code 
pub trait Repr<C: Representer> {
    fn repr(&self, c: &C);
}

pub trait Representer {
    fn src(&self, span: TSpan) -> &str;
    fn whole_src(&self) -> &str;
    fn ast(&self) -> &Ast;
    fn child(&self) -> Self;
    fn begin_line(&self);
    fn write_start<B: Borrow<str>>(&self, s: B);
    fn write_add<B: Borrow<str>>(&self, s: B);
    fn char(&self, c: char);
    fn space(&self) {
        self.char(' ');
    }
    fn writeln<B: Borrow<str>>(&self, s: B);
}

pub struct ReprPrinter<'a> {
    indent: &'a str,
    count: u32,
    ast: &'a Ast,
    src: &'a str,
}
impl<'a> ReprPrinter<'a> {
    pub fn new(indent: &'a str, ast: &'a Ast, src: &'a str) -> Self {
        Self { indent, count: 0, ast, src }
    }
}

impl Representer for ReprPrinter<'_> {
    fn src(&self, span: TSpan) -> &str {
        &self.src[span.range()]
    }
    fn whole_src(&self) -> &str {
        self.src
    }
    fn ast(&self) -> &Ast { self.ast }
    fn child(&self) -> Self {
        Self {
            indent: self.indent,
            count: self.count + 1,
            ast: self.ast,
            src: self.src
        }
    }

    fn begin_line(&self) {
        print!("{}", self.indent.repeat(self.count as usize));
    }

    fn write_start<B: Borrow<str>>(&self, s: B) {
        print!("{}{}", self.indent.repeat(self.count as usize), s.borrow());
    }

    fn write_add<B: Borrow<str>>(&self, s: B) {
        print!("{}", s.borrow());
    }
    fn char(&self, c: char) {
        print!("{c}");
    }

    fn writeln<B: Borrow<str>>(&self, s: B) {
        println!("{}{}", self.indent.repeat(self.count as usize), s.borrow());
    }
}


impl<C: Representer> Repr<C> for Module {
    fn repr(&self, c: &C) {
        for (name, def) in &c.ast()[self.definitions] {
            def.repr(c, name);
            c.writeln("\n");
        }
    }
}

impl Definition {
    fn repr<C: Representer>(&self, c: &C, name: &str) {
        c.write_start(name);
        if !matches!(self, Self::Global(_, _) | Self::Const(_, _)) {
            c.write_add(" :: ");
        }
        match self {
            Self::Function(func) => func.repr(c, false),
            Self::Struct(struct_) => struct_.repr(c),
            Self::Enum(def) => def.repr(c),
            Self::Trait(t) => t.repr(c),
            Self::Module(_) => {}
            Self::Use(path) => {
                c.write_add("use ");
                path.repr(c);
            }
            Self::Const(ty, expr) => {
                c.write_add(name);
                if let UnresolvedType::Infer(_) = ty {
                    c.write_add(" :: ");
                }  else {
                    c.write_add(": ");
                    ty.repr(c);
                    c.write_add(" : ");
                }
                c.ast()[*expr].repr(c);
            }
            Self::Global(ty, val) => {
                c.write_add(name);
                c.write_add(": ");
                ty.repr(c);
                if let &Some(val) = val {
                    c.write_add(" = ");
                    c.ast()[val].repr(c);
                }
            }
        }
    }
}

impl Function {
    fn repr<C: Representer>(&self, c: &C, in_trait: bool) {
        c.write_add("fn");
        if !self.params.is_empty() {
            c.write_add("(");
            for (i, (name, param, _, _)) in self.params.iter().enumerate() {
                c.write_add(name.as_str());
                c.space();
                param.repr(c);
                if i != self.params.len() - 1 {
                    c.write_add(", ");
                }
            }
            c.write_add(")");
        }
        c.write_add(" -> ");
        self.return_type.repr(c);
        match &self.body.map(|body| &c.ast()[body]) {
            Some(block@Expr::Block { .. }) => {
                c.space();
                block.repr(c);
            }
            Some(expr) => {
                c.write_add(": ");
                expr.repr(c);
            }
            None => if !in_trait { c.write_add(" extern") }
        }
    }
}

impl StructDefinition {
    fn repr<C: Representer>(&self, c: &C) {
        c.write_add("struct {\n");
        let child = c.child();
        for (i, (name, ty, _, _)) in self.members.iter().enumerate() {
            child.begin_line();
            child.write_add(name.as_str());
            child.space();
            ty.repr(&child);
            child.write_add(if i == (self.members.len() - 1) { "\n" } else { ",\n" });
        }
        c.write_start("}");
    }
}

impl EnumDefinition {
    fn repr<C: Representer>(&self, c: &C) {
        c.write_add("enum {\n");
        let child = c.child();
        for (_, name) in &self.variants {
            child.begin_line();
            child.write_add(name.as_str());
        }
        c.write_start("}");
    }
}


impl TraitDefinition {
    fn repr<C: Representer>(&self, c: &C) {
        c.write_add("trait {\n");
        let child = c.child();
        for (name, (_, func)) in &self.functions {
            c.write_start(name.as_str());
            c.write_add(" :: ");
            func.repr(&child, true);
        }
        c.write_start("}");
    }
}

impl<C: Representer> Repr<C> for Expr {
    fn repr(&self, c: &C) {
        let ast = c.ast();
        match &self {
            Self::Block { span: _, items, defs } => {
                c.write_add("{\n");
                let child = c.child();
                for (name, def) in &ast[*defs] {
                    def.repr(&child, name);
                }
                for item in &ast[*items] {
                    child.write_start("");
                    ast[*item].repr(&child);
                    child.writeln("");
                }
                c.write_start("}");
            },
            Self::Declare { pat, annotated_ty } => {
                ast[*pat].repr(c);

                c.write_add(": ");
                annotated_ty.repr(c);
            }
            Self::DeclareWithVal { pat, annotated_ty, val } => {
                ast[*pat].repr(c);
                
                if matches!(annotated_ty, UnresolvedType::Infer(_)) {
                    c.write_add(" := ");
                } else {
                    c.write_add(": ");
                    annotated_ty.repr(c);
                    c.write_add(" = ");
                }
                ast[*val].repr(c);
            }
            Self::Return { start: _, val } => {
                c.write_add("ret");
                c.space();
                ast[*val].repr(c);
            }
            Self::IntLiteral(span) | Self::FloatLiteral(span) | Self::StringLiteral(span) 
                => c.write_add(c.src(*span)),
            Self::BoolLiteral { start: _, val } => c.write_add(if *val { "true" } else { "false" }),
            Self::EnumLiteral { dot: _, ident } => {
                c.char('.');
                c.write_add(c.src(*ident));
            }
            Self::Record { span: _, names, values } => {
                c.write_add(".{ ");
                for (i, name) in names.iter().enumerate() {
                    if i != 0 {
                        c.write_add(", ");
                    }
                    c.write_add(c.src(*name));
                    c.space();
                    let value = ast.extra[*values as usize + i];
                    ast[value].repr(c);
                }
                c.write_add(" }")
            }
            Self::Nested(_, inner) => {
                c.char('(');
                ast[*inner].repr(c);
                c.char(')');
            }
            Self::Unit(_) => c.write_add("()"),
            Self::Variable(span) => c.write_add(c.src(*span)),
            Self::Hole(_) => c.char('_'),
            Self::Array(_, elems) => {
                let elems = &ast[*elems];
                c.char('[');
                let mut elems = elems.iter().copied();
                if let Some(first) = elems.next() {
                    ast[first].repr(c);
                }
                for elem in elems {
                    c.write_add(", ");
                    ast[elem].repr(c);
                }
                c.char(']');
            }
            Self::Tuple(_, elems) => {
                let elems = &ast[*elems];
                c.char('(');
                let mut it = elems.iter().copied();
                if let Some(f) = it.next() { ast[f].repr(c) };
                for elem in it {
                    c.write_add(", ");
                    ast[elem].repr(c);
                }
                if elems.len() == 1 {
                    c.char(',');
                }
                c.char(')');
            }
            Self::If { start: _, cond, then } => {
                c.write_add("if ");
                ast[*cond].repr(c);
                let then = &ast[*then];
                match then {
                    Expr::Block { .. } => c.space(),
                    _ => c.write_add(": ")
                }
                then.repr(c);
            }
            Self::IfElse { start: _, cond, then, else_ } => {
                c.write_add("if ");
                ast[*cond].repr(c);
                let then = &ast[*then];
                match then {
                    Expr::Block { .. } => c.space(),
                    _ => c.write_add(": ")
                }
                then.repr(c);
                c.write_add(" else ");
                ast[*else_].repr(c);
            }
            Self::Match { start: _, end: _, val, extra_branches, branch_count } => {
                c.write_add("match ");
                ast[*val].repr(c);
                c.write_add(" {\n");
                let extra = ExprExtra { idx: *extra_branches, count: *branch_count * 2 };
                let match_c = c.child();
                for [pat, branch] in ast[extra].array_chunks() {
                    c.begin_line();
                    ast[*pat].repr(&match_c);
                    let branch = &ast[*branch];
                    if !matches!(branch, Expr::Block { .. }) {
                        match_c.write_add(": ");
                    }
                    branch.repr(&match_c);
                    match_c.char('\n');
                }
                c.writeln("}");
            }
            Self::While { start: _, cond, body } => {
                c.write_add("while ");
                ast[*cond].repr(c);
                let body = &ast[*body];
                if body.is_block() {
                    c.space();
                } else {
                    c.write_add(": ");
                }
                body.repr(c);
            }
            Self::FunctionCall { func, args, end: _ } => {
                let args = &ast[*args];
                let func = &ast[*func];
                func.repr(c);
                c.write_add("(");
                for (i, arg) in args.iter().enumerate() {
                    ast[*arg].repr(c);
                    if i != (args.len() - 1) {
                        c.write_add(", ");
                    }
                }
                c.write_add(")");
            }
            Self::UnOp(_, un_op, expr) => {
                let expr = &ast[*expr];
                c.char(match un_op {
                    UnOp::Neg => '-',
                    UnOp::Not => '!',
                    UnOp::Ref => '&',
                    UnOp::Deref => {
                        expr.repr(c);
                        c.char('^');
                        return;
                    }
                });
                expr.repr(c);
            }
            Self::BinOp(op, l, r) => {
                c.write_add("(");
                ast[*l].repr(c);
                c.space();
                op.repr(c);
                c.space();
                ast[*r].repr(c);
                c.write_add(")");
            }
            Self::MemberAccess { left, name } => {
                ast[*left].repr(c);
                c.char('.');
                c.write_add(c.src(*name));
            }
            Self::Index { expr, .. } => {
                c.char('[');
                ast[*expr].repr(c);
                c.char(']');
            }
            Self::TupleIdx { expr, idx, end: _ } => {
                ast[*expr].repr(c);
                c.char('.');
                c.write_add(idx.to_string());
            }
            Self::Cast(_, ty, expr) => {
                ast[*expr].repr(c);
                c.write_add(" as ");
                ty.repr(c);
            },
            Self::Root(_) => c.write_add("root"),
            Self::Asm { span: _, asm_str_span, args } => {
                c.write_add("asm(");
                c.write_add(c.src(*asm_str_span));
                for arg in &ast[*args] {
                    c.write_add(", ");
                    ast[*arg].repr(c);
                }
                c.char(')');
            }
        }
    }
}

impl<R: Representer> Repr<R> for IdentPath {
    fn repr(&self, c: &R) {
        let (root, iter, last) = self.segments(c.whole_src());
        let has_root = root.is_some();
        if has_root {
            c.write_add("root");
        }
        let mut has_segments = false;
        for (i, segment) in iter.enumerate() {
            has_segments = true;
            if i != 0 || has_root {
                c.write_add(".");
            }
            c.write_add(segment.0);
        }
        if let Some(last) = last {
            if has_root || has_segments {
                c.write_add(".");
            }
            c.write_add(last.0);
        }
    }
}

impl<R: Representer> Repr<R> for UnresolvedType {
    fn repr(&self, c: &R) {
        match self {
            Self::Primitive(p, _) => p.repr(c),
            Self::Unresolved(path, generics) => {
                path.repr(c);
                if let Some((generics, _)) = generics {
                    c.write_add("[");
                    for (i, ty) in generics.iter().enumerate() {
                        if i != 0 {
                            c.write_add(", ");
                        }
                        ty.repr(c);
                    }
                    c.write_add("]");
                }
            }
            Self::Pointer(ptr) => {
                let (inner, _) = &**ptr;
                c.char('*');
                inner.repr(c);
            }
            Self::Array(array) => {
                let (inner, _, size) = &**array;
                c.char('[');
                inner.repr(c);
                c.write_add("; ");
                if let Some(size) = size {
                    c.write_add(size.to_string());
                } else {
                    c.char('_');
                }
                c.char(']');
            }
            Self::Tuple(elems, _) => {
                c.char('(');
                let mut elems = elems.iter();
                if let Some(e) = elems.next() { e.repr(c) }
                for elem in elems {
                    c.write_add(", ");
                    elem.repr(c);
                }
                c.char(')');
            }
            Self::Infer(_) => c.char('_')
        }
    }
}

impl<C: Representer> Repr<C> for Primitive {
    fn repr(&self, c: &C) {
        match self { 
            Self::I8 | Self::U8
            | Self::I16 | Self::U16
            | Self::I32 | Self::U32
            | Self::I64 | Self::U64
            | Self::I128 | Self::U128
                => self.as_int().unwrap().repr(c),
            Self::F32 | Self::F64 => self.as_float().unwrap().repr(c),
            Self::Bool => c.write_add("bool"),
            Self::Unit => c.write_add("()"),
            Self::Never => c.write_add("!"),
            Self::Type => c.write_add("type"),
        }
    }
}

impl<C: Representer> Repr<C> for IntType {
    fn repr(&self, c: &C) {
        use IntType::*;
        c.write_add(match self {
            I8 => "i8",
            I16 => "i16",
            I32 => "i32",
            I64 => "i64",
            I128 => "i128",
            U8 => "u8",
            U16 => "u16",
            U32 => "u32",
            U64 => "u64",
            U128 => "u128",
        });
    }
}

impl<C: Representer> Repr<C> for FloatType {
    fn repr(&self, c: &C) {
        c.write_add(match self {
            Self::F32 => "f32",
            Self::F64 => "f64"
        });
    }
}

impl<C: Representer> Repr<C> for Operator {
    fn repr(&self, c: &C) {
        c.write_add(match self {
            Operator::Add => "+",
            Operator::Sub => "-",
            Operator::Mul => "*",
            Operator::Div => "/",
            Operator::Mod => "%",

            Operator::Assignment(assignment) => return assignment.repr(c),
            
            Operator::Equals => "==",
            Operator::NotEquals => "!=",
            
            Operator::Or => "or",
            Operator::And => "and",

            Operator::LT => "<",
            Operator::GT => ">",
            Operator::LE => "<=",
            Operator::GE => ">=",

            Operator::Range => "..",
            Operator::RangeExclusive => "..<",
        });
    }
}

impl<C: Representer> Repr<C> for AssignType {
    fn repr(&self, c: &C) {
        c.write_add(match self {
            AssignType::Assign => "=",
            AssignType::AddAssign => "+=",
            AssignType::SubAssign => "-=",
            AssignType::MulAssign => "*=",
            AssignType::DivAssign => "/=",
            AssignType::ModAssign => "%=",
        });
    }
}