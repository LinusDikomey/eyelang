use std::borrow::Borrow;
use crate::{types::*, lexer::tokens::AssignType};

use super::*;


/// Represent ast nodes as the original code 
pub trait Repr<C: Representer> {
    fn repr(&self, c: &C);
}

/*enum ReprWriter<'a, W: std::fmt::Write> {
    Writer(&'a mut W),
    Parent(&'a mut ReprCtx<'a, W>)
}*/


pub trait Representer {
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
    count: u32
}
impl<'a> ReprPrinter<'a> {
    pub fn new(indent: &'a str) -> Self {
        Self { indent, count: 0 }
    }
}

impl Representer for ReprPrinter<'_> {
    fn child(&self) -> Self {
        Self {
            indent: self.indent,
            count: self.count + 1
        }
    }

    fn begin_line(&self) {
        print!("{}", self.indent.repeat(self.count as usize));
    }

    fn write_start<B: Borrow<str>>(&self, s: B) {
        print!("{}{}", self.indent.repeat(self.count as usize), s.borrow());
    }

    fn write_add<B: Borrow<str>>(&self, s: B) {
        print!("{}", s.borrow())
    }
    fn char(&self, c: char) {
        print!("{c}")
    }

    fn writeln<B: Borrow<str>>(&self, s: B) {
        println!("{}{}", self.indent.repeat(self.count as usize), s.borrow());
    }
}


impl<C: Representer> Repr<C> for Module {
    fn repr(&self, c: &C) {
        for (name, def) in &self.definitions {
            def.repr(c, name);
            c.writeln("");
        }
    }
}

impl Definition {
    fn repr<C: Representer>(&self, c: &C, name: &str) {
        match self {
            Self::Function(func) => func.repr(c, name),
            Self::Struct(struc) => struc.repr(c, name),
            Self::Module(_) => {}
        }
    }
}

impl Function {
    fn repr<C: Representer>(&self, c: &C, name: &str) {
        c.write_add(name);
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
        self.return_type.0.repr(c);
        match &self.body {
            Some(body@BlockOrExpr::Expr(_)) => {
                c.write_add(": ");
                body.repr(c);
            }
            Some(body) => {
                c.space();
                body.repr(c);
            }
            None => c.write_add(" extern")
        }
        c.writeln("");
    }
}

impl StructDefinition {
    fn repr<C: Representer>(&self, c: &C, name: &str) {
        c.writeln(format!("{} :: {{", name));
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

impl<C: Representer> Repr<C> for Block {
    fn repr(&self, c: &C) {
        c.write_add("{\n");
        let child = c.child();
        for (name, def) in &self.defs {
            def.repr(&child, name);
        }
        for item in &self.items {
            item.repr(&child);
        }
        c.write_start("}");
    }
}

impl<C: Representer> Repr<C> for BlockItem {
    fn repr(&self, c: &C) {
        match self {
            Self::Block(block) => block.repr(c),
            Self::Declare(name, _idx, ty, expr) => {
                c.write_start(name.as_str());
                if let Some(ty) = ty {
                    c.write_add(": ");
                    ty.repr(c);
                    if expr.is_some() {
                        c.space();
                    }
                } else {
                    debug_assert!(expr.is_some());
                    c.write_add(" :");
                }
                if let Some(expr) = expr {
                    c.write_add("= ");
                    expr.repr(c);
                }
            }
            Self::Expression(expr) => {
                c.begin_line();
                expr.repr(c);
            }
        }
        c.write_add("\n");
    }
}

impl<C: Representer> Repr<C> for Expression {
    fn repr(&self, c: &C) {
        match self {
            Self::Return(val) => {
                c.write_add("ret");
                c.space();
                val.repr(c);
            }
            Self::IntLiteral(lit) => c.write_add(format!("{lit}")),
            Self::FloatLiteral(lit) => c.write_add(format!("{lit}")),
            Self::StringLiteral(s) => {
                c.write_add("\"");
                c.write_add(s.as_str().replace('\n', "\\n"));
                c.write_add("\"");
            }
            Self::BoolLiteral(b) => c.write_add(if *b { "true" } else { "false" }),
            Self::Unit => c.write_add("()"),
            Self::Variable(name) => c.write_add(name.as_str()),
            Self::If(box If { cond, then, else_ }) => {
                c.write_add("if ");
                cond.repr(c);
                if let BlockOrExpr::Block(_) = then {
                    c.space();
                } else {
                    c.write_add(": ");
                }
                then.repr(c);
                if let Some(else_block) = else_ {
                    c.write_add(" else ");
                    else_block.repr(c);
                }
            }
            Self::While(box While { cond, body }) => {
                c.write_add("while ");
                cond.repr(c);
                if let BlockOrExpr::Block(_) = body {
                    c.space();
                } else {
                    c.write_add(": ");
                }
                body.repr(c);
            }
            Self::FunctionCall(func, args) => {
                func.repr(c);
                c.write_add("(");
                for (i, arg) in args.iter().enumerate() {
                    arg.repr(c);
                    if i != (args.len() - 1) {
                        c.write_add(", ");
                    }
                }
                c.write_add(")");
            }
            Self::UnOp(un_op, expr) => {
                c.char(match un_op {
                    UnOp::Neg => '-',
                    UnOp::Not => '!',
                });
                expr.repr(c);
            }
            Self::BinOp(op, exprs) => {
                c.write_add("(");
                let (l, r) = &**exprs;
                l.repr(c);
                c.space();
                op.repr(c);
                c.space();
                r.repr(c);
                c.write_add(")");
            }
            Self::MemberAccess(expr, member) => {
                expr.repr(c);
                c.write_add(".");
                c.write_add(member.as_str());
            }
            Self::Cast(ty, expr) => {
                ty.repr(c);
                c.space();
                expr.repr(c);
            },
            Self::Root => c.write_add("root")
        }
    }
}

impl<R: Representer> Repr<R> for IdentPath {
    fn repr(&self, c: &R) {
        let (has_root, iter, last) = self.segments();
        if has_root {
            c.write_add("root");
        }
        let mut has_segments = false;
        for (i, name) in iter.enumerate() {
            has_segments = true;
            if i != 0 || has_root {
                c.write_add(".");
            }
            c.write_add(name.as_str());
        }
        if let Some(last) = last {
            if has_root || has_segments {
                c.write_add(".");
            }
            c.write_add(last.as_str());
        }
    }
}

impl<R: Representer> Repr<R> for UnresolvedType {
    fn repr(&self, c: &R) {
        match self {
            Self::Primitive(p) => p.repr(c),
            Self::Unresolved(path) => path.repr(c)
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
            Self::String => c.write_add("string"),
            Self::Bool => c.write_add("bool"),
            Self::Unit => c.write_add("()"),
            Self::Never => c.write_add("!")
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
        })
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
        })
    }
}