use std::borrow::Borrow;
use crate::{types::*, lexer::tokens::AssignType};

use super::*;


/// Represent ast nodes as the original code 
pub trait Repr<C: Representer> {
    fn repr(&self, c: &C);
}

pub trait Representer {
    fn src(&self, span: TSpan) -> &str;
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
        for (name, def) in &self.definitions {
            def.repr(c, name);
            c.writeln("\n");
        }
    }
}

impl Definition {
    fn repr<C: Representer>(&self, c: &C, name: &str) {
        match self {
            Self::Function(func) => func.repr(c, name),
            Self::Struct(struc) => struc.repr(c, name),
            Self::Module(_) => {}
            Self::Use(path) => {
                c.write_add("use ");
                path.repr(c);
            }
        }
    }
}

impl Function {
    fn repr<C: Representer>(&self, c: &C, name: &str) {
        c.write_start("fn ");
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
        c.space();
        self.return_type.0.repr(c);
        match &self.body.map(|body| &c.ast()[body]) {
            Some(block@Expr::Block { .. }) => {
                c.space();
                block.repr(c);
            }
            Some(expr) => {
                c.write_add(": ");
                expr.repr(c);
            }
            None => c.write_add(" extern")
        }
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

impl<C: Representer> Repr<C> for Expr {
    fn repr(&self, c: &C) {
        let ast = c.ast();
        match &self {
            Self::Block { span: _, items, defs } => {
                c.write_add("{\n");
                let child = c.child();
                for (name, def) in defs {
                    def.repr(&child, name);
                }
                for item in items {
                    child.write_start("");
                    ast[*item].repr(&child);
                    child.writeln("");
                }
                c.write_start("}");
            },
            Self::Declare { name, end: _, annotated_ty, val } => {
                c.write_add(c.src(*name));
                if !matches!(annotated_ty, UnresolvedType::Infer(_)) {
                    c.write_add(": ");
                    annotated_ty.repr(c);
                    if val.is_some() {
                        c.write_add(" = ");
                    }
                } else {
                    c.write_add(" := ");
                }
                val.map(|v| ast[v].repr(c));
            }
            Self::Return { start: _, val } => {
                c.write_add("ret");
                c.space();
                ast[*val].repr(c);
            }
            Self::IntLiteral(span) => c.write_add(c.src(*span)),
            Self::FloatLiteral(span) => c.write_add(c.src(*span)),
            Self::StringLiteral(span) => {
                //c.write_add("\"");
                c.write_add(c.src(*span));
                //c.write_add("\"");
            }
            Self::BoolLiteral { start: _, val } => c.write_add(if *val { "true" } else { "false" }),
            Self::Nested(_, inner) => {
                c.char('(');
                ast[*inner].repr(c);
                c.char(')');
            }
            Self::Unit(_) => c.write_add("()"),
            Self::Variable(span) => c.write_add(c.src(*span)),
            Self::If { span: _, cond, then, else_ } => {
                c.write_add("if ");
                ast[*cond].repr(c);
                let then = &ast[*then];
                match then {
                    Expr::Block { .. } => c.space(),
                    _ => c.write_add(": ")
                }
                then.repr(c);
                if let Some(else_block) = else_ {
                    c.write_add(" else ");
                    ast[*else_block].repr(c);
                }
            }
            Self::While(box While { span: _, cond, body }) => {
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
            Self::MemberAccess(expr, member) => {
                ast[*expr].repr(c);
                c.write_add(".");
                c.write_add(c.src(*member));
            }
            Self::Cast(_, ty, expr) => {
                ty.repr(c);
                c.space();
                ast[*expr].repr(c);
            },
            Self::Root(_) => c.write_add("root")
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
        for (i, segment) in iter.enumerate() {
            has_segments = true;
            if i != 0 || has_root {
                c.write_add(".");
            }
            let name = c.src(*segment);
            c.write_add(name);
        }
        if let Some(last) = last {
            if has_root || has_segments {
                c.write_add(".");
            }
            c.write_add(c.src(last));
        }
    }
}

impl<R: Representer> Repr<R> for UnresolvedType {
    fn repr(&self, c: &R) {
        match self {
            Self::Primitive(p, _) => p.repr(c),
            Self::Unresolved(path) => path.repr(c),
            Self::Pointer(inner, _) => {
                c.char('*');
                inner.repr(c);
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