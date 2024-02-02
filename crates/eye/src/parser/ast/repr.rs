use std::borrow::Borrow;
use types::{IntType, FloatType};

use crate::parser::token::AssignType;

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
}
impl<'a> ReprPrinter<'a> {
    pub fn new(indent: &'a str, ast: &'a Ast) -> Self {
        Self { indent, count: 0, ast }
    }

    pub fn print_module(&self) {
        for (name, item) in &self.ast.top_level_scope().definitions {
            item.repr(self, name);
            println!("\n");
        }
    }

    pub fn src_at(&self, span: TSpan) -> &str {
        &self.ast.src()[span.range()]
    }
}

impl Representer for ReprPrinter<'_> {
    fn src(&self, span: TSpan) -> &str {
        self.src_at(span)
    }
    fn whole_src(&self) -> &str {
        self.ast.src()
    }
    fn ast(&self) -> &Ast { self.ast }
    fn child(&self) -> Self {
        Self {
            indent: self.indent,
            count: self.count + 1,
            ast: self.ast,
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

impl Definition {
    fn repr<C: Representer>(&self, c: &C, name: &str) {
        if !matches!(self, Self::Path(_)) {
            c.write_start(name);
        }
        match self {
            Self::Path(path) => {
                c.write_start("use ");
                path.repr(c);
                
                c.write_add(" as ");
                c.write_add(name);
            }
            Self::Expr { value, ty } => {
                if let UnresolvedType::Infer(_) = ty {
                    c.write_add(" :: ");
                } else {
                    c.write_add(": ");
                    ty.repr(c);
                    c.write_add(" : ");
                }
                c.ast()[*value].repr(c);
            }
            Self::Global(id) => {
                let global = &c.ast()[*id];

                c.write_add(name);
                c.write_add(": ");
                global.ty.repr(c);
                if let Some(val) = global.val {
                    c.write_add(" = ");
                    c.ast()[val].repr(c);
                }
            }
            Self::Module(_) => {
                c.write_add("<module ");
                c.write_add(name);
                c.write_add(">");
            }
            Self::Generic(i) => c.write_add(format!("<generic #{i}>"))
        }
    }
}

impl Function {
    fn repr<C: Representer>(&self, c: &C, in_trait: bool) {
        c.write_add("fn");
        if !self.params.is_empty() {
            c.write_add("(");
            for (i, (name_span, ty)) in self.params.iter().enumerate() {
                let name = c.src(*name_span);
                c.write_add(name);
                c.space();
                ty.repr(c);
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
impl TypeDef {
    fn repr<C: Representer>(&self, c: &C) {
        match self {
            TypeDef::Struct(s) => s.repr(c),
            TypeDef::Enum(e) => e.repr(c),
        }
    }
}

impl StructDefinition {
    fn repr<C: Representer>(&self, c: &C) {
        c.write_add("struct {\n");
        let child = c.child();
        for (i, (name_span, ty)) in self.members.iter().enumerate() {
            child.begin_line();
            child.write_add(&c.ast()[*name_span]);
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
        for (_, name, args) in &self.variants {
            child.begin_line();
            child.write_add(name.as_str());
            if !args.is_empty() {
                child.write_add("(");
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        child.write_add(", ");
                    }
                    arg.repr(&child);
                }
                child.write_add(")");
            }
            /*
            if let Some(value) = value {
                child.write_add(" = ");
                child.write_add(value.to_string());
            }
            */
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
        match self {
            &Self::Function { id } => {
                c.ast()[id].repr(c, false);
            }
            &Self::Type { id } => c.ast()[id].repr(c),
            Self::Block { items, scope } => {
                c.write_add("{\n");
                let child = c.child();
                for (name, def) in &ast[*scope].definitions {
                    def.repr(&child, name);
                    c.writeln("\n");
                }
                for item in &ast[*items] {
                    child.write_start("");
                    item.repr(&child);
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
            Self::ReturnUnit { .. } => {
                c.write_add("ret");
            }
            Self::IntLiteral(span) | Self::FloatLiteral(span) | Self::StringLiteral(span) 
                => c.write_add(c.src(*span)),
            Self::BoolLiteral { start: _, val } => c.write_add(if *val { "true" } else { "false" }),
            Self::EnumLiteral { span: _, ident, args } => {
                c.char('.');
                c.write_add(c.src(*ident));
                if args.count > 0 {
                    c.char('(');
                    for arg in ast[*args].iter() {
                        arg.repr(c);
                    }
                    c.char(')');
                }
            }
            Self::Nested(_, inner) => {
                c.char('(');
                ast[*inner].repr(c);
                c.char(')');
            }
            Self::Unit(_) => c.write_add("()"),
            Self::Ident { span, .. } => c.write_add(c.src(*span)),
            Self::Hole(_) => c.char('_'),
            Self::Array(_, elems) => {
                let mut elems = ast[*elems].iter();
                c.char('[');
                if let Some(first) = elems.next() {
                    first.repr(c);
                }
                for elem in elems {
                    c.write_add(", ");
                    elem.repr(c);
                }
                c.char(']');
            }
            Self::Tuple(_, elems) => {
                let mut elems_iter = ast[*elems].iter();
                c.char('(');
                if let Some(elem) = elems_iter.next() {
                    elem.repr(c);
                };
                for elem in elems_iter {
                    c.write_add(", ");
                    elem.repr(c);
                }
                if elems.count() == 1 {
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
            Self::IfPat { start: _, pat, value, then } => {
                c.write_add("if ");
                ast[*pat].repr(c);
                c.write_add(" := ");
                ast[*value].repr(c);
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
            Self::IfPatElse { start: _, pat, value, then, else_ } => {
                c.write_add("if ");
                ast[*pat].repr(c);
                c.write_add(" := ");
                ast[*value].repr(c);
                let then = &ast[*then];
                match then {
                    Expr::Block { .. } => c.space(),
                    _ => c.write_add(": ")
                }
                then.repr(c);
                c.write_add(" else ");
                ast[*else_].repr(c);
            }
            Self::Match { span: _, val, extra_branches, branch_count } => {
                c.write_add("match ");
                ast[*val].repr(c);
                c.write_add(" {\n");
                let extra = ExprExtra { idx: *extra_branches, count: *branch_count * 2 };
                let match_c = c.child();
                let branches = &ast[extra];
                debug_assert_eq!(branches.len() % 2, 0);
                let mut branches = branches.iter();
                while let Some(pat) = branches.next() {
                    let branch = branches.next().unwrap();
                    c.begin_line();
                    pat.repr(&match_c);
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
            Self::WhilePat { start: _, pat, val, body } => {
                c.write_add("while ");
                ast[*pat].repr(c);
                c.write_add(" := ");
                ast[*val].repr(c);
                let body = &ast[*body];
                if body.is_block() {
                    c.space();
                } else {
                    c.write_add(": ");
                }
                body.repr(c);
            }
            Self::FunctionCall(call_id) => {
                let Call { called_expr, args, .. } = &ast[*call_id];
                let args = &ast[*args];
                let called = &ast[*called_expr];
                called.repr(c);
                c.write_add("(");
                for (i, arg) in args.iter().enumerate() {
                    arg.repr(c);
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
            Self::MemberAccess { left, name, .. } => {
                ast[*left].repr(c);
                c.char('.');
                c.write_add(c.src(*name));
            }
            Self::Index { expr, .. } => {
                c.char('[');
                ast[*expr].repr(c);
                c.char(']');
            }
            Self::TupleIdx { left: expr, idx, end: _ } => {
                ast[*expr].repr(c);
                c.char('.');
                c.write_add(idx.to_string());
            }
            Self::As(val, ty) => {
                ast[*val].repr(c);
                c.write_add(" as ");
                ty.repr(c);
            }
            Self::Root(_) => c.write_add("root"),
            Self::Asm { span: _, asm_str_span, args } => {
                c.write_add("asm(");
                c.write_add(c.src(*asm_str_span));
                for arg in &ast[*args] {
                    c.write_add(", ");
                    arg.repr(c);
                }
                c.char(')');
            }
            Self::Primitive { primitive, .. } => c.write_add(<&str>::from(*primitive))
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
            Self::Primitive { ty, .. } => ty.repr(c),
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
                let (inner, size, _) = &**array;
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
