use std::fmt;

use color_format::{cwrite, cwriteln};
use parser::ast::{AssignType, Primitive};

use crate::{
    Compiler,
    hir::{
        Arithmetic, CastType, Comparison, Hir, LValue, LValueId, Logic, Node, NodeId, Pattern,
        PatternId, PatternIds, TypeProperty,
    },
    typing::{LocalTypeId, LocalTypeIds},
};

pub struct HirDisplay<'a> {
    pub node: NodeId,
    pub hir: &'a Hir,
    pub compiler: &'a Compiler,
    pub indent_count: usize,
}
impl<'a> fmt::Display for HirDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let &Self {
            node,
            hir,
            compiler,
            indent_count,
        } = self;
        fn indent_n(f: &mut fmt::Formatter<'_>, n: usize) -> fmt::Result {
            for _ in 0..n {
                write!(f, "  ")?;
            }
            Ok(())
        }
        let indent = |f| indent_n(f, indent_count);
        match &hir[node] {
            Node::Invalid => {
                cwrite!(f, "(#b<invalid>)")?;
            }
            Node::Block(ids) => {
                cwriteln!(f, "(")?;
                for id in ids.iter() {
                    indent_n(f, indent_count + 1)?;
                    cwriteln!(f, "{}", hir.display(id, compiler, indent_count + 1))?;
                }
                indent(f)?;
                cwrite!(f, ")")?;
            }
            Node::Unit => cwrite!(f, "(#b<unit>)")?,
            &Node::IntLiteral { val, ty } => {
                cwrite!(
                    f,
                    "(#b<int> #y<{val}>): {}",
                    compiler.types.display(hir[ty])
                )?;
            }
            &Node::FloatLiteral { val, ty } => {
                cwrite!(
                    f,
                    "(#b<float> #y<{val}>): {}",
                    compiler.types.display(hir[ty])
                )?;
            }
            Node::BoolLiteral(b) => {
                cwrite!(f, "#y<{b}>")?;
            }
            &Node::ArrayLiteral { elems, array_ty } => {
                cwrite!(f, "(#b<array> ")?;
                for (i, elem) in elems.iter().enumerate() {
                    if i != 0 {
                        cwrite!(f, " ")?;
                    }
                    cwrite!(f, "{}", hir.display(elem, compiler, indent_count))?;
                }
                cwrite!(f, "): {}", compiler.types.display(hir[array_ty]))?;
            }
            Node::TupleLiteral { elems, elem_types } => {
                cwrite!(f, "(#b<tuple> ")?;
                for (i, (elem, ty)) in elems.iter().zip(elem_types.iter()).enumerate() {
                    if i != 0 {
                        cwrite!(f, " ")?;
                    }
                    cwrite!(
                        f,
                        "{}: {}",
                        hir.display(elem, compiler, indent_count),
                        compiler.types.display(hir[ty])
                    )?;
                }
                cwrite!(f, ")")?;
            }
            &Node::EnumLiteral {
                elems,
                elem_types,
                enum_ty,
            } => {
                cwrite!(f, "(#b<enum-literal>")?;
                for (i, (elem, ty)) in elems.iter().zip(elem_types.iter()).enumerate() {
                    if i != 0 {
                        cwrite!(f, " ")?;
                    }
                    cwrite!(
                        f,
                        "{}: {}",
                        hir.display(elem, compiler, indent_count),
                        compiler.types.display(hir[ty])
                    )?;
                }
                cwrite!(f, "): {}", compiler.types.display(hir[enum_ty]))?;
            }
            Node::StringLiteral(s) => {
                cwrite!(f, "(#b<string> {s:?})")?;
            }
            Node::InferredEnumOrdinal(id) => {
                cwrite!(f, "(#b<enum-ordinal> {}{})", "#", id.0)?;
            }
            &Node::Declare { pattern } => {
                cwrite!(f, "(#b<decl> {})", hir.display_pattern(pattern, compiler))?;
            }
            &Node::DeclareWithVal { pattern, val } => {
                cwrite!(
                    f,
                    "(#b<decl> {} {})",
                    hir.display_pattern(pattern, compiler),
                    hir.display(val, compiler, indent_count),
                )?;
            }
            Node::Variable(id) => cwrite!(f, "(#b<var> #y<{}>)", id.0)?,
            &Node::Global(module, id, ty) => cwrite!(
                f,
                "(#b<global> {}:{}): {}",
                module.idx(),
                id.idx(),
                compiler.types.display(hir[ty])
            )?,
            &Node::Assign(lval, val, assign_ty, ty) => {
                let op = match assign_ty {
                    AssignType::Assign => "",
                    AssignType::AddAssign => "-add",
                    AssignType::SubAssign => "-sub",
                    AssignType::MulAssign => "-mul",
                    AssignType::DivAssign => "-div",
                    AssignType::ModAssign => "-mod",
                };
                cwrite!(
                    f,
                    "(#b<assign{op}> {}: {} {})",
                    hir.display_lvalue(lval, compiler, indent_count),
                    compiler.types.display(hir[ty]),
                    hir.display(val, compiler, indent_count),
                )?;
            }
            &Node::Const { id, ty } => cwrite!(
                f,
                "(#b<const> #y<{}>): {}",
                id.0,
                compiler.types.display(hir[ty])
            )?,
            &Node::Negate(id, ty) => {
                cwrite!(
                    f,
                    "(#b<neg> {}): {}",
                    hir.display(id, compiler, indent_count),
                    compiler.types.display(hir[ty]),
                )?;
            }
            &Node::Not(id) => cwrite!(f, "(#b<not> {})", hir.display(id, compiler, indent_count))?,
            &Node::AddressOf { value, value_ty } => cwrite!(
                f,
                "(#b<addr> {}: {})",
                hir.display_lvalue(value, compiler, indent_count),
                compiler.types.display(hir[value_ty])
            )?,
            &Node::Deref { value, deref_ty } => cwrite!(
                f,
                "(#b<deref> {}): {}",
                hir.display(value, compiler, indent_count),
                compiler.types.display(hir[deref_ty]),
            )?,
            &Node::Promote { value, variable } => cwrite!(
                f,
                "(#b<promote> {} #m<into> (#b<var> #y<{}>))",
                hir.display(value, compiler, indent_count),
                variable.0,
            )?,
            &Node::Cast(id) => {
                let cast = &hir[id];
                cwrite!(f, "(#b<cast> ")?;
                match cast.cast_ty {
                    CastType::Invalid => cwrite!(f, "#m<invalid>")?,
                    CastType::Noop => cwrite!(f, "#m<noop>")?,
                    CastType::Int { from, to } => cwrite!(
                        f,
                        "(#m<int> #r<{}> #r<{}>)",
                        <&str>::from(Primitive::from(from)),
                        <&str>::from(Primitive::from(to)),
                    )?,
                    CastType::Float { from, to } => cwrite!(
                        f,
                        "(#m<float> #r<{}> #r<{}>)",
                        <&str>::from(Primitive::from(from)),
                        <&str>::from(Primitive::from(to)),
                    )?,
                    CastType::IntToFloat { from, to } => cwrite!(
                        f,
                        "(#m<int-float> #r<{}> #r<{}>)",
                        <&str>::from(Primitive::from(from)),
                        <&str>::from(Primitive::from(to)),
                    )?,
                    CastType::FloatToInt { from, to } => cwrite!(
                        f,
                        "(#m<float-int> #r<{}> #r<{}>)",
                        <&str>::from(Primitive::from(from)),
                        <&str>::from(Primitive::from(to)),
                    )?,
                    CastType::IntToPtr { from } => cwrite!(
                        f,
                        "(#m<int-ptr> #r<{}>)",
                        <&str>::from(Primitive::from(from))
                    )?,
                    CastType::PtrToInt { to } => {
                        cwrite!(f, "(#m<ptr-int> #r<{}>)", <&str>::from(Primitive::from(to)))?
                    }
                    CastType::EnumToInt { from, to } => cwrite!(
                        f,
                        "(#b<enum-int> {} #r<{}>",
                        compiler.types.display(hir[from]),
                        <&str>::from(Primitive::from(to))
                    )?,
                }
                cwrite!(f, " {})", hir.display(cast.val, compiler, indent_count))?;
            }
            &Node::Comparison {
                l,
                r,
                cmp,
                compared: _,
            } => {
                let cmp = match cmp {
                    Comparison::LT => "<",
                    Comparison::GT => ">",
                    Comparison::LE => "<=",
                    Comparison::GE => ">=",
                };
                cwrite!(
                    f,
                    "(#b<{cmp}> {} {})",
                    hir.display(l, compiler, indent_count),
                    hir.display(r, compiler, indent_count),
                )?
            }
            &Node::Logic { l, r, logic } => {
                let logic = match logic {
                    Logic::And => "and",
                    Logic::Or => "or",
                };
                cwrite!(
                    f,
                    "(#b<{logic}> {} {})",
                    hir.display(l, compiler, indent_count),
                    hir.display(r, compiler, indent_count),
                )?
            }
            &Node::Arithmetic(l, r, op, ty) => {
                let op = match op {
                    Arithmetic::Add => "+",
                    Arithmetic::Sub => "-",
                    Arithmetic::Mul => "*",
                    Arithmetic::Div => "/",
                    Arithmetic::Mod => "%",
                };
                cwrite!(
                    f,
                    "(#b<{op}> {} {}): {}",
                    hir.display(l, compiler, indent_count),
                    hir.display(r, compiler, indent_count),
                    compiler.types.display(hir[ty]),
                )?;
            }
            &Node::Element {
                tuple_value,
                index,
                elem_types,
            } => {
                cwrite!(
                    f,
                    "(#b<element> #y<{index}> {}: (",
                    hir.display(tuple_value, compiler, indent_count),
                )?;
                for (i, elem) in elem_types.iter().enumerate() {
                    if i != 0 {
                        cwrite!(f, ", ")?;
                    }
                    cwrite!(f, "{}", compiler.types.display(hir[elem]))?;
                }
                cwrite!(f, "))")?;
            }
            &Node::ArrayIndex {
                array,
                index,
                elem_ty,
            } => {
                cwrite!(
                    f,
                    "(#b<index> {} {}): {}",
                    hir.display(array, compiler, indent_count),
                    hir.display(index, compiler, indent_count),
                    compiler.types.display(hir[elem_ty]),
                )?;
            }
            &Node::Return(val) => cwrite!(
                f,
                "(#b<return> {})",
                hir.display(val, compiler, indent_count),
            )?,
            &Node::IfElse {
                cond,
                then,
                else_,
                resulting_ty,
            } => {
                cwriteln!(f, "(if {}", hir.display(cond, compiler, indent_count),)?;
                for branch in [then, else_] {
                    indent_n(f, indent_count + 1)?;
                    cwriteln!(f, "{}", hir.display(branch, compiler, indent_count + 1))?;
                }
                indent(f)?;
                cwrite!(f, "): {}", compiler.types.display(hir[resulting_ty]))?;
            }
            &Node::IfPatElse {
                pat,
                val,
                then,
                else_,
                resulting_ty,
            } => {
                cwriteln!(
                    f,
                    "(#b<if-pat> {} {}",
                    hir.display_pattern(pat, compiler),
                    hir.display(val, compiler, indent_count)
                )?;
                for branch in [then, else_] {
                    indent_n(f, indent_count + 1)?;
                    cwriteln!(f, "{}", hir.display(branch, compiler, indent_count + 1))?;
                }
                indent(f)?;
                cwrite!(f, "): {}", compiler.types.display(hir[resulting_ty]))?;
            }
            &Node::Match {
                value,
                branch_index,
                pattern_index,
                branch_count,
                resulting_ty,
            } => {
                cwrite!(
                    f,
                    "(#b<match> {}",
                    hir.display(value, compiler, indent_count)
                )?;
                for i in 0..branch_count {
                    cwriteln!(f)?;
                    indent_n(f, indent_count + 1)?;
                    let pattern = PatternId(pattern_index + i);
                    let branch = NodeId(branch_index + i);
                    cwrite!(
                        f,
                        "{} {}",
                        hir.display_pattern(pattern, compiler),
                        hir.display(branch, compiler, indent_count + 1)
                    )?;
                }
                cwriteln!(f)?;
                indent(f)?;
                cwrite!(f, "): {}", compiler.types.display(hir[resulting_ty]))?;
            }
            &Node::While { cond, body } => cwrite!(
                f,
                "(#b<while> {} {})",
                hir.display(cond, compiler, indent_count),
                hir.display(body, compiler, indent_count),
            )?,
            &Node::WhilePat { pat, val, body } => cwrite!(
                f,
                "(#b<while> {} {} {})",
                hir.display_pattern(pat, compiler),
                hir.display(val, compiler, indent_count),
                hir.display(body, compiler, indent_count),
            )?,
            &Node::Call {
                function,
                args,
                arg_types,
                return_ty,
                noreturn: _,
            } => {
                cwrite!(
                    f,
                    "(#b<call> {}",
                    hir.display(function, compiler, indent_count)
                )?;
                for (arg, ty) in args.iter().zip(arg_types.iter()) {
                    cwrite!(
                        f,
                        " {}: {}",
                        hir.display(arg, compiler, indent_count),
                        compiler.types.display(hir[ty]),
                    )?;
                }
                cwrite!(f, "): {}", compiler.types.display(hir[return_ty]))?;
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
                cwrite!(
                    f,
                    "(#b<call-trait-method> <#m<trait> {}:{}",
                    trait_id.0.idx(),
                    trait_id.1.idx()
                )?;
                if trait_generics.count > 0 {
                    cwrite!(f, "[")?;
                    for (i, generic) in trait_generics.iter().enumerate() {
                        if i != 0 {
                            cwrite!(f, ", ")?;
                        }
                        cwrite!(f, "{}", compiler.types.display(hir[generic]))?;
                    }
                    cwrite!(f, "]")?;
                }
                cwrite!(f, " #m<as> {}", compiler.types.display(hir[self_ty]))?;
                cwrite!(f, ".{method_index}")?;
                for arg in args.iter() {
                    cwrite!(f, " {}", hir.display(arg, compiler, indent_count))?;
                }
                cwrite!(f, "): {}", compiler.types.display(hir[return_ty]))?;
            }
            &Node::TypeProperty(ty, property) => {
                let prop = match property {
                    TypeProperty::Size => "size",
                    TypeProperty::Align => "align",
                    TypeProperty::Stride => "stride",
                };
                cwrite!(
                    f,
                    "(#b<type_prop> #c<{prop}> {})",
                    compiler.types.display(hir[ty])
                )?;
            }
            &Node::FunctionItem(module, function, generics) => {
                cwrite!(f, "(#b<function> {}:{}[", module.idx(), function.idx())?;
                for (i, generic) in generics.iter().enumerate() {
                    if i != 0 {
                        cwrite!(f, " ")?;
                    }
                    cwrite!(f, "{}", compiler.types.display(hir[generic]))?;
                }
                cwrite!(f, "])")?;
            }
            &Node::Capture(id) => cwrite!(f, "(#b<capture> #y<{}>)", id.0)?,
            &Node::Break(n) => cwrite!(f, "(#b<break> #y<{n}>)")?,
            &Node::Continue(n) => cwrite!(f, "(#b<continue> #y<{n}>)")?,
        }
        Ok(())
    }
}

pub struct PatternDisplay<'a> {
    pub pattern: PatternId,
    pub hir: &'a Hir,
    pub compiler: &'a Compiler,
}
impl<'a> fmt::Display for PatternDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let &Self {
            pattern,
            hir,
            compiler,
        } = self;
        match &hir[pattern] {
            Pattern::Invalid => cwrite!(f, "#m<invalid>"),
            Pattern::Variable(id) => {
                let var_ty = hir.vars[id.idx()];
                cwrite!(
                    f,
                    "(#b<var> #y<{}>): {}",
                    id.0,
                    compiler.types.display(hir[var_ty]),
                )
            }
            Pattern::Ignore => cwrite!(f, "_"),
            &Pattern::Tuple {
                member_count,
                patterns,
                types: type_ids,
            } => {
                cwrite!(f, "(")?;
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
                        cwrite!(f, " ")?;
                    }
                    cwrite!(f, "{}", hir.display_pattern(pat, compiler))?;
                }
                cwrite!(f, "): (")?;
                for (i, ty) in type_ids.iter().enumerate() {
                    if i != 0 {
                        cwrite!(f, " ")?;
                    }
                    cwrite!(f, "{}", compiler.types.display(hir[ty]))?;
                }
                cwrite!(f, ")")
            }
            &Pattern::Int(signed, unsigned_val, ty) => cwrite!(
                f,
                "(#b<int> #y<{}{}>): {}",
                if signed { "-" } else { "" },
                unsigned_val,
                compiler.types.display(hir[ty]),
            ),

            Pattern::Bool(b) => cwrite!(f, "#m<{b}>"),
            Pattern::String(s) => cwrite!(f, "(#m<string> #y<{s:?}>)"),
            &Pattern::Range {
                min_max,
                ty: _,
                min_max_signs,
                inclusive,
            } => {
                cwrite!(
                    f,
                    "(#b<range> {}{} {}{}#m<{}>)",
                    if min_max_signs.0 { "-" } else { "" },
                    min_max.0,
                    if min_max_signs.1 { "-" } else { "" },
                    min_max.1,
                    if inclusive { " inclusive" } else { "" }
                )
            }
            &Pattern::EnumVariant {
                ordinal,
                types: enum_types,
                args,
            } => {
                cwrite!(
                    f,
                    "(#b<enum-variant> #y<{ordinal:?}>: {}",
                    compiler.types.display(hir[LocalTypeId(enum_types)]),
                )?;
                for (arg, ty) in args.iter().zip(
                    LocalTypeIds {
                        idx: enum_types + 1,
                        count: args.count,
                    }
                    .iter(),
                ) {
                    cwrite!(
                        f,
                        " {}: {}",
                        hir.display_pattern(arg, compiler),
                        compiler.types.display(hir[ty]),
                    )?;
                }
                cwrite!(f, ")")
            }
        }
    }
}

pub struct LValueDisplay<'a> {
    pub lval: LValueId,
    pub hir: &'a Hir,
    pub compiler: &'a Compiler,
    pub indent_count: usize,
}
impl<'a> fmt::Display for LValueDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            lval,
            hir,
            compiler,
            indent_count,
        } = self;
        let indent_count = *indent_count;
        match hir[*lval] {
            LValue::Invalid => cwrite!(f, "(#b<invalid>)"),
            LValue::Variable(id) => cwrite!(f, "(#b<var> #y<{}>)", id.0),
            LValue::Global(module, id) => cwrite!(f, "(#b<global> {} {})", module.idx(), id.idx()),
            LValue::Deref(val) => {
                cwrite!(f, "(deref {})", hir.display(val, compiler, indent_count))
            }
            LValue::Member {
                tuple,
                index,
                elem_types,
            } => {
                cwrite!(
                    f,
                    "(#b<member> #y<{index}> {}: (",
                    hir.display_lvalue(tuple, compiler, indent_count),
                )?;
                for (i, elem) in elem_types.iter().enumerate() {
                    if i != 0 {
                        cwrite!(f, ", ")?;
                    }
                    cwrite!(f, "{}", compiler.types.display(hir[elem]))?;
                }
                cwrite!(f, "))")
            }
            LValue::ArrayIndex {
                array,
                index,
                elem_ty: element_type,
            } => cwrite!(
                f,
                "(#b<index> {} {}): {}",
                hir.display_lvalue(array, compiler, indent_count),
                hir.display(index, compiler, indent_count),
                compiler.types.display(hir[element_type]),
            ),
        }
    }
}
