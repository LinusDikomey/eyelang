use std::fmt;

pub enum Node {
    Group(Vec<Node>, R),
    Text(Box<str>),
    TextIf(Cond, Box<str>),
    Indent(Box<Node>),
}
impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        debug_print_node(0, self, f)
    }
}

fn debug_print_node(indent: usize, node: &Node, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let indent_line = |f: &mut fmt::Formatter<'_>| {
        for _ in 0..indent {
            write!(f, "  ")?;
        }
        Ok(())
    };
    indent_line(f)?;
    match node {
        Node::Group(nodes, r) => {
            writeln!(f, "<group r={r:?}>")?;
            for node in nodes {
                debug_print_node(indent + 1, node, f)?;
            }
            indent_line(f)?;
            writeln!(f, "</group>")?;
            Ok(())
        }
        Node::Text(text) => writeln!(f, "<text t={text:?}>"),
        Node::TextIf(cond, text) => writeln!(
            f,
            "<text t={text:?} if={}>",
            match cond {
                Cond::Flat => "flat",
                Cond::Broken => "broken",
            }
        ),
        Node::Indent(node) => {
            writeln!(f, "<indent>")?;
            debug_print_node(indent + 1, node, f)?;
            indent_line(f)?;
            writeln!(f, "</indent>")
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cond {
    Flat,
    Broken,
}

#[derive(Clone, Copy, Debug)]
pub enum R {
    Width(u32),
    Broken,
}
impl std::ops::Add for R {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Width(a), Self::Width(b)) => Self::Width(a + b),
            _ => Self::Broken,
        }
    }
}
impl std::ops::AddAssign for R {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}
