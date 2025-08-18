use crate::dom::{Cond, Node, R};

pub fn render(mut dom: Node) -> String {
    let line_width = crate::LINE_WIDTH;
    compute(&mut dom, line_width);
    tracing::debug!(target: "format", "Dom after width compute:\n{dom:?}");
    let mut s = String::new();
    let mut f = Formatter {
        s: &mut s,
        mandatory_newline: false,
        pending_newlines: 0,
        indent: 0,
        column_position: 0,
        line_width,
    };
    f.fmt(&dom, Cond::Flat);
    f.write_pending_newlines();
    s
}

fn compute(node: &mut Node, line_width: u32) -> R {
    match node {
        Node::Group(nodes, r) => {
            debug_assert!(matches!(r, R::Width(0)), "R assigned before computing");
            for node in &mut *nodes {
                *r += compute(node, line_width);
            }
            if let R::Width(w) = *r
                && w > line_width
            {
                *r = R::Broken;
            }
            *r
        }
        Node::Text(text) | Node::TextIf(Cond::Flat, text) if text.ends_with('\n') => R::Broken,
        Node::Text(text) | Node::TextIf(Cond::Flat, text) => R::Width(text_width(text)),
        Node::TextIf(Cond::Broken, _) => R::Width(0), // assume the node is not broken
        Node::Indent(inner) => compute(inner, line_width) + R::Width(2),
    }
}

struct Formatter<'a> {
    s: &'a mut String,
    mandatory_newline: bool,
    pending_newlines: u32,
    column_position: u32,
    indent: usize,
    line_width: u32,
}
impl<'a> Formatter<'a> {
    fn text(&mut self, mut text: &str) {
        let newlines_only = text.chars().all(|c| c == '\n');
        if newlines_only {
            let newline_count = text.len() as u32;
            self.pending_newlines = if self.mandatory_newline && self.pending_newlines == 1 {
                // if there is exactly one newline, it just terminated a line and we want to print
                // additional newlines
                newline_count + 1
            } else {
                // if there are already multiple newlines, take the max
                self.pending_newlines.max(newline_count)
            };
            return;
        }
        self.write_pending_newlines();

        while text.ends_with('\n') {
            self.pending_newlines += 1;
            text = &text[..text.len() - 1];
        }
        if text.is_empty() && self.pending_newlines > 0 {
            self.mandatory_newline = true;
        }
        self.s.push_str(text);
        self.column_position += text_width(text);
    }

    fn write_pending_newlines(&mut self) {
        for _ in 0..self.pending_newlines {
            self.s.push('\n');
        }

        if self.pending_newlines > 0 {
            self.column_position = 0;
            for _ in 0..self.indent {
                self.s.push_str("  ");
                self.column_position += 2;
            }
        }
        self.pending_newlines = 0;
        self.mandatory_newline = false;
    }

    fn fmt(&mut self, node: &Node, cond: Cond) {
        match node {
            Node::Group(nodes, r) => {
                let cond = match r {
                    R::Broken => Cond::Broken,
                    &R::Width(w) if self.column_position + w > self.line_width => Cond::Broken,
                    _ => Cond::Flat,
                };
                for node in nodes {
                    self.fmt(node, cond);
                }
            }
            Node::Text(text) => self.text(text),
            Node::TextIf(if_cond, text) => {
                if *if_cond == cond {
                    self.text(text);
                }
            }
            Node::Indent(inner) => {
                self.indent += 1;
                self.fmt(inner, cond);
                self.indent -= 1;
            }
        }
    }
}

fn text_width(text: &str) -> u32 {
    // FIXME: this does not represent the width properly
    text.chars().count() as u32
}
