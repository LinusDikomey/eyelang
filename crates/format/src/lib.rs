use error::Errors;
use parser::parse;

/// Convert to dom
mod convert;
/// Representation of a formattable syntax tree
mod dom;
/// Final layouuting and rendering of the dom
mod render;

pub fn format(src: Box<str>) -> (String, Errors) {
    let mut errors = Errors::new();
    let cst = parse::<parser::ast::Token>(src, &mut errors, dmap::new());
    let dom = convert::module(&cst);
    tracing::debug!(target: "fmt::dom", "Format dom:\n{dom:?}\n");
    (render::render(dom), errors)
}
