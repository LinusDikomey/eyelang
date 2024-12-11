#![deny(unused_must_use)]
#![allow(
    clippy::new_without_default,
    clippy::too_many_arguments,
    clippy::wrong_self_convention
)]

/// typechecking and emitting hir from the ast
pub mod check;
/// the query-based compiler able to answer and cache various requests
mod compiler;
/// compiler errors and error formatting
pub mod error;
/// compile-time code evaluation
mod eval;
/// high-level intermediate representation that knows type information and resolved identifiers
mod hir;
/// hir->ir lowering
mod irgen;
/// call the system linker
mod link;
/// parse source code into an ast
mod parser;
/// TypeTable data structure and logic for type inference/checking
mod types;

pub use compiler::{Compiler, Def, ProjectError};
pub use link::link;
pub use parser::ast::repr::ReprPrinter;
pub use span::{IdentPath, Span, TSpan};

id::id!(ProjectId);
impl Default for ProjectId {
    fn default() -> Self {
        Self::MISSING
    }
}
