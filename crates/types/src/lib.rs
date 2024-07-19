mod float;
mod int;
mod layout;
mod primitive;
mod resolved_type;
mod unresolved;

pub use float::FloatType;
pub use int::IntType;
pub use layout::Layout;
pub use primitive::Primitive;
pub use resolved_type::{FunctionType, Type};
pub use unresolved::UnresolvedType;
