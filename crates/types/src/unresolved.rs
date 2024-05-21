use span::{IdentPath, TSpan};

use crate::Primitive;

#[derive(Debug, Clone)]
pub enum UnresolvedType {
    Primitive { ty: Primitive, span_start: u32 },
    Unresolved(IdentPath, Option<(Box<[UnresolvedType]>, TSpan)>),
    Pointer(Box<(UnresolvedType, u32)>),
    Array(Box<(UnresolvedType, Option<u32>, TSpan)>),
    Tuple(Vec<UnresolvedType>, TSpan),
    Infer(u32),
}
impl UnresolvedType {
    pub fn span(&self) -> TSpan {
        match self {
            &UnresolvedType::Primitive { ty, span_start } => {
                TSpan::with_len(span_start, ty.token_len())
            }
            UnresolvedType::Tuple(_, span) => *span,
            UnresolvedType::Unresolved(path, generics) => generics.as_ref().map_or_else(
                || path.span(),
                |generics| TSpan::new(path.span().start, generics.1.end),
            ),
            UnresolvedType::Array(array) => array.2,
            UnresolvedType::Pointer(ptr) => {
                let (inner, start) = &**ptr;
                TSpan::new(*start, inner.span().end)
            }
            UnresolvedType::Infer(s) => TSpan::new(*s, *s),
        }
    }
}
