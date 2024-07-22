use span::{IdentPath, TSpan};

use crate::Primitive;

#[derive(Debug, Clone)]
pub enum UnresolvedType {
    Primitive {
        ty: Primitive,
        span_start: u32,
    },
    Unresolved(IdentPath, Option<(Box<[UnresolvedType]>, TSpan)>),
    Pointer(Box<(UnresolvedType, u32)>),
    Array(Box<(UnresolvedType, Option<u32>, TSpan)>),
    Tuple(Vec<UnresolvedType>, TSpan),
    Function {
        span_and_return_type: Box<(TSpan, UnresolvedType)>,
        params: Box<[UnresolvedType]>,
    },
    Infer(TSpan),
}
impl UnresolvedType {
    pub fn to_string(&self, s: &mut String, src: &str) {
        match self {
            &UnresolvedType::Primitive { ty, .. } => s.push_str(ty.into()),
            UnresolvedType::Unresolved(path, generics) => {
                let (root, segments, last) = path.segments(src);
                if root.is_some() {
                    s.push_str("root");
                }
                let mut prev = root.is_some();
                for (segment, _) in segments {
                    if prev {
                        s.push('.');
                    }
                    s.push_str(segment);
                    prev = true;
                }
                if let Some((last, _)) = last {
                    if prev {
                        s.push('.');
                    }
                    s.push_str(last);
                }
                if let Some((generics, _)) = generics {
                    s.push('[');
                    for (i, ty) in generics.iter().enumerate() {
                        if i != 0 {
                            s.push_str(", ");
                            ty.to_string(s, src);
                        }
                    }
                    s.push(']');
                }
            }
            UnresolvedType::Pointer(pointee) => {
                s.push('*');
                pointee.0.to_string(s, src);
            }
            UnresolvedType::Array(b) => {
                s.push('[');
                b.0.to_string(s, src);
                s.push_str("; ");
                use core::fmt::Write;
                match b.1 {
                    Some(count) => write!(s, "{count}]").unwrap(),
                    None => s.push_str("_]"),
                }
            }
            UnresolvedType::Tuple(types, _) => {
                s.push('(');
                for (i, ty) in types.iter().enumerate() {
                    if i != 0 {
                        s.push_str(", ");
                    }
                    ty.to_string(s, src);
                }
                s.push(')');
            }
            UnresolvedType::Function {
                span_and_return_type,
                params,
            } => {
                s.push_str("fn(");
                for (i, ty) in params.iter().enumerate() {
                    if i != 0 {
                        s.push_str(", ");
                    }
                    ty.to_string(s, src);
                }
                s.push_str(") -> ");
                span_and_return_type.1.to_string(s, src);
            }
            UnresolvedType::Infer(_) => s.push('_'),
        }
    }

    pub fn span(&self) -> TSpan {
        match self {
            &UnresolvedType::Primitive { ty, span_start } => {
                TSpan::with_len(span_start, ty.token_len().get() - 1)
            }
            UnresolvedType::Tuple(_, span) | UnresolvedType::Infer(span) => *span,
            UnresolvedType::Unresolved(path, generics) => generics.as_ref().map_or_else(
                || path.span(),
                |generics| TSpan::new(path.span().start, generics.1.end),
            ),
            UnresolvedType::Array(array) => array.2,
            UnresolvedType::Pointer(ptr) => {
                let (inner, start) = &**ptr;
                TSpan::new(*start, inner.span().end)
            }
            UnresolvedType::Function {
                span_and_return_type,
                ..
            } => span_and_return_type.0,
        }
    }
}
