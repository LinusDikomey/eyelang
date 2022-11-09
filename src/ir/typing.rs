use std::{borrow::Cow, ops::Index};

use crate::{error::*, ir::TypeDef, span::Span, types::Primitive};

use super::{SymbolKey, Type, TypeInfoOrIndex, TypingCtx};
