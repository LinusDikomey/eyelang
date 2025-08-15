use std::fmt;

use color_format::cwrite;

use crate::{
    Compiler,
    typing::{LocalTypeId, TypeTable},
};

pub struct TypeDisplay<'a> {
    pub ty: LocalTypeId,
    pub table: &'a TypeTable,
    pub compiler: &'a Compiler,
}
impl<'a> fmt::Display for TypeDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        self.table
            .type_to_string(self.compiler, self.table[self.ty], &mut s);
        cwrite!(f, "#m<{s}>")
    }
}
