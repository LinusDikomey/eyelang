use std::fmt;

use color_format::{cwrite, cwriteln};

use crate::{
    Compiler,
    compiler::{BodyOrTypes, CheckedFunction},
};

pub struct CheckedFunctionDisplay<'a> {
    pub function: &'a CheckedFunction,
    pub compiler: &'a Compiler,
}
impl<'a> fmt::Display for CheckedFunctionDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { function, compiler } = self;
        cwrite!(f, "BEGIN HIR {}", function.name)?;
        if function.generic_count != 0 {
            cwrite!(f, "[")?;
            for i in 0..function.generic_count {
                if i != 0 {
                    cwrite!(f, ", ")?;
                }
                cwrite!(f, "${i}")?;
            }
            cwrite!(f, "]")?;
        }
        cwrite!(f, "(")?;
        for (i, param) in function.params.iter().enumerate() {
            if i != 0 {
                cwrite!(f, ", ")?;
            }
            cwrite!(
                f,
                "(var {i}): {}",
                self.compiler.types.display(function[param])
            )?;
        }
        if function.varargs {
            if function.params.count != 0 {
                cwrite!(f, ", ")?;
            }
            cwrite!(f, "...")?;
        }
        cwrite!(
            f,
            ") -{} {}",
            ">",
            self.compiler.types.display(function[function.return_type]),
        )?; // TODO: problem in color-format: can't escape >
        cwrite!(f, "\n  ")?;
        match &function.body_or_types {
            BodyOrTypes::Body(body) => {
                cwrite!(f, "{}", body.display(body.root_id(), compiler, 1))?;
            }
            BodyOrTypes::Types(_) => {
                cwriteln!(f, "  #m<<extern{}>", ">")?;
            }
        }
        cwriteln!(f, "\nEND HIR\n")
    }
}
