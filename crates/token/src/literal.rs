use std::fmt;

use crate::{FloatType, IntType};

#[derive(Debug, Clone, Copy)]
pub struct IntLiteral {
    pub val: u128,
    pub ty: Option<IntType>,
}
impl IntLiteral {
    pub fn parse(s: &str) -> Self {
        let val = s.parse::<u128>().unwrap();
        Self { val, ty: None }
    }
}
impl fmt::Display for IntLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.val)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FloatLiteral {
    pub val: f64,
    pub ty: Option<FloatType>,
}
impl FloatLiteral {
    pub fn parse(s: &str) -> Self {
        Self {
            val: s.parse().unwrap(),
            ty: None,
        }
    }
}
impl fmt::Display for FloatLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.val)
    }
}
