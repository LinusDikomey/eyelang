use crate::ast::ModuleId;

#[derive(Debug, Clone, Copy)]
pub struct TSpan {
    pub start: u32,
    pub end: u32
}
impl TSpan {
    pub fn new(start: u32, end: u32) -> Self {
        debug_assert!(start <= end+1, "Invalid span constructed");
        Self { start, end }
    }
    pub fn in_mod(self, module: ModuleId) -> Span {
        Span::new(self.start, self.end, module)
    }
    pub fn range(self) -> std::ops::RangeInclusive<usize> {
        self.start as usize ..= self.end as usize
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Span {
    pub start: u32,
    pub end: u32,
    pub module: ModuleId
}
impl Span {
    pub fn new(start: u32, end: u32, module: ModuleId) -> Self {
        Self { start, end, module }
    }
    pub fn _todo(module: ModuleId) -> Self {
        Self { start: 0, end: 0, module }
    }
}