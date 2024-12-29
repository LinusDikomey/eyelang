use crate::{BlockId, BlockTarget, FunctionId, GlobalId, Ref, TypeId};

#[derive(Debug, Clone, Copy)]
pub enum Argument<'a> {
    Ref(Ref),
    BlockTarget(BlockTarget<'a>),
    Int(u64),
    Float(f64),
    TypeId(TypeId),
    FunctionId(FunctionId),
    GlobalId(GlobalId),
}
impl From<Ref> for Argument<'_> {
    fn from(value: Ref) -> Self {
        Self::Ref(value)
    }
}
impl From<BlockId> for Argument<'_> {
    fn from(value: BlockId) -> Self {
        Self::BlockTarget(BlockTarget(value, &[]))
    }
}
impl<'a> From<BlockTarget<'a>> for Argument<'a> {
    fn from(value: BlockTarget<'a>) -> Self {
        Self::BlockTarget(value)
    }
}
impl From<u64> for Argument<'_> {
    fn from(value: u64) -> Self {
        Self::Int(value)
    }
}
impl From<u32> for Argument<'_> {
    fn from(value: u32) -> Self {
        Self::Int(value.into())
    }
}
impl From<f64> for Argument<'_> {
    fn from(value: f64) -> Self {
        Self::Float(value)
    }
}
impl From<TypeId> for Argument<'_> {
    fn from(value: TypeId) -> Self {
        Self::TypeId(value)
    }
}
impl From<FunctionId> for Argument<'_> {
    fn from(value: FunctionId) -> Self {
        Self::FunctionId(value)
    }
}
impl From<GlobalId> for Argument<'_> {
    fn from(value: GlobalId) -> Self {
        Self::GlobalId(value)
    }
}

pub trait IntoArgs<'a> {
    type Args: ExactSizeIterator<Item = Argument<'a>>;

    fn into_args(self) -> Self::Args;
}
impl IntoArgs<'static> for Vec<Ref> {
    // PERF: specifying function pointer here in Map type might worsen performance since it becomes
    // a dynamic call
    type Args = std::iter::Map<std::vec::IntoIter<Ref>, fn(Ref) -> Argument<'static>>;
    fn into_args(self) -> Self::Args {
        self.into_iter().map(Argument::Ref)
    }
}
impl IntoArgs<'static> for () {
    type Args = std::array::IntoIter<Argument<'static>, 0>;

    fn into_args(self) -> Self::Args {
        [].into_iter()
    }
}
impl<'a, T: Into<Argument<'a>>> IntoArgs<'a> for T {
    type Args = std::array::IntoIter<Argument<'a>, 1>;

    fn into_args(self) -> Self::Args {
        [self.into()].into_iter()
    }
}

impl<'a, T: Into<Argument<'a>>> IntoArgs<'a> for (T,) {
    type Args = std::array::IntoIter<Argument<'a>, 1>;

    fn into_args(self) -> Self::Args {
        [self.0.into()].into_iter()
    }
}

impl<'a, A0: Into<Argument<'a>>, A1: Into<Argument<'a>>> IntoArgs<'a> for (A0, A1) {
    type Args = std::array::IntoIter<Argument<'a>, 2>;

    fn into_args(self) -> Self::Args {
        [self.0.into(), self.1.into()].into_iter()
    }
}
impl<'a, A0: Into<Argument<'a>>, A1: Into<Argument<'a>>, A2: Into<Argument<'a>>> IntoArgs<'a>
    for (A0, A1, A2)
{
    type Args = std::array::IntoIter<Argument<'a>, 3>;

    fn into_args(self) -> Self::Args {
        [self.0.into(), self.1.into(), self.2.into()].into_iter()
    }
}
impl<
        'a,
        A0: Into<Argument<'a>>,
        A1: Into<Argument<'a>>,
        A2: Into<Argument<'a>>,
        A3: Into<Argument<'a>>,
    > IntoArgs<'a> for (A0, A1, A2, A3)
{
    type Args = std::array::IntoIter<Argument<'a>, 4>;

    fn into_args(self) -> Self::Args {
        [self.0.into(), self.1.into(), self.2.into(), self.3.into()].into_iter()
    }
}
