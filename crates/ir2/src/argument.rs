use crate::{BlockId, FunctionId, GlobalId, Ref, TypeId};

#[derive(Debug, Clone, Copy)]
pub enum Argument {
    Ref(Ref),
    Block(BlockId),
    Int(u32),
    TypeId(TypeId),
    FunctionId(FunctionId),
    GlobalId(GlobalId),
}
impl From<Ref> for Argument {
    fn from(value: Ref) -> Self {
        Self::Ref(value)
    }
}
impl From<BlockId> for Argument {
    fn from(value: BlockId) -> Self {
        Self::Block(value)
    }
}
impl From<u32> for Argument {
    fn from(value: u32) -> Self {
        Self::Int(value)
    }
}
impl From<TypeId> for Argument {
    fn from(value: TypeId) -> Self {
        Self::TypeId(value)
    }
}
impl From<FunctionId> for Argument {
    fn from(value: FunctionId) -> Self {
        Self::FunctionId(value)
    }
}
impl From<GlobalId> for Argument {
    fn from(value: GlobalId) -> Self {
        Self::GlobalId(value)
    }
}

pub trait IntoArgs {
    type Args: ExactSizeIterator<Item = Argument>;

    fn into_args(self) -> Self::Args;
}
impl IntoArgs for () {
    type Args = std::array::IntoIter<Argument, 0>;

    fn into_args(self) -> Self::Args {
        [].into_iter()
    }
}
impl<T: Into<Argument>> IntoArgs for T {
    type Args = std::array::IntoIter<Argument, 1>;

    fn into_args(self) -> Self::Args {
        [self.into()].into_iter()
    }
}

impl<T: Into<Argument>> IntoArgs for (T,) {
    type Args = std::array::IntoIter<Argument, 1>;

    fn into_args(self) -> Self::Args {
        [self.0.into()].into_iter()
    }
}

impl<A0: Into<Argument>, A1: Into<Argument>> IntoArgs for (A0, A1) {
    type Args = std::array::IntoIter<Argument, 2>;

    fn into_args(self) -> Self::Args {
        [self.0.into(), self.1.into()].into_iter()
    }
}
impl<A0: Into<Argument>, A1: Into<Argument>, A2: Into<Argument>> IntoArgs for (A0, A1, A2) {
    type Args = std::array::IntoIter<Argument, 3>;

    fn into_args(self) -> Self::Args {
        [self.0.into(), self.1.into(), self.2.into()].into_iter()
    }
}
impl<A0: Into<Argument>, A1: Into<Argument>, A2: Into<Argument>, A3: Into<Argument>> IntoArgs
    for (A0, A1, A2, A3)
{
    type Args = std::array::IntoIter<Argument, 4>;

    fn into_args(self) -> Self::Args {
        [self.0.into(), self.1.into(), self.2.into(), self.3.into()].into_iter()
    }
}
