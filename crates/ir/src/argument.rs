use crate::{
    BlockId, BlockTarget, Environment, FunctionId, FunctionIr, GlobalId, Instruction, MCReg,
    Parameter, Ref, TypeId,
};

#[derive(Debug, Clone, Copy)]
pub enum Argument<'a> {
    Ref(Ref),
    BlockTarget(BlockTarget<'a>),
    Int(u64),
    Float(f64),
    TypeId(TypeId),
    FunctionId(FunctionId),
    GlobalId(GlobalId),
    MCReg(MCReg),
}
impl Argument<'_> {
    pub fn parameter_ty(&self) -> Parameter {
        match self {
            Argument::Ref(_) => Parameter::Ref,
            Argument::BlockTarget(_) => Parameter::BlockTarget,
            Argument::Int(_) => Parameter::Int,
            Argument::Float(_) => Parameter::Float,
            Argument::TypeId(_) => Parameter::TypeId,
            Argument::FunctionId(_) => Parameter::FunctionId,
            Argument::GlobalId(_) => Parameter::GlobalId,
            Argument::MCReg(_) => Parameter::MCReg(crate::Usage::Def), // TODO: setting def here ok?
        }
    }
}
impl From<Ref> for Argument<'_> {
    fn from(value: Ref) -> Self {
        Self::Ref(value)
    }
}
impl TryFrom<Argument<'_>> for Ref {
    type Error = ArgError;
    fn try_from(value: Argument) -> Result<Self, Self::Error> {
        let Argument::Ref(value) = value else {
            return Err(ArgError {
                expected: Parameter::Ref,
                found: value.parameter_ty(),
            });
        };
        Ok(value)
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
impl<'a> TryFrom<Argument<'a>> for BlockTarget<'a> {
    type Error = ArgError;
    fn try_from(value: Argument<'a>) -> Result<Self, Self::Error> {
        let Argument::BlockTarget(value) = value else {
            return Err(ArgError {
                expected: Parameter::BlockTarget,
                found: value.parameter_ty(),
            });
        };
        Ok(value)
    }
}
impl From<u64> for Argument<'_> {
    fn from(value: u64) -> Self {
        Self::Int(value)
    }
}
impl TryFrom<Argument<'_>> for u64 {
    type Error = ArgError;
    fn try_from(value: Argument) -> Result<Self, Self::Error> {
        let Argument::Int(value) = value else {
            return Err(ArgError {
                expected: Parameter::Int,
                found: value.parameter_ty(),
            });
        };
        Ok(value)
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
impl TryFrom<Argument<'_>> for f64 {
    type Error = ArgError;
    fn try_from(value: Argument) -> Result<Self, Self::Error> {
        let Argument::Float(value) = value else {
            return Err(ArgError {
                expected: Parameter::Float,
                found: value.parameter_ty(),
            });
        };
        Ok(value)
    }
}
impl From<TypeId> for Argument<'_> {
    fn from(value: TypeId) -> Self {
        Self::TypeId(value)
    }
}
impl TryFrom<Argument<'_>> for TypeId {
    type Error = ArgError;
    fn try_from(value: Argument) -> Result<Self, Self::Error> {
        let Argument::TypeId(value) = value else {
            return Err(ArgError {
                expected: Parameter::TypeId,
                found: value.parameter_ty(),
            });
        };
        Ok(value)
    }
}
impl From<FunctionId> for Argument<'_> {
    fn from(value: FunctionId) -> Self {
        Self::FunctionId(value)
    }
}
impl TryFrom<Argument<'_>> for FunctionId {
    type Error = ArgError;
    fn try_from(value: Argument) -> Result<Self, Self::Error> {
        let Argument::FunctionId(value) = value else {
            return Err(ArgError {
                expected: Parameter::FunctionId,
                found: value.parameter_ty(),
            });
        };
        Ok(value)
    }
}
impl From<GlobalId> for Argument<'_> {
    fn from(value: GlobalId) -> Self {
        Self::GlobalId(value)
    }
}
impl From<MCReg> for Argument<'_> {
    fn from(value: MCReg) -> Self {
        Self::MCReg(value)
    }
}
impl TryFrom<Argument<'_>> for GlobalId {
    type Error = ArgError;
    fn try_from(value: Argument) -> Result<Self, Self::Error> {
        let Argument::GlobalId(value) = value else {
            return Err(ArgError {
                expected: Parameter::GlobalId,
                found: value.parameter_ty(),
            });
        };
        Ok(value)
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

#[derive(Debug, Clone, Copy)]
pub enum ArgsError {
    CountMismatch { expected: usize, found: usize },
    InvalidType { index: usize, error: ArgError },
}

#[derive(Debug, Clone, Copy)]
pub struct ArgError {
    pub expected: Parameter,
    pub found: Parameter,
}

pub trait Args<'a>: Sized {
    fn get(
        ir: &'a FunctionIr,
        inst: &'a Instruction,
        env: &'a Environment,
    ) -> Result<Self, ArgsError>;
}

macro_rules! count {
    () => {
        0
    };
    ($t: ident $($rest: ident)*) => {
       1 + count!($($rest)*)
    };
}
macro_rules! args_impl {
    ($($t: ident)*) => {
        #[allow(unused_parens, unused_assignments)]
        impl<'a, $($t),*> Args<'a> for ($($t),*)
        where
        $(
            $t: TryFrom<Argument<'a>, Error = ArgError>,
        )*
        {
            fn get(
                ir: &'a FunctionIr,
                inst: &'a Instruction,
                env: &'a Environment,
            ) -> Result<Self, ArgsError> {
                let mut it = ir.args_iter(inst, env);
                let expected_count = count!($($t)*);
                let mut found_so_far = 0;
                let value = (
                    $(
                        {
                            let arg: $t = it
                                .next()
                                .ok_or(ArgsError::CountMismatch {
                                    expected: expected_count,
                                    found: found_so_far,
                                })
                                ?
                                .try_into()
                                .map_err(|error| ArgsError::InvalidType { index: 0, error })?;
                            found_so_far += 1;
                            arg
                        }
                    ),*
                );
                let remaining_count = it.count();
                if remaining_count > 0 {
                    return Err(ArgsError::CountMismatch {
                        expected: 1,
                        found: expected_count + remaining_count,
                    });
                }
                Ok(value)
            }
        }
    };
}
args_impl!(A);
args_impl!(A B);
args_impl!(A B C);
args_impl!(A B C D);
args_impl!(A B C D E);
args_impl!(A B C D E F);
