use std::fmt;

macro_rules! id {
    ($t: ty, $size: literal: $($name: ident)*) => {
        $(
            #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
            pub struct $name($t);
            #[allow(unused)]
            impl $name {
                pub fn new(id: $t) -> Self {
                    Self(id)
                }

                pub fn idx(self) -> usize { self.0 as usize }

                pub fn to_bytes(self) -> [u8; $size] {
                    self.0.to_le_bytes()
                }

                pub fn from_bytes(b: [u8; $size]) -> Self {
                    Self(<$t>::from_le_bytes(b))
                }
            }
        )*
    };
}
pub(crate) use id;


pub fn write_delimited<W: std::fmt::Write, I, T, D>(f: &mut W, i: I, delim: D) -> fmt::Result
where
    I: IntoIterator<Item = T>,
    T: fmt::Display,
    D: fmt::Display
{
    let mut i = i.into_iter();
    i.next().map(|first| write!(f, "{first}")).transpose()?;
    for elem in i {
        write!(f, "{delim}{elem}")?;
    }
    Ok(())
}

pub fn write_delimited_with<W: std::fmt::Write, I, T, F, D>(f: &mut W, i: I, write_func: F, delim: D) -> fmt::Result
where
    I: IntoIterator<Item = T>,
    F: Fn(&mut W, T) -> fmt::Result,
    D: fmt::Display
{
    let mut i = i.into_iter();
    i.next().map(|t| write_func(f, t)).transpose()?;
    for elem in i {
        write!(f, "{delim}")?;
        write_func(f, elem)?;
    }
    Ok(())
}
