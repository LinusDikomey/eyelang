use std::fmt;



pub fn write_delimited<I, T, D>(f: &mut fmt::Formatter, i: I, delim: D) -> fmt::Result
where
    I: IntoIterator<Item = T>,
    T: fmt::Display,
    D: fmt::Display
{
    let mut i =i.into_iter();
    i.next().map(|first| write!(f, "{first}")).transpose()?;
    for elem in i {
        write!(f, "{delim}{elem}")?;
    }
    Ok(())
}

pub fn write_delimited_with<I, T, F, D>(f: &mut fmt::Formatter, i: I, write_func: F, delim: D) -> fmt::Result
where
    I: IntoIterator<Item = T>,
    F: Fn(&mut fmt::Formatter, T) -> fmt::Result,
    D: fmt::Display
{
    let mut i =i.into_iter();
    i.next().map(|t| write_func(f, t)).transpose()?;
    for elem in i {
        write!(f, "{delim}")?;
        write_func(f, elem)?;
    }
    Ok(())
}