pub trait IteratorExt: Iterator {
    fn try_any<F, E>(self, mut f: F) -> Result<bool, E>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> Result<bool, E>,
    {
        for item in self {
            if f(item)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn try_all<F, E>(self, mut f: F) -> Result<bool, E>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> Result<bool, E>,
    {
        for item in self {
            if !f(item)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

impl<I: Iterator> IteratorExt for I {}
