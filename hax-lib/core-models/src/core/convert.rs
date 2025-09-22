use super::result::Result;

trait TryInto<T> {
    type Error;
    fn try_into(self) -> Result<T, Self::Error>;
}

trait Into<T> {
    fn into(self) -> T;
}

trait From<T> {
    fn from(x: T) -> Self;
}

trait TryFrom<T>: Sized {
    type Error;
    fn try_from(x: T) -> Result<Self, Self::Error>;
}

// TODO add impls for integer types and for Infallible

impl<T, U: From<T>> Into<U> for T {
    fn into(self) -> U {
        U::from(self)
    }
}

pub struct Infallible;

impl<T, U: From<T>> TryFrom<T> for U {
    type Error = Infallible;
    fn try_from(x: T) -> Result<Self, Self::Error> {
        Result::Ok(U::from(x))
    }
}

impl<T, U: TryFrom<T>> TryInto<U> for T {
    type Error = U::Error;
    fn try_into(self) -> Result<U, Self::Error> {
        U::try_from(self)
    }
}

impl<T> From<T> for T {
    fn from(x: T) -> Self {
        x
    }
}

trait AsRef<T> {
    fn as_ref(self) -> T;
}

impl<T> AsRef<T> for T {
    fn as_ref(self) -> T {
        self
    }
}
