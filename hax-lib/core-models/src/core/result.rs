pub enum Result<T, E> {
    Ok(T),
    Err(E),
}

use super::ops::function::*;
use Result::*;

#[hax_lib::attributes]
impl<T, E> Result<T, E> {
    #[hax_lib::requires(self.is_ok())]
    pub fn unwrap(self) -> T {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }
    #[hax_lib::requires(self.is_ok())]
    pub fn expect(self, _msg: &str) -> T {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }
    pub fn map<U, F>(self, op: F) -> Result<U, E>
    where
        F: FnOnce<T, Output = U>,
    {
        match self {
            Ok(t) => Ok(op.call_once(t)),
            Err(e) => Err(e),
        }
    }
    pub fn map_or<U, F>(self, default: U, f: F) -> U
    where
        F: FnOnce<T, Output = U>,
    {
        match self {
            Ok(t) => f.call_once(t),
            Err(e) => default,
        }
    }
    pub fn map_or_else<U, D, F>(self, default: D, f: F) -> U
    where
        F: FnOnce<T, Output = U>,
        D: FnOnce<E, Output = U>,
    {
        match self {
            Ok(t) => f.call_once(t),
            Err(e) => default.call_once(e),
        }
    }
    pub fn map_err<O, F>(self, op: O) -> Result<T, F>
    where
        O: FnOnce<E, Output = F>,
    {
        match self {
            Ok(t) => Ok(t),
            Err(e) => Err(op.call_once(e)),
        }
    }

    pub fn is_ok(&self) -> bool {
        matches!(*self, Ok(_))
    }
    pub fn and_then<U, F>(self, op: F) -> Result<U, E>
    where
        F: FnOnce<T, Output = Result<U, E>>,
    {
        match self {
            Ok(t) => op.call_once(t),
            Err(e) => Err(e),
        }
    }
}
