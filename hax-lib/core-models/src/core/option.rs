pub enum Option<T> {
    Some(T),
    None,
}

#[hax_lib::fstar::before("open Rust_primitives.Integers")]
struct Dummy;

use super::default::Default;
use super::ops::function::*;
use super::result::Result::*;
use super::result::*;
use Option::*;

#[hax_lib::attributes]
impl<T> Option<T> {
    #[hax_lib::ensures(|res| hax_lib::Prop::implies(res.into(), fstar!("Option_Some? self")))]
    pub fn is_some(&self) -> bool {
        matches!(*self, Some(_))
    }

    pub fn is_some_and<F: FnOnce<T, Output = bool>>(self, f: F) -> bool {
        match self {
            None => false,
            Some(x) => f.call_once(x),
        }
    }

    pub fn is_none(&self) -> bool {
        self.is_some() == false
    }

    pub fn is_none_or<F: FnOnce<T, Output = bool>>(self, f: F) -> bool {
        match self {
            None => true,
            Some(x) => f.call_once(x),
        }
    }
    pub const fn as_ref(&self) -> Option<&T> {
        match *self {
            Some(ref x) => Some(x),
            None => None,
        }
    }

    #[hax_lib::requires(self.is_some())]
    pub fn expect(self, _msg: &str) -> T {
        match self {
            Some(val) => val,
            None => super::panicking::internal::panic(),
        }
    }

    #[hax_lib::requires(self.is_some())]
    pub fn unwrap(self) -> T {
        match self {
            Some(val) => val,
            None => super::panicking::internal::panic(),
        }
    }

    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Some(x) => x,
            None => default,
        }
    }

    pub fn unwrap_or_else<F: FnOnce<(), Output = T>>(self, f: F) -> T {
        match self {
            Some(x) => x,
            None => f.call_once(()),
        }
    }

    pub fn unwrap_or_default(self) -> T
    where
        T: Default,
    {
        match self {
            Some(x) => x,
            None => T::default(),
        }
    }

    pub fn map<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce<T, Output = U>,
    {
        match self {
            Some(x) => Some(f.call_once(x)),
            None => None,
        }
    }

    pub fn map_or<U, F>(self, default: U, f: F) -> U
    where
        F: FnOnce<T, Output = U>,
    {
        match self {
            Some(t) => f.call_once(t),
            None => default,
        }
    }

    pub fn map_or_else<U, D, F>(self, default: D, f: F) -> U
    where
        F: FnOnce<T, Output = U>,
        D: FnOnce<(), Output = U>,
    {
        match self {
            Some(t) => f.call_once(t),
            None => default.call_once(()),
        }
    }

    pub fn map_or_default<U, F>(self, f: F) -> U
    where
        F: FnOnce<T, Output = U>,
        U: Default,
    {
        match self {
            Some(t) => f.call_once(t),
            None => U::default(),
        }
    }
    pub fn ok_or<E>(self, err: E) -> Result<T, E> {
        match self {
            Some(v) => Ok(v),
            None => Err(err),
        }
    }

    pub fn ok_or_else<E, F: FnOnce<(), Output = E>>(self, err: F) -> Result<T, E> {
        match self {
            Some(v) => Ok(v),
            None => Err(err.call_once(())),
        }
    }

    pub fn and_then<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce<T, Output = Option<U>>,
    {
        match self {
            Some(x) => f.call_once(x),
            None => None,
        }
    }

    // The interface in Rust is wrong. but is good after extraction.
    // We cannot make a useful model with the right interface so we loose the executability.
    pub fn take(self) -> (Option<T>, Option<T>) {
        (None, self)
    }
}
