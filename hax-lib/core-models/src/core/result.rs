/// See <https://doc.rust-lang.org/std/result/enum.Result.html>
pub enum Result<T, E> {
    /// See <https://doc.rust-lang.org/std/result/enum.Result.html#variant.Ok>
    Ok(T),
    /// See <https://doc.rust-lang.org/std/result/enum.Result.html#variant.Err>
    Err(E),
}

use super::ops::function::*;
use super::option::Option;
use self::Result::*;

#[hax_lib::attributes]
impl<T, E> Result<T, E> {
    /// See <https://doc.rust-lang.org/std/result/enum.Result.html#method.unwrap>
    #[hax_lib::requires(self.is_ok())]
    pub fn unwrap(self) -> T {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Ok(t) => t,
            Err(_) => default,
        }
    }

    /// See <https://doc.rust-lang.org/std/result/enum.Result.html#method.expect>
    #[hax_lib::requires(self.is_ok())]
    pub fn expect(self, _msg: &str) -> T {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }

    /// See <https://doc.rust-lang.org/std/result/enum.Result.html#method.map>
    pub fn map<U, F>(self, op: F) -> Result<U, E>
    where
        F: FnOnce<T, Output = U>,
    {
        match self {
            Ok(t) => Ok(op.call_once(t)),
            Err(e) => Err(e),
        }
    }

    /// See <https://doc.rust-lang.org/std/result/enum.Result.html#method.map_or>
    pub fn map_or<U, F>(self, default: U, f: F) -> U
    where
        F: FnOnce<T, Output = U>,
    {
        match self {
            Ok(t) => f.call_once(t),
            Err(_e) => default,
        }
    }

    /// See <https://doc.rust-lang.org/std/result/enum.Result.html#method.map_or_else>
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

    /// See <https://doc.rust-lang.org/std/result/enum.Result.html#method.map_err>
    pub fn map_err<F, O>(self, op: O) -> Result<T, F>
    where
        O: FnOnce<E, Output = F>,
    {
        match self {
            Ok(t) => Ok(t),
            Err(e) => Err(op.call_once(e)),
        }
    }

    /// See <https://doc.rust-lang.org/std/result/enum.Result.html#method.is_ok>
    pub fn is_ok(&self) -> bool {
        matches!(*self, Ok(_))
    }

    /// See <https://doc.rust-lang.org/std/result/enum.Result.html#method.and_then>
    pub fn and_then<U, F>(self, op: F) -> Result<U, E>
    where
        F: FnOnce<T, Output = Result<U, E>>,
    {
        match self {
            Ok(t) => op.call_once(t),
            Err(e) => Err(e),
        }
    }

    /// See <https://doc.rust-lang.org/std/result/enum.Result.html#method.ok>
    pub fn ok(self) -> Option<T> {
        match self {
            Ok(x) => Option::Some(x),
            Err(_) => Option::None,
        }
    }
}

#[cfg(test)]
mod tests {
    // Note: Inject impls for std Result/Option -> model Result/Option
    // and PartialEq for model Result are defined in option.rs tests
    use crate::testing::Inject;

    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_is_ok(x in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().is_ok() == x.is_ok());
        }

        #[test]
        fn test_unwrap(v in any::<u8>()) {
            // Only test Ok case since unwrap requires is_ok()
            let res: Result<u8, u8> = Ok(v);
            prop_assert!(res.clone().inject().unwrap() == res.unwrap());
        }

        #[test]
        fn test_expect(v in any::<u8>()) {
            // Only test Ok case since expect requires is_ok()
            let res: Result<u8, u8> = Ok(v);
            prop_assert!(res.clone().inject().expect("msg") == res.expect("msg"));
        }

        #[test]
        fn test_map(x in any::<Result<u8, u8>>(), a in any::<[u8; 256]>()) {
            let f = |v: u8| a[v as usize];
            prop_assert!(x.clone().inject().map(f) == x.map(f).inject());
        }

        #[test]
        fn test_map_or(x in any::<Result<u8, u8>>(), default in any::<u8>(), a in any::<[u8; 256]>()) {
            let f = |v: u8| a[v as usize];
            prop_assert!(x.clone().inject().map_or(default, f) == x.map_or(default, f));
        }

        #[test]
        fn test_map_or_else(x in any::<Result<u8, u8>>(), a in any::<[u8; 256]>(), b in any::<[u8; 256]>()) {
            let f = |v: u8| a[v as usize];
            let d = |e: u8| b[e as usize];
            prop_assert!(x.clone().inject().map_or_else(d, f) == x.map_or_else(d, f));
        }

        #[test]
        fn test_map_err(x in any::<Result<u8, u8>>(), a in any::<[u8; 256]>()) {
            let f = |e: u8| a[e as usize];
            prop_assert!(x.clone().inject().map_err(f) == x.map_err(f).inject());
        }

        #[test]
        fn test_and_then(x in any::<Result<u8, u8>>(), threshold in any::<u8>()) {
            let f_model = |v: u8| if v > threshold { super::Result::Ok(v) } else { super::Result::Err(v) };
            let f_std = |v: u8| if v > threshold { Ok(v) } else { Err(v) };
            prop_assert!(x.clone().inject().and_then(f_model) == x.and_then(f_std).inject());
        }

        #[test]
        fn test_ok(x in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().ok() == x.ok().inject());
        }
    }
}
