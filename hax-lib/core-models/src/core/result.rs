/// See [`std::result::Result`]
#[cfg_attr(test, derive(PartialEq))]
pub enum Result<T, E> {
    /// See [`std::result::Result::Ok`]
    Ok(T),
    /// See [`std::result::Result::Err`]
    Err(E),
}

use self::Result::*;
use super::clone::Clone;
use super::default::Default;
use super::ops::function::*;
use super::option::Option;

#[hax_lib::attributes]
impl<T, E> Result<T, E> {
    /// See [`std::result::Result::is_ok`]
    pub fn is_ok(&self) -> bool {
        matches!(*self, Ok(_))
    }

    /// See [`std::result::Result::is_ok_and`]
    pub fn is_ok_and<F: FnOnce<T, Output = bool>>(self, f: F) -> bool {
        match self {
            Ok(t) => f.call_once(t),
            Err(_) => false,
        }
    }

    /// See [`std::result::Result::is_err`]
    pub fn is_err(&self) -> bool {
        !self.is_ok()
    }

    /// See [`std::result::Result::is_err_and`]
    pub fn is_err_and<F: FnOnce<E, Output = bool>>(self, f: F) -> bool {
        match self {
            Ok(_) => false,
            Err(e) => f.call_once(e),
        }
    }

    /// See [`std::result::Result::as_ref`]
    pub const fn as_ref(&self) -> Result<&T, &E> {
        match *self {
            Ok(ref t) => Ok(t),
            Err(ref e) => Err(e),
        }
    }

    /// See [`std::result::Result::as_mut`]
    pub fn as_mut(&mut self) -> Result<&mut T, &mut E> {
        match *self {
            Ok(ref mut t) => Ok(t),
            Err(ref mut e) => Err(e),
        }
    }

    /// See [`std::result::Result::expect`]
    #[hax_lib::requires(self.is_ok())]
    pub fn expect(self, _msg: &str) -> T {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }

    /// See [`std::result::Result::unwrap`]
    #[hax_lib::requires(self.is_ok())]
    pub fn unwrap(self) -> T {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }

    /// See [`std::result::Result::expect_err`]
    #[hax_lib::requires(self.is_err())]
    pub fn expect_err(self, _msg: &str) -> E {
        match self {
            Ok(_) => super::panicking::internal::panic(),
            Err(e) => e,
        }
    }

    /// See [`std::result::Result::unwrap_err`]
    #[hax_lib::requires(self.is_err())]
    pub fn unwrap_err(self) -> E {
        match self {
            Ok(_) => super::panicking::internal::panic(),
            Err(e) => e,
        }
    }

    /// See [`std::result::Result::unwrap_or`]
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Ok(t) => t,
            Err(_) => default,
        }
    }

    /// See [`std::result::Result::unwrap_or_else`]
    pub fn unwrap_or_else<F: FnOnce<E, Output = T>>(self, op: F) -> T {
        match self {
            Ok(t) => t,
            Err(e) => op.call_once(e),
        }
    }

    /// See [`std::result::Result::unwrap_or_default`]
    pub fn unwrap_or_default(self) -> T
    where
        T: Default,
    {
        match self {
            Ok(t) => t,
            Err(_) => T::default(),
        }
    }

    /// See [`std::result::Result::map`]
    pub fn map<U, F>(self, op: F) -> Result<U, E>
    where
        F: FnOnce<T, Output = U>,
    {
        match self {
            Ok(t) => Ok(op.call_once(t)),
            Err(e) => Err(e),
        }
    }

    /// See [`std::result::Result::map_or`]
    pub fn map_or<U, F>(self, default: U, f: F) -> U
    where
        F: FnOnce<T, Output = U>,
    {
        match self {
            Ok(t) => f.call_once(t),
            Err(_) => default,
        }
    }

    /// See [`std::result::Result::map_or_else`]
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

    /// See [`std::result::Result::map_or_default`]
    pub fn map_or_default<U, F>(self, f: F) -> U
    where
        F: FnOnce<T, Output = U>,
        U: Default,
    {
        match self {
            Ok(t) => f.call_once(t),
            Err(_) => U::default(),
        }
    }

    /// See [`std::result::Result::map_err`]
    pub fn map_err<F, O>(self, op: O) -> Result<T, F>
    where
        O: FnOnce<E, Output = F>,
    {
        match self {
            Ok(t) => Ok(t),
            Err(e) => Err(op.call_once(e)),
        }
    }

    /// See [`std::result::Result::inspect`]
    pub fn inspect<F: for<'a> FnOnce<&'a T, Output = ()>>(self, f: F) -> Result<T, E> {
        if let Ok(ref t) = self {
            f.call_once(t);
        }
        self
    }

    /// See [`std::result::Result::inspect_err`]
    pub fn inspect_err<F: for<'a> FnOnce<&'a E, Output = ()>>(self, f: F) -> Result<T, E> {
        if let Err(ref e) = self {
            f.call_once(e);
        }
        self
    }

    /// See [`std::result::Result::ok`]
    pub fn ok(self) -> Option<T> {
        match self {
            Ok(x) => Option::Some(x),
            Err(_) => Option::None,
        }
    }

    /// See [`std::result::Result::err`]
    pub fn err(self) -> Option<E> {
        match self {
            Ok(_) => Option::None,
            Err(e) => Option::Some(e),
        }
    }

    /// See [`std::result::Result::and`]
    pub fn and<U>(self, res: Result<U, E>) -> Result<U, E> {
        match self {
            Ok(_) => res,
            Err(e) => Err(e),
        }
    }

    /// See [`std::result::Result::and_then`]
    pub fn and_then<U, F>(self, op: F) -> Result<U, E>
    where
        F: FnOnce<T, Output = Result<U, E>>,
    {
        match self {
            Ok(t) => op.call_once(t),
            Err(e) => Err(e),
        }
    }

    /// See [`std::result::Result::or`]
    pub fn or<F>(self, res: Result<T, F>) -> Result<T, F> {
        match self {
            Ok(t) => Ok(t),
            Err(_) => res,
        }
    }

    /// See [`std::result::Result::or_else`]
    pub fn or_else<F, O: FnOnce<E, Output = Result<T, F>>>(self, op: O) -> Result<T, F> {
        match self {
            Ok(t) => Ok(t),
            Err(e) => op.call_once(e),
        }
    }
}

impl<T: Clone, E> Result<T, E> {
    /// See [`std::result::Result::cloned`]
    pub fn cloned(self) -> Result<T, E> {
        match self {
            Ok(t) => Ok(t.clone()),
            Err(e) => Err(e),
        }
    }
}

impl<T, E> Result<Option<T>, E> {
    /// See [`std::result::Result::transpose`]
    pub fn transpose(self) -> Option<Result<T, E>> {
        match self {
            Ok(Option::Some(t)) => Option::Some(Ok(t)),
            Ok(Option::None) => Option::None,
            Err(e) => Option::Some(Err(e)),
        }
    }
}

impl<T, E> Result<Result<T, E>, E> {
    /// See [`std::result::Result::flatten`]
    pub fn flatten(self) -> Result<T, E> {
        match self {
            Ok(inner) => inner,
            Err(e) => Err(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::testing::Inject;

    impl<T: Inject, E: Inject> Inject for Result<T, E> {
        type Model = super::Result<T::Model, E::Model>;
        fn inject(self) -> Self::Model {
            match self {
                Ok(v) => super::Result::Ok(v.inject()),
                Err(e) => super::Result::Err(e.inject()),
            }
        }
    }

    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_is_ok(x in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().is_ok() == x.is_ok());
        }

        #[test]
        fn test_is_ok_and(x in any::<Result<u8, u8>>(), threshold in any::<u8>()) {
            let f = |v: u8| v > threshold;
            prop_assert!(x.clone().inject().is_ok_and(f) == x.is_ok_and(f));
        }

        #[test]
        fn test_is_err(x in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().is_err() == x.is_err());
        }

        #[test]
        fn test_is_err_and(x in any::<Result<u8, u8>>(), threshold in any::<u8>()) {
            let f = |e: u8| e > threshold;
            prop_assert!(x.clone().inject().is_err_and(f) == x.is_err_and(f));
        }

        #[test]
        fn test_as_ref(x in any::<Result<u8, u8>>()) {
            // Test that as_ref preserves the structure and allows access to the value
            let model = x.clone().inject();
            let model_ref = model.as_ref();
            match (&x, model_ref) {
                (Ok(v), super::Result::Ok(mv)) => prop_assert!(*v == *mv),
                (Err(e), super::Result::Err(me)) => prop_assert!(*e == *me),
                _ => prop_assert!(false, "as_ref changed variant"),
            }
        }

        #[test]
        fn test_expect(v in any::<u8>()) {
            // Only test Ok case since expect requires is_ok()
            let res: Result<u8, u8> = Ok(v);
            prop_assert!(res.clone().inject().expect("msg") == res.expect("msg"));
        }

        #[test]
        fn test_unwrap(v in any::<u8>()) {
            // Only test Ok case since unwrap requires is_ok()
            let res: Result<u8, u8> = Ok(v);
            prop_assert!(res.clone().inject().unwrap() == res.unwrap());
        }

        #[test]
        fn test_expect_err(e in any::<u8>()) {
            // Only test Err case since expect_err requires is_err()
            let res: Result<u8, u8> = Err(e);
            prop_assert!(res.clone().inject().expect_err("msg") == res.expect_err("msg"));
        }

        #[test]
        fn test_unwrap_err(e in any::<u8>()) {
            // Only test Err case since unwrap_err requires is_err()
            let res: Result<u8, u8> = Err(e);
            prop_assert!(res.clone().inject().unwrap_err() == res.unwrap_err());
        }

        #[test]
        fn test_unwrap_or(x in any::<Result<u8, u8>>(), default in any::<u8>()) {
            prop_assert!(x.clone().inject().unwrap_or(default) == x.unwrap_or(default));
        }

        #[test]
        fn test_unwrap_or_else(x in any::<Result<u8, u8>>(), a in any::<[u8; 256]>()) {
            let f = |e: u8| a[e as usize];
            prop_assert!(x.clone().inject().unwrap_or_else(f) == x.unwrap_or_else(f));
        }

        #[test]
        fn test_unwrap_or_default(x in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().unwrap_or_default() == x.unwrap_or_default());
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
        fn test_map_or_default(x in any::<Result<u8, u8>>(), a in any::<[u8; 256]>()) {
            let f = |v: u8| a[v as usize];
            // map_or_default is unstable in std, so compare with equivalent behavior
            prop_assert!(x.clone().inject().map_or_default(f) == x.map(f).unwrap_or_default());
        }

        #[test]
        fn test_map_err(x in any::<Result<u8, u8>>(), a in any::<[u8; 256]>()) {
            let f = |e: u8| a[e as usize];
            prop_assert!(x.clone().inject().map_err(f) == x.map_err(f).inject());
        }

        #[test]
        fn test_ok(x in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().ok() == x.ok().inject());
        }

        #[test]
        fn test_err(x in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().err() == x.err().inject());
        }

        #[test]
        fn test_and(x in any::<Result<u8, u8>>(), y in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().and(y.clone().inject()) == x.and(y).inject());
        }

        #[test]
        fn test_and_then(x in any::<Result<u8, u8>>(), threshold in any::<u8>()) {
            let f_model = |v: u8| if v > threshold { super::Result::Ok(v) } else { super::Result::Err(v) };
            let f_std = |v: u8| if v > threshold { Ok(v) } else { Err(v) };
            prop_assert!(x.clone().inject().and_then(f_model) == x.and_then(f_std).inject());
        }

        #[test]
        fn test_or(x in any::<Result<u8, u8>>(), y in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().or(y.clone().inject()) == x.or(y).inject());
        }

        #[test]
        fn test_or_else(x in any::<Result<u8, u8>>(), a in any::<[u8; 256]>()) {
            let f_model = |e: u8| super::Result::Ok::<u8, u8>(a[e as usize]);
            let f_std = |e: u8| Ok::<u8, u8>(a[e as usize]);
            prop_assert!(x.clone().inject().or_else(f_model) == x.or_else(f_std).inject());
        }

        #[test]
        fn test_cloned(x in any::<Result<u8, u8>>()) {
            // In our model, clone is identity, so cloned should be equivalent to identity
            prop_assert!(x.clone().inject().cloned() == x.clone().inject());
        }

        #[test]
        fn test_transpose(inner in any::<Option<u8>>(), err in any::<u8>(), is_ok in any::<bool>()) {
            let x: Result<Option<u8>, u8> = if is_ok { Ok(inner) } else { Err(err) };
            let model_x: super::Result<crate::option::Option<u8>, u8> = if is_ok {
                super::Result::Ok(inner.inject())
            } else {
                super::Result::Err(err)
            };
            prop_assert!(model_x.transpose() == x.transpose().inject());
        }

        #[test]
        fn test_flatten(inner in any::<Result<u8, u8>>(), err in any::<u8>(), is_ok in any::<bool>()) {
            let x: Result<Result<u8, u8>, u8> = if is_ok { Ok(inner.clone()) } else { Err(err) };
            let model_x: super::Result<super::Result<u8, u8>, u8> = if is_ok {
                super::Result::Ok(inner.inject())
            } else {
                super::Result::Err(err)
            };
            prop_assert!(model_x.flatten() == x.flatten().inject());
        }
    }
}
