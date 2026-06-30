/// See [`std::result::Result`]
#[cfg_attr(test, derive(PartialEq, Debug))]
pub enum Result<T, E> {
    /// See [`std::result::Result::Ok`]
    Ok(T),
    /// See [`std::result::Result::Err`]
    Err(E),
}

use self::Result::*;
use super::clone::Clone;
use super::default::Default;
use super::option::Option;

#[hax_lib::attributes]
#[cfg_attr(charon, aeneas::exclude)]
impl<T, E> Result<T, E> {
    /// See [`std::result::Result::is_ok`]
    pub fn is_ok(&self) -> bool {
        matches!(*self, Ok(_))
    }

    /// See [`std::result::Result::is_ok_and`]
    pub fn is_ok_and<F: FnOnce(T) -> bool>(self, f: F) -> bool {
        match self {
            Ok(t) => f(t),
            Err(_) => false,
        }
    }

    /// See [`std::result::Result::is_err`]
    pub fn is_err(&self) -> bool {
        !self.is_ok()
    }

    /// See [`std::result::Result::is_err_and`]
    pub fn is_err_and<F: FnOnce(E) -> bool>(self, f: F) -> bool {
        match self {
            Ok(_) => false,
            Err(e) => f(e),
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
    #[hax_lib::exclude]
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
    pub fn unwrap_or_else<F: FnOnce(E) -> T>(self, op: F) -> T {
        match self {
            Ok(t) => t,
            Err(e) => op(e),
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
        F: FnOnce(T) -> U,
    {
        match self {
            Ok(t) => Ok(op(t)),
            Err(e) => Err(e),
        }
    }

    /// See [`std::result::Result::map_or`]
    pub fn map_or<U, F>(self, default: U, f: F) -> U
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Ok(t) => f(t),
            Err(_) => default,
        }
    }

    /// See [`std::result::Result::map_or_else`]
    pub fn map_or_else<U, D, F>(self, default: D, f: F) -> U
    where
        F: FnOnce(T) -> U,
        D: FnOnce(E) -> U,
    {
        match self {
            Ok(t) => f(t),
            Err(e) => default(e),
        }
    }

    /// See [`std::result::Result::map_or_default`]
    pub fn map_or_default<U, F>(self, f: F) -> U
    where
        F: FnOnce(T) -> U,
        U: Default,
    {
        match self {
            Ok(t) => f(t),
            Err(_) => U::default(),
        }
    }

    /// See [`std::result::Result::map_err`]
    pub fn map_err<F, O>(self, op: O) -> Result<T, F>
    where
        O: FnOnce(E) -> F,
    {
        match self {
            Ok(t) => Ok(t),
            Err(e) => Err(op(e)),
        }
    }

    /// See [`std::result::Result::inspect`]
    pub fn inspect<F: FnOnce(&T)>(self, f: F) -> Result<T, E> {
        if let Ok(ref t) = self {
            f(t);
        }
        self
    }

    /// See [`std::result::Result::inspect_err`]
    pub fn inspect_err<F: FnOnce(&E)>(self, f: F) -> Result<T, E> {
        if let Err(ref e) = self {
            f(e);
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
        F: FnOnce(T) -> Result<U, E>,
    {
        match self {
            Ok(t) => op(t),
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
    pub fn or_else<F, O: FnOnce(E) -> Result<T, F>>(self, op: O) -> Result<T, F> {
        match self {
            Ok(t) => Ok(t),
            Err(e) => op(e),
        }
    }
}

#[hax_lib::attributes]
#[cfg_attr(charon, aeneas::exclude)]
impl<T: Clone, E> Result<T, E> {
    /// See [`std::result::Result::cloned`]
    pub fn cloned(self) -> Result<T, E> {
        match self {
            Ok(t) => Ok(t.clone()),
            Err(e) => Err(e),
        }
    }
}

#[hax_lib::attributes]
#[cfg_attr(charon, aeneas::exclude)]
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

#[hax_lib::attributes]
#[cfg_attr(charon, aeneas::exclude)]
impl<T, E> Result<Result<T, E>, E> {
    /// See [`std::result::Result::flatten`]
    pub fn flatten(self) -> Result<T, E> {
        match self {
            Ok(inner) => inner,
            Err(e) => Err(e),
        }
    }
}

/// Models the std impl `FromIterator<Result<A, E>> for Result<V, E>`: collect
/// an iterator of `Result`s into a `Result` of a collection, short-circuiting
/// on the first `Err`.
///
/// Opaque: our `FromIterator::from_iter` signature deliberately omits the
/// `Item = ...` bound (to avoid the associated-type constraint), so the
/// short-circuiting body cannot be written in terms of the iterator's items;
/// the behaviour is axiomatised. The body below exists only to typecheck —
/// it delegates to `V`'s own `from_iter`.
#[hax_lib::opaque]
impl<A, E, V: crate::iter::traits::collect::FromIterator<A>>
    crate::iter::traits::collect::FromIterator<Result<A, E>> for Result<V, E>
{
    fn from_iter<T: crate::iter::traits::collect::IntoIterator>(iter: T) -> Result<V, E> {
        Ok(<V as crate::iter::traits::collect::FromIterator<A>>::from_iter(iter))
    }
}

impl<T, E> crate::ops::try_trait::Try for Result<T, E> {
    type Output = T;
    type Residual = Result<crate::convert::Infallible, E>;

    #[inline]
    fn from_output(output: Self::Output) -> Self {
        Ok(output)
    }

    #[inline]
    fn branch(self) -> crate::ops::control_flow::ControlFlow<Self::Residual, Self::Output> {
        match self {
            Ok(v) => crate::ops::control_flow::ControlFlow::Continue(v),
            Err(e) => crate::ops::control_flow::ControlFlow::Break(Err(e)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::testing::Inject;
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
            prop_assert!(x.clone().inject().as_ref() == x.as_ref().inject().as_ref())
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
        fn test_transpose(x in any::<Result<Option<u8>, u8>>()) {
            prop_assert!(x.inject().transpose() == x.transpose().inject());
        }

        #[test]
        fn test_flatten(x in any::<Result<Result<u8, u8>, u8>>(), is_ok in any::<bool>()) {
            prop_assert!(x.inject().flatten() == x.flatten().inject());
        }

        // ----- Try (from_output / branch) -----------------------------------
        // std's `Try` is unstable, so these pin the model's documented
        // semantics (which mirror `?`): `from_output` injects into `Ok`,
        // `branch` sends `Ok(v)` to `Continue(v)` and `Err(e)` to `Break(Err(e))`.

        #[test]
        fn test_try_from_output(v in any::<u8>()) {
            use crate::ops::try_trait::Try;
            prop_assert_eq!(
                <super::Result<u8, u8> as Try>::from_output(v),
                super::Result::Ok(v)
            );
        }

        #[test]
        fn test_try_branch_ok(v in any::<u8>()) {
            use crate::ops::try_trait::Try;
            use crate::ops::control_flow::ControlFlow;
            let r: super::Result<u8, u8> = super::Result::Ok(v);
            match r.branch() {
                ControlFlow::Continue(c) => prop_assert_eq!(c, v),
                ControlFlow::Break(_) => prop_assert!(false, "Ok should Continue"),
            }
        }

        #[test]
        fn test_try_branch_err(e in any::<u8>()) {
            use crate::ops::try_trait::Try;
            use crate::ops::control_flow::ControlFlow;
            let r: super::Result<u8, u8> = super::Result::Err(e);
            match r.branch() {
                // `Break` carries the residual `Result<Infallible, u8>`; match
                // the `Err` arm to read the error without needing `Infallible: Eq`.
                ControlFlow::Break(super::Result::Err(ee)) => prop_assert_eq!(ee, e),
                _ => prop_assert!(false, "Err should Break(Err(e))"),
            }
        }
    }
}
