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
use rust_primitives::sequence::{Seq, seq_empty, seq_len, seq_one, seq_remove};

#[hax_lib::attributes]
impl<T, E> Result<T, E> {
    /// See [`std::result::Result::is_ok`]
    #[cfg_attr(charon, aeneas::exclude)]
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
    #[cfg_attr(charon, aeneas::exclude)]
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
    #[cfg_attr(charon, aeneas::exclude)]
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
    #[cfg(hax_backend_fstar)]
    #[hax_lib::requires(self.is_ok())]
    pub fn expect(self, _msg: &str) -> T {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }

    /// See [`std::result::Result::unwrap`]
    #[cfg(hax_backend_fstar)]
    #[hax_lib::requires(self.is_ok())]
    pub fn unwrap(self) -> T {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }

    /// See [`std::result::Result::expect_err`]
    #[cfg(hax_backend_fstar)]
    #[hax_lib::requires(self.is_err())]
    pub fn expect_err(self, _msg: &str) -> E {
        match self {
            Ok(_) => super::panicking::internal::panic(),
            Err(e) => e,
        }
    }

    /// See [`std::result::Result::unwrap_err`]
    #[cfg(hax_backend_fstar)]
    #[hax_lib::requires(self.is_err())]
    pub fn unwrap_err(self) -> E {
        match self {
            Ok(_) => super::panicking::internal::panic(),
            Err(e) => e,
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
        D: FnOnce(E) -> U,
        F: FnOnce(T) -> U,
    {
        match self {
            Ok(t) => f(t),
            Err(e) => default(e),
        }
    }

    /// See [`std::result::Result::map_or_default`]
    #[cfg_attr(charon, aeneas::exclude)]
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
    #[cfg_attr(charon, aeneas::exclude)]
    pub fn ok(self) -> Option<T> {
        match self {
            Ok(x) => Option::Some(x),
            Err(_) => Option::None,
        }
    }

    /// See [`std::result::Result::err`]
    #[cfg_attr(charon, aeneas::exclude)]
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

    /// See [`std::result::Result::unwrap_or`]
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Ok(t) => t,
            Err(_) => default,
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

    /// See [`std::result::Result::unwrap_unchecked`]
    ///
    /// Calling std's version on an `Err` is undefined behaviour; the `requires`
    /// rules that input out, and the model panics rather than inventing a value.
    // F*-only contract: the Lean pipeline now feeds `requires` to aeneas as a
    // spec, and aeneas crashes computing the name of this one — `Not_found` in
    // `NameMatcher.ty_to_pattern_aux` — for a `requires` on an `unsafe fn` in a
    // generic inherent impl. The model still panics on the bad input, so the
    // Lean side loses only the stated precondition, not the guard.
    #[cfg_attr(hax_backend_fstar, hax_lib::requires(self.is_ok()))]
    pub unsafe fn unwrap_unchecked(self) -> T {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }

    /// See [`std::result::Result::unwrap_err_unchecked`]
    ///
    /// See `unwrap_unchecked` for why the `Ok` arm panics.
    #[cfg_attr(hax_backend_fstar, hax_lib::requires(self.is_err()))]
    pub unsafe fn unwrap_err_unchecked(self) -> E {
        match self {
            Ok(_) => super::panicking::internal::panic(),
            Err(e) => e,
        }
    }

    /// See [`std::result::Result::iter`]
    pub fn iter(&self) -> Iter<'_, T> {
        match self {
            Ok(t) => Iter(seq_one(t)),
            Err(_) => Iter(seq_empty()),
        }
    }

    /// See [`std::result::Result::iter_mut`]
    // `&mut` returns are unsupported in the F* backend.
    #[hax_lib::exclude]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        match self {
            Ok(t) => IterMut(seq_one(t)),
            Err(_) => IterMut(seq_empty()),
        }
    }
}

/// aeneas/lean copies of the four methods whose std signature carries a `Debug`
/// bound: charon emits the dictionary, so the model must take it, but the F*
/// versions above must stay bound-free to keep their `impl__` names.
#[cfg(not(hax_backend_fstar))]
#[hax_lib::attributes]
impl<T, E> Result<T, E> {
    /// See [`std::result::Result::expect`]
    #[cfg_attr(not(charon), hax_lib::requires(self.is_ok()))]
    pub fn expect(self, _msg: &str) -> T
    where
        E: super::fmt::Debug,
    {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }

    /// See [`std::result::Result::unwrap`]
    #[cfg_attr(not(charon), hax_lib::requires(self.is_ok()))]
    pub fn unwrap(self) -> T
    where
        E: super::fmt::Debug,
    {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }

    /// See [`std::result::Result::expect_err`]
    #[cfg_attr(not(charon), hax_lib::requires(self.is_err()))]
    pub fn expect_err(self, _msg: &str) -> E
    where
        T: super::fmt::Debug,
    {
        match self {
            Ok(_) => super::panicking::internal::panic(),
            Err(e) => e,
        }
    }

    /// See [`std::result::Result::unwrap_err`]
    #[cfg_attr(not(charon), hax_lib::requires(self.is_err()))]
    pub fn unwrap_err(self) -> E
    where
        T: super::fmt::Debug,
    {
        match self {
            Ok(_) => super::panicking::internal::panic(),
            Err(e) => e,
        }
    }
}

// Anonymous lifetime for the reason given on `option::Option::cloned`.
#[hax_lib::attributes]
impl<T: Clone, E> Result<&'_ T, E> {
    /// See [`std::result::Result::cloned`]
    pub fn cloned(self) -> Result<T, E> {
        match self {
            Ok(t) => Ok(t.clone()),
            Err(e) => Err(e),
        }
    }
}

#[cfg(hax_backend_fstar)]
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
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
#[hax_lib::attributes]
impl<A, E, V: crate::iter::traits::collect::FromIterator<A>>
    crate::iter::traits::collect::FromIterator<Result<A, E>> for Result<V, E>
{
    fn from_iter<T: crate::iter::traits::collect::IntoIterator>(iter: T) -> Result<V, E> {
        Ok(<V as crate::iter::traits::collect::FromIterator<A>>::from_iter(iter))
    }
}

#[hax_lib::attributes]
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

#[cfg(not(hax_backend_fstar))]
#[hax_lib::attributes]
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

/// Mirrors the `Option` instance in `core/option.rs`. F* compares `Result`s with
/// its own structural equality, so this is only extracted for aeneas/lean.
#[cfg(not(hax_backend_fstar))]
#[hax_lib::attributes]
impl<T: super::cmp::PartialEq<T>, E: super::cmp::PartialEq<E>> super::cmp::PartialEq<Result<T, E>>
    for Result<T, E>
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Ok(a), Ok(b)) => a.eq(b),
            (Err(a), Err(b)) => a.eq(b),
            _ => false,
        }
    }
}

/// The error half of `?`: re-inject the `Err(e)` residual, widening the error
/// via `From` (mirrors std's `impl<T, E, F: From<E>> ... for Result<T, F>`). `Ok`
/// is unreachable — the residual's payload is `Infallible`.
// opaque for F*: can't prove the `Ok(_)` arm (`Infallible`) unreachable.
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
impl<T, E, F: crate::convert::From<E>>
    crate::ops::try_trait::FromResidual<Result<crate::convert::Infallible, E>> for Result<T, F>
{
    fn from_residual(residual: Result<crate::convert::Infallible, E>) -> Self {
        match residual {
            Err(e) => Err(<F as crate::convert::From<E>>::from(e)),
            Ok(_) => super::panicking::internal::panic(),
        }
    }
}

/// See [`std::result::Iter`]
///
/// A `Result`'s iterators yield at most one element; the payload is a `Seq` so
/// `next` can be written the same way as the slice/array iterators.
pub struct Iter<'a, T>(pub Seq<&'a T>);

#[hax_lib::attributes]
impl<'a, T> crate::iter::traits::iterator::Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        if seq_len(&self.0) == 0 {
            Option::None
        } else {
            Option::Some(seq_remove(&mut self.0, 0))
        }
    }
}

/// See [`std::result::IterMut`]
// `&mut` returns are unsupported in the F* backend.
#[cfg_attr(charon, aeneas::exclude)]
// F*-only: `charon::exclude` would drop this dummy type while its `impl`
// blocks still reference it (see f32.rs).
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub struct IterMut<'a, T>(pub Seq<&'a mut T>);

#[hax_lib::attributes]
#[hax_lib::exclude]
impl<'a, T> crate::iter::traits::iterator::Iterator for IterMut<'a, T> {
    type Item = &'a mut T;
    fn next(&mut self) -> Option<&'a mut T> {
        if seq_len(&self.0) == 0 {
            Option::None
        } else {
            Option::Some(seq_remove(&mut self.0, 0))
        }
    }
}

/// See [`std::result::IntoIter`]
pub struct IntoIter<T>(pub Seq<T>);

#[hax_lib::attributes]
impl<T> crate::iter::traits::iterator::Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if seq_len(&self.0) == 0 {
            Option::None
        } else {
            Option::Some(seq_remove(&mut self.0, 0))
        }
    }
}

#[hax_lib::attributes]
impl<T, E> crate::iter::traits::collect::IntoIterator for Result<T, E> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> IntoIter<T> {
        match self {
            Ok(t) => IntoIter(seq_one(t)),
            Err(_) => IntoIter(seq_empty()),
        }
    }
}

/// Std bounds `as_deref` by `T: Deref`. The model's only `Deref` instance is
/// `&T`, so the impl is specialised to `Result<&T, E>` — the same set of self
/// types, without needing the bound.
#[hax_lib::attributes]
#[cfg_attr(charon, aeneas::exclude)]
impl<'a, T, E> Result<&'a T, E> {
    /// See [`std::result::Result::as_deref`]
    pub fn as_deref(&self) -> Result<&T, &E> {
        match self {
            Ok(t) => Ok(*t),
            Err(e) => Err(e),
        }
    }
}

/// Std bounds `as_deref_mut` by `T: DerefMut`; see `as_deref` above for why the
/// model specialises the self type instead.
#[hax_lib::attributes]
#[cfg_attr(charon, aeneas::exclude)]
impl<'a, T, E> Result<&'a mut T, E> {
    /// See [`std::result::Result::as_deref_mut`]
    // `&mut` returns are unsupported in the F* backend.
    #[hax_lib::exclude]
    pub fn as_deref_mut(&mut self) -> Result<&mut T, &mut E> {
        match self {
            Ok(t) => Ok(&mut **t),
            Err(e) => Err(e),
        }
    }
}

/// `Copy` here is `core`'s, not the model's: reading `*t` out of a `&T` is a
/// language operation, which the model's `marker::Copy` cannot license.
#[hax_lib::attributes]
#[cfg_attr(charon, aeneas::exclude)]
impl<'a, T: Copy, E> Result<&'a T, E> {
    /// See [`std::result::Result::copied`]
    pub fn copied(self) -> Result<T, E> {
        match self {
            Ok(t) => Ok(*t),
            Err(e) => Err(e),
        }
    }
}

/// Std spells the never type in the bounds of `into_ok`/`into_err`
/// (`E: Into<!>`), which makes the impossible arm unreachable by typing. `!` is
/// unstable and the model's `convert::Infallible` is a unit struct — hence
/// inhabited — so the arm survives and needs the usual panic guard.
#[hax_lib::attributes]
#[cfg_attr(charon, aeneas::exclude)]
impl<T> Result<T, crate::convert::Infallible> {
    /// See [`std::result::Result::into_ok`]
    #[hax_lib::requires(self.is_ok())]
    pub fn into_ok(self) -> T {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }
}

/// See the note on `into_ok`.
#[hax_lib::attributes]
#[cfg_attr(charon, aeneas::exclude)]
impl<E> Result<crate::convert::Infallible, E> {
    /// See [`std::result::Result::into_err`]
    #[hax_lib::requires(self.is_err())]
    pub fn into_err(self) -> E {
        match self {
            Ok(_) => super::panicking::internal::panic(),
            Err(e) => e,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::iter::traits::iterator::Iterator as ModelIterator;
    use crate::option::Option as ModelOption;
    use crate::testing::Inject;
    use proptest::prelude::*;

    /// The `Result` iterators are lazy; draining them is what observes them.
    fn drain<I: ModelIterator>(mut it: I) -> Vec<I::Item> {
        let mut out = Vec::new();
        while let ModelOption::Some(x) = it.next() {
            out.push(x);
        }
        out
    }

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

        // std's `Result::cloned` is unstable, so the expectation is spelled out:
        // cloning the `&u8` in the `Ok` arm gives that `u8` back.
        #[test]
        fn test_cloned(x in any::<Result<u8, u8>>()) {
            let model: super::Result<&u8, u8> = match &x {
                Ok(t) => super::Result::Ok(t),
                Err(e) => super::Result::Err(*e),
            };
            prop_assert!(model.cloned() == x.inject());
        }

        #[test]
        fn test_transpose(x in any::<Result<Option<u8>, u8>>()) {
            prop_assert!(x.inject().transpose() == x.transpose().inject());
        }

        #[test]
        fn test_flatten(x in any::<Result<Result<u8, u8>, u8>>(), is_ok in any::<bool>()) {
            prop_assert!(x.inject().flatten() == x.flatten().inject());
        }

        // The model's `PartialEq for Result` is aeneas/lean-only.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_eq(x in any::<Result<u8, u8>>(), y in any::<Result<u8, u8>>()) {
            prop_assert_eq!(
                crate::cmp::PartialEq::eq(&x.clone().inject(), &y.clone().inject()),
                x == y
            );
        }

        // `x == x` exercises the equal-payload `(Ok, Ok)` / `(Err, Err)` arms;
        // two independent draws hit an equal `Err` pair about once in 512.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_eq_reflexive(x in any::<Result<u8, u8>>()) {
            prop_assert!(crate::cmp::PartialEq::eq(
                &x.clone().inject(),
                &x.clone().inject()
            ));
        }

        // ----- Try (from_output / branch) -----------------------------------
        // std's `Try` is unstable, so these pin the model's documented
        // semantics (which mirror `?`): `from_output` injects into `Ok`,
        // `branch` sends `Ok(v)` to `Continue(v)` and `Err(e)` to `Break(Err(e))`.

        // ----- unwrap_unchecked / unwrap_err_unchecked -----------------------
        // Only the in-domain half is exercised: std's versions are UB — not a
        // panic — on the other variant, so there is nothing to compare against.

        #[test]
        fn test_unwrap_unchecked(v in any::<u8>()) {
            let res: Result<u8, u8> = Ok(v);
            prop_assert_eq!(
                unsafe { res.clone().inject().unwrap_unchecked() },
                unsafe { res.unwrap_unchecked() }
            );
        }

        #[test]
        fn test_unwrap_err_unchecked(e in any::<u8>()) {
            let res: Result<u8, u8> = Err(e);
            prop_assert_eq!(
                unsafe { res.clone().inject().unwrap_err_unchecked() },
                unsafe { res.unwrap_err_unchecked() }
            );
        }

        // The out-of-domain halves have no std counterpart, so what is pinned is
        // that the model panics rather than returning nonsense.
        #[test]
        fn test_unwrap_unchecked_on_err_panics(e in any::<u8>()) {
            let res: super::Result<u8, u8> = super::Result::Err(e);
            let panicked = std::panic::catch_unwind(|| unsafe { res.unwrap_unchecked() }).is_err();
            prop_assert!(panicked);
        }

        #[test]
        fn test_unwrap_err_unchecked_on_ok_panics(v in any::<u8>()) {
            let res: super::Result<u8, u8> = super::Result::Ok(v);
            let panicked =
                std::panic::catch_unwind(|| unsafe { res.unwrap_err_unchecked() }).is_err();
            prop_assert!(panicked);
        }

        // ----- iter / iter_mut / into_iter ------------------------------------

        #[test]
        fn test_iter(x in any::<Result<u8, u8>>()) {
            let model = x.clone().inject();
            prop_assert_eq!(
                drain(model.iter()).into_iter().copied().collect::<Vec<u8>>(),
                x.iter().copied().collect::<Vec<u8>>()
            );
        }

        // Mutating through the yielded `&mut` is what distinguishes `iter_mut`.
        #[test]
        fn test_iter_mut(x in any::<Result<u8, u8>>()) {
            let mut model = x.clone().inject();
            for r in drain(model.iter_mut()) {
                *r = r.wrapping_add(1);
            }
            let mut std_res = x.clone();
            for r in std_res.iter_mut() {
                *r = r.wrapping_add(1);
            }
            prop_assert!(model == std_res.inject());
        }

        #[test]
        fn test_into_iter(x in any::<Result<u8, u8>>()) {
            use crate::iter::traits::collect::IntoIterator as ModelIntoIterator;
            let model = <super::Result<u8, u8> as ModelIntoIterator>::into_iter(x.clone().inject());
            prop_assert_eq!(drain(model), x.into_iter().collect::<Vec<u8>>());
        }

        // ----- as_deref / as_deref_mut / copied ------------------------------

        #[test]
        fn test_as_deref(x in any::<Result<u8, u8>>()) {
            let std_res: Result<&u8, u8> = match &x {
                Ok(v) => Ok(v),
                Err(e) => Err(*e),
            };
            let model: super::Result<&u8, u8> = match &x {
                Ok(v) => super::Result::Ok(v),
                Err(e) => super::Result::Err(*e),
            };
            prop_assert_eq!(
                model.as_deref().map(|v: &u8| *v).map_err(|e: &u8| *e),
                std_res.as_deref().map(|v| *v).map_err(|e| *e).inject()
            );
        }

        #[test]
        fn test_as_deref_mut(v in any::<u8>(), e in any::<u8>(), is_ok in any::<bool>()) {
            let mut std_target = v;
            let mut model_target = v;
            let mut std_res: Result<&mut u8, u8> =
                if is_ok { Ok(&mut std_target) } else { Err(e) };
            let mut model: super::Result<&mut u8, u8> = if is_ok {
                super::Result::Ok(&mut model_target)
            } else {
                super::Result::Err(e)
            };
            if let Ok(r) = std_res.as_deref_mut() {
                *r = r.wrapping_add(1);
            }
            if let super::Result::Ok(r) = model.as_deref_mut() {
                *r = r.wrapping_add(1);
            }
            drop(std_res);
            drop(model);
            prop_assert_eq!(model_target, std_target);
        }

        #[test]
        fn test_copied(x in any::<Result<u8, u8>>()) {
            let model: super::Result<&u8, u8> = match &x {
                Ok(v) => super::Result::Ok(v),
                Err(e) => super::Result::Err(*e),
            };
            // std's `Result::copied` is unstable; `as_ref().map(|v| *v)` is the
            // stable spelling of the same behaviour.
            prop_assert_eq!(
                model.copied(),
                x.as_ref().map(|v| *v).map_err(|e| *e).inject()
            );
        }

        // ----- into_ok / into_err --------------------------------------------
        // std bounds these by `E: Into<!>` / `T: Into<!>`; the never type is
        // unstable, so there is no callable std counterpart and the expected
        // behaviour is pinned directly.

        #[test]
        fn test_into_ok(v in any::<u8>()) {
            let res: super::Result<u8, crate::convert::Infallible> = super::Result::Ok(v);
            prop_assert_eq!(res.into_ok(), v);
        }

        #[test]
        fn test_into_err(e in any::<u8>()) {
            let res: super::Result<crate::convert::Infallible, u8> = super::Result::Err(e);
            prop_assert_eq!(res.into_err(), e);
        }

        // The model's `Infallible` is a unit struct, so unlike std's never type
        // the off-domain variant *is* constructible — and panics.
        #[test]
        fn test_into_ok_on_err_panics(_ignored in any::<u8>()) {
            let res: super::Result<u8, crate::convert::Infallible> =
                super::Result::Err(crate::convert::Infallible);
            let panicked = std::panic::catch_unwind(|| res.into_ok()).is_err();
            prop_assert!(panicked);
        }

        #[test]
        fn test_into_err_on_ok_panics(_ignored in any::<u8>()) {
            let res: super::Result<crate::convert::Infallible, u8> =
                super::Result::Ok(crate::convert::Infallible);
            let panicked = std::panic::catch_unwind(|| res.into_err()).is_err();
            prop_assert!(panicked);
        }

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

        #[test]
        fn test_as_mut(x in any::<Result<u8, u8>>()) {
            let mut model = x.clone().inject();
            let mut std_value = x.clone();
            match (model.as_mut(), std_value.as_mut()) {
                (super::Ok(m), Ok(s)) => { *m = 1; *s = 1; }
                (super::Err(m), Err(s)) => { *m = 2; *s = 2; }
                _ => prop_assert!(false, "as_mut changed the variant"),
            }
            prop_assert_eq!(model, std_value.inject());
        }

        #[test]
        fn test_inspect(x in any::<Result<u8, u8>>()) {
            let model_seen = std::cell::Cell::new(0u8);
            let model = x.clone().inject().inspect(|v: &u8| model_seen.set(*v));
            let std_seen = std::cell::Cell::new(0u8);
            let std_value = x.clone().inspect(|v: &u8| std_seen.set(*v));
            prop_assert_eq!(model_seen.get(), std_seen.get());
            prop_assert_eq!(model, std_value.inject());
        }

        #[test]
        fn test_inspect_err(x in any::<Result<u8, u8>>()) {
            let model_seen = std::cell::Cell::new(0u8);
            let model = x.clone().inject().inspect_err(|e: &u8| model_seen.set(*e));
            let std_seen = std::cell::Cell::new(0u8);
            let std_value = x.clone().inspect_err(|e: &u8| std_seen.set(*e));
            prop_assert_eq!(model_seen.get(), std_seen.get());
            prop_assert_eq!(model, std_value.inject());
        }

        // `?` on an `Err`: re-inject the residual, widening `u8` to `u16`.
        #[test]
        fn test_from_residual(e in any::<u8>()) {
            use crate::ops::try_trait::FromResidual;
            let residual: super::Result<crate::convert::Infallible, u8> = super::Err(e);
            let widened: super::Result<u8, u16> = FromResidual::from_residual(residual);
            prop_assert_eq!(widened, super::Err(e as u16));
        }
    }

    // The `Ok(_)` arm of `from_residual` is unreachable for a real residual (its
    // payload would have to be an `Infallible`), so it can only be run directly.
    #[test]
    #[should_panic]
    fn test_from_residual_ok_panics() {
        use crate::ops::try_trait::FromResidual;
        let residual: super::Result<crate::convert::Infallible, u8> =
            super::Ok(crate::convert::Infallible);
        let _: super::Result<u8, u16> = FromResidual::from_residual(residual);
    }

    #[test]
    fn test_unwrap_on_err_panics() {
        crate::testing::panics_like_core(
            || super::Result::<u8, u8>::Err(1).unwrap(),
            || Err::<u8, u8>(1).unwrap(),
        );
    }

    #[test]
    fn test_expect_on_err_panics() {
        crate::testing::panics_like_core(
            || super::Result::<u8, u8>::Err(1).expect("boom"),
            || Err::<u8, u8>(1).expect("boom"),
        );
    }

    #[test]
    fn test_unwrap_err_on_ok_panics() {
        crate::testing::panics_like_core(
            || super::Result::<u8, u8>::Ok(1).unwrap_err(),
            || Ok::<u8, u8>(1).unwrap_err(),
        );
    }

    #[test]
    fn test_expect_err_on_ok_panics() {
        crate::testing::panics_like_core(
            || super::Result::<u8, u8>::Ok(1).expect_err("boom"),
            || Ok::<u8, u8>(1).expect_err("boom"),
        );
    }
}
