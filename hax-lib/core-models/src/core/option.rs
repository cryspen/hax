/// See [`std::option::Option`]
#[cfg_attr(test, derive(PartialEq))]
pub enum Option<T> {
    /// See [`std::option::Option::Some`]
    Some(T),
    /// See [`std::option::Option::None`]
    None,
}

use self::Option::*;
use super::default::Default;
use super::ops::function::*;
use super::result::Result::*;
use super::result::*;

#[hax_lib::attributes]
impl<T> Option<T> {
    /// See [`std::option::Option::is_some`]
    #[hax_lib::ensures(|res| hax_lib::Prop::implies(res.into(), fstar!("Option_Some? self")))]
    pub fn is_some(&self) -> bool {
        matches!(*self, Some(_))
    }

    /// See [`std::option::Option::is_some_and`]
    pub fn is_some_and<F: FnOnce<T, Output = bool>>(self, f: F) -> bool {
        match self {
            None => false,
            Some(x) => f.call_once(x),
        }
    }

    /// See [`std::option::Option::is_none`]
    pub fn is_none(&self) -> bool {
        self.is_some() == false
    }

    /// See [`std::option::Option::is_none_or`]
    pub fn is_none_or<F: FnOnce<T, Output = bool>>(self, f: F) -> bool {
        match self {
            None => true,
            Some(x) => f.call_once(x),
        }
    }

    /// See [`std::option::Option::as_ref`]
    pub const fn as_ref(&self) -> Option<&T> {
        match *self {
            Some(ref x) => Some(x),
            None => None,
        }
    }

    /// See [`std::option::Option::expect`]
    #[hax_lib::requires(self.is_some())]
    pub fn expect(self, _msg: &str) -> T {
        match self {
            Some(val) => val,
            None => super::panicking::internal::panic(),
        }
    }

    /// See [`std::option::Option::unwrap`]
    #[hax_lib::requires(self.is_some())]
    pub fn unwrap(self) -> T {
        match self {
            Some(val) => val,
            None => super::panicking::internal::panic(),
        }
    }

    /// See [`std::option::Option::unwrap_or`]
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Some(x) => x,
            None => default,
        }
    }

    /// See [`std::option::Option::unwrap_or_else`]
    pub fn unwrap_or_else<F: FnOnce<(), Output = T>>(self, f: F) -> T {
        match self {
            Some(x) => x,
            None => f.call_once(()),
        }
    }

    /// See [`std::option::Option::unwrap_or_default`]
    pub fn unwrap_or_default(self) -> T
    where
        T: Default,
    {
        match self {
            Some(x) => x,
            None => T::default(),
        }
    }

    /// See [`std::option::Option::map`]
    pub fn map<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce<T, Output = U>,
    {
        match self {
            Some(x) => Some(f.call_once(x)),
            None => None,
        }
    }

    /// See [`std::option::Option::map_or`]
    pub fn map_or<U, F>(self, default: U, f: F) -> U
    where
        F: FnOnce<T, Output = U>,
    {
        match self {
            Some(t) => f.call_once(t),
            None => default,
        }
    }

    /// See [`std::option::Option::map_or_else`]
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

    /// See [`std::option::Option::map_or_default`]
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

    /// See [`std::option::Option::ok_or`]
    pub fn ok_or<E>(self, err: E) -> Result<T, E> {
        match self {
            Some(v) => Ok(v),
            None => Err(err),
        }
    }

    /// See [`std::option::Option::ok_or_else`]
    pub fn ok_or_else<E, F: FnOnce<(), Output = E>>(self, err: F) -> Result<T, E> {
        match self {
            Some(v) => Ok(v),
            None => Err(err.call_once(())),
        }
    }

    /// See [`std::option::Option::and_then`]
    pub fn and_then<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce<T, Output = Option<U>>,
    {
        match self {
            Some(x) => f.call_once(x),
            None => None,
        }
    }

    /// See [`std::option::Option::take`]
    ///
    /// Note: The interface in Rust is wrong, but is good after extraction.
    /// We cannot make a useful model with the right interface so we lose the executability.
    pub fn take(self) -> (Option<T>, Option<T>) {
        (None, self)
    }
}

#[cfg(test)]
mod tests {
    use crate::testing::Inject;

    impl<T: Inject> Inject for Option<T> {
        type Model = super::Option<T::Model>;
        fn inject(&self) -> Self::Model {
            match self {
                Some(v) => super::Option::Some(v.inject()),
                None => super::Option::None,
            }
        }
    }

    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_is_some(x in any::<Option<u8>>()) {
            prop_assert!(x.clone().inject().is_some() == x.is_some());
        }

        #[test]
        fn test_is_some_and(x in any::<Option<u8>>(), threshold in any::<u8>()) {
            let f = |v: u8| v > threshold;
            prop_assert!(x.clone().inject().is_some_and(f) == x.is_some_and(f));
        }

        #[test]
        fn test_is_none(x in any::<Option<u8>>()) {
            prop_assert!(x.clone().inject().is_none() == x.is_none());
        }

        #[test]
        fn test_is_none_or(x in any::<Option<u8>>(), threshold in any::<u8>()) {
            let f = |v: u8| v > threshold;
            prop_assert!(x.clone().inject().is_none_or(f) == x.is_none_or(f));
        }

        #[test]
        fn test_as_ref(x in any::<Option<u8>>()) {
            prop_assert!(x.clone().inject().as_ref().map(|v: &u8| *v) == x.as_ref().inject());
        }

        #[test]
        fn test_expect(x in any::<u8>()) {
            // Only test Some case since expect requires is_some()
            let opt = Some(x);
            prop_assert!(opt.clone().inject().expect("msg") == opt.expect("msg"));
        }

        #[test]
        fn test_unwrap(x in any::<u8>()) {
            // Only test Some case since unwrap requires is_some()
            let opt = Some(x);
            prop_assert!(opt.clone().inject().unwrap() == opt.unwrap());
        }

        #[test]
        fn test_unwrap_or(x in any::<Option<u8>>(), default in any::<u8>()) {
            prop_assert!(x.clone().inject().unwrap_or(default) == x.unwrap_or(default));
        }

        #[test]
        fn test_unwrap_or_else(x in any::<Option<u8>>(), default in any::<u8>()) {
            let f = |()| default;
            let f_std = || default;
            prop_assert!(x.clone().inject().unwrap_or_else(f) == x.unwrap_or_else(f_std));
        }

        #[test]
        fn test_unwrap_or_default(x in any::<Option<u8>>()) {
            prop_assert!(x.clone().inject().unwrap_or_default() == x.unwrap_or_default());
        }

        #[test]
        fn test_map(x in any::<Option<u8>>(), a in any::<[u8; 256]>()) {
            let f = |x: u8| a[x as usize];
            prop_assert!(x.clone().inject().map(f) == x.map(f).inject());
        }

        #[test]
        fn test_map_or(x in any::<Option<u8>>(), default in any::<u8>(), a in any::<[u8; 256]>()) {
            let f = |v: u8| a[v as usize];
            prop_assert!(x.clone().inject().map_or(default, f) == x.map_or(default, f));
        }

        #[test]
        fn test_map_or_else(x in any::<Option<u8>>(), default in any::<u8>(), a in any::<[u8; 256]>()) {
            let f = |v: u8| a[v as usize];
            let d = |()| default;
            let d_std = || default;
            prop_assert!(x.clone().inject().map_or_else(d, f) == x.map_or_else(d_std, f));
        }

        #[test]
        fn test_map_or_default(x in any::<Option<u8>>(), a in any::<[u8; 256]>()) {
            let f = |v: u8| a[v as usize];
            // map_or_default is unstable in std, so compare with equivalent behavior
            prop_assert!(x.clone().inject().map_or_default(f) == x.map(f).unwrap_or_default());
        }

        #[test]
        fn test_ok_or(x in any::<Option<u8>>(), err in any::<u8>()) {
            prop_assert!(x.clone().inject().ok_or(err) == x.ok_or(err).inject());
        }

        #[test]
        fn test_ok_or_else(x in any::<Option<u8>>(), err in any::<u8>()) {
            let f = |()| err;
            let f_std = || err;
            prop_assert!(x.clone().inject().ok_or_else(f) == x.ok_or_else(f_std).inject());
        }

        #[test]
        fn test_and_then(x in any::<Option<u8>>(), threshold in any::<u8>()) {
            let f_model = |v: u8| if v > threshold { super::Option::Some(v) } else { super::Option::None };
            let f_std = |v: u8| if v > threshold { Some(v) } else { None };
            prop_assert!(x.clone().inject().and_then(f_model) == x.and_then(f_std).inject());
        }

        #[test]
        fn test_take(x in any::<Option<u8>>()) {
            // std::option::Option::take takes &mut self and returns Option<T>,
            // leaving None in place. Our model returns (remaining, taken).
            let mut std_opt = x.clone();
            let taken_std = std_opt.take();
            let remaining_std = std_opt;

            let (remaining_model, taken_model) = x.inject().take();

            prop_assert!(remaining_model == remaining_std.inject());
            prop_assert!(taken_model == taken_std.inject());
        }
    }
}
