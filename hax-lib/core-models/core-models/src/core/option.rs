/// See [`std::option::Option`]
#[cfg_attr(test, derive(PartialEq, Debug))]
pub enum Option<T> {
    /// See [`std::option::Option::Some`]
    Some(T),
    /// See [`std::option::Option::None`]
    None,
}

use self::Option::*;
use super::default::Default;
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
    pub fn is_some_and<F: FnOnce(T) -> bool>(self, f: F) -> bool {
        match self {
            None => false,
            Some(x) => f(x),
        }
    }

    /// See [`std::option::Option::is_none`]
    pub fn is_none(&self) -> bool {
        self.is_some() == false
    }

    /// See [`std::option::Option::is_none_or`]
    pub fn is_none_or<F: FnOnce(T) -> bool>(self, f: F) -> bool {
        match self {
            None => true,
            Some(x) => f(x),
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
    pub fn unwrap_or_else<F: FnOnce() -> T>(self, f: F) -> T {
        match self {
            Some(x) => x,
            None => f(),
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
        F: FnOnce(T) -> U,
    {
        match self {
            Some(x) => Some(f(x)),
            None => None,
        }
    }

    /// See [`std::option::Option::map_or`]
    pub fn map_or<U, F>(self, default: U, f: F) -> U
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Some(t) => f(t),
            None => default,
        }
    }

    /// See [`std::option::Option::map_or_else`]
    pub fn map_or_else<U, D, F>(self, default: D, f: F) -> U
    where
        F: FnOnce(T) -> U,
        D: FnOnce() -> U,
    {
        match self {
            Some(t) => f(t),
            None => default(),
        }
    }

    /// See [`std::option::Option::map_or_default`]
    pub fn map_or_default<U, F>(self, f: F) -> U
    where
        F: FnOnce(T) -> U,
        U: Default,
    {
        match self {
            Some(t) => f(t),
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
    pub fn ok_or_else<E, F: FnOnce() -> E>(self, err: F) -> Result<T, E> {
        match self {
            Some(v) => Ok(v),
            None => Err(err()),
        }
    }

    /// See [`std::option::Option::and_then`]
    pub fn and_then<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce(T) -> Option<U>,
    {
        match self {
            Some(x) => f(x),
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

    /// See [`std::option::Option::filter`]
    // opaque: F* cannot prove that the Fn output projection equals bool in an if-condition
    #[hax_lib::opaque]
    pub fn filter<P: FnOnce(&T) -> bool>(self, predicate: P) -> Option<T> {
        match self {
            Some(x) => {
                if predicate(&x) {
                    Some(x)
                } else {
                    None
                }
            }
            None => None,
        }
    }

    /// See [`std::option::Option::or`]
    pub fn or(self, optb: Option<T>) -> Option<T> {
        match self {
            Some(x) => Some(x),
            None => optb,
        }
    }

    /// See [`std::option::Option::or_else`]
    pub fn or_else<F: FnOnce() -> Option<T>>(self, f: F) -> Option<T> {
        match self {
            Some(x) => Some(x),
            None => f(),
        }
    }

    /// See [`std::option::Option::xor`]
    pub fn xor(self, optb: Option<T>) -> Option<T> {
        match (self, optb) {
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            _ => None,
        }
    }

    /// See [`std::option::Option::zip`]
    pub fn zip<U>(self, other: Option<U>) -> Option<(T, U)> {
        match (self, other) {
            (Some(a), Some(b)) => Some((a, b)),
            _ => None,
        }
    }

    /// See [`std::option::Option::inspect`]
    pub fn inspect<F: FnOnce(&T)>(self, f: F) -> Option<T> {
        if let Some(ref x) = self {
            f(x);
        }
        self
    }
}

#[hax_lib::attributes]
impl<T> Option<Option<T>> {
    /// See [`std::option::Option::flatten`]
    pub fn flatten(self) -> Option<T> {
        match self {
            Some(inner) => inner,
            None => None,
        }
    }
}

#[hax_lib::attributes]
impl<T> Default for Option<T> {
    /// See [`std::default::Default`]
    fn default() -> Option<T> {
        None
    }
}

#[cfg(not(hax_backend_fstar))]
#[hax_lib::attributes]
impl<T: super::clone::Clone> super::clone::Clone for Option<T> {
    fn clone(self) -> Self {
        match self {
            Self::Some(arg0) => Self::Some(arg0.clone()),
            Self::None => Self::None,
        }
    }
}

#[hax_lib::attributes]
impl<T: super::cmp::PartialEq<T>> super::cmp::PartialEq<Option<T>> for Option<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Some(a), Self::Some(b)) => a.eq(b),
            (Self::None, Self::None) => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::testing::Inject;
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
            let f = || default;
            prop_assert!(x.clone().inject().unwrap_or_else(f) == x.unwrap_or_else(f));
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
            let d = || default;
            prop_assert!(x.clone().inject().map_or_else(d, f) == x.map_or_else(d, f));
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
            let f = || err;
            prop_assert!(x.clone().inject().ok_or_else(f) == x.ok_or_else(f).inject());
        }

        #[test]
        fn test_and_then(x in any::<Option<u8>>(), threshold in any::<u8>()) {
            let f_model = |v: u8| if v > threshold { super::Option::Some(v) } else { super::Option::None };
            let f_std = |v: u8| if v > threshold { Some(v) } else { None };
            prop_assert!(x.clone().inject().and_then(f_model) == x.and_then(f_std).inject());
        }

        #[test]
        fn test_filter(x in any::<Option<u8>>(), threshold in any::<u8>()) {
            let f = |v: &u8| *v > threshold;
            prop_assert!(x.clone().inject().filter(f) == x.filter(f).inject());
        }

        #[test]
        fn test_or(x in any::<Option<u8>>(), y in any::<Option<u8>>()) {
            prop_assert!(x.clone().inject().or(y.clone().inject()) == x.or(y).inject());
        }

        #[test]
        fn test_or_else(x in any::<Option<u8>>(), default in any::<u8>()) {
            let f_model = || super::Option::Some(default);
            let f_std = || Some(default);
            prop_assert!(x.clone().inject().or_else(f_model) == x.or_else(f_std).inject());
        }

        #[test]
        fn test_xor(x in any::<Option<u8>>(), y in any::<Option<u8>>()) {
            prop_assert!(x.clone().inject().xor(y.clone().inject()) == x.xor(y).inject());
        }

        #[test]
        fn test_zip(x in any::<Option<u8>>(), y in any::<Option<u8>>()) {
            let model_result = x.clone().inject().zip(y.clone().inject());
            let std_result = x.zip(y);
            prop_assert!(model_result == std_result.inject());
        }

        #[test]
        fn test_flatten(x in any::<Option<Option<u8>>>()) {
            prop_assert!(x.inject().flatten() == x.flatten().inject());
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

        #[test]
        fn test_option_eq(x in any::<Option<u8>>(), y in any::<Option<u8>>()) {
            prop_assert_eq!(
                <super::Option<u8> as crate::cmp::PartialEq<super::Option<u8>>>::eq(
                    &x.inject(), &y.inject()
                ),
                x == y
            );
        }

        #[test]
        fn test_option_clone(x in any::<Option<u8>>()) {
            // `core_models`' `Clone::clone` takes `self` by value.
            prop_assert_eq!(
                <super::Option<u8> as crate::clone::Clone>::clone(x.inject()),
                x.clone().inject()
            );
        }
    }

    #[test]
    fn test_option_default() {
        use crate::testing::Inject;
        let model: super::Option<u8> = <super::Option<u8> as crate::default::Default>::default();
        let std_default: Option<u8> = Default::default();
        assert_eq!(model, std_default.inject());
    }
}
