use crate::option::Option;
use rust_primitives::slice::array_pair;

/// See [`std::cmp::PartialEq`]
#[hax_lib::attributes]
pub trait PartialEq<Rhs>
where
    Rhs: ?Sized,
{
    /// See [`std::cmp::PartialEq::eq`]
    #[hax_lib::requires(true)]
    fn eq(&self, other: &Rhs) -> bool;

    /// See [`std::cmp::PartialEq::ne`]. Provided method: the aeneas Lean backend
    /// synthesises `#[derive(PartialEq)]` instances as `{ eq := …, ne := …PartialEq.ne.default … }`,
    /// so the model must carry `ne` or those instances fail with "`ne` is not a field of
    /// `core.cmp.PartialEq`". Modelled exactly like the `PartialOrd::{lt,le,gt,ge}` defaults
    /// below (cfg-guarded off F*; `== false` avoids negation for the F* lib).
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::requires(true)]
    fn ne(&self, other: &Rhs) -> bool {
        self.eq(other) == false
    }
}

/// See [`std::cmp::Eq`]
pub trait Eq: PartialEq<Self> {}

/// See [`std::cmp::Ordering`]
#[cfg_attr(test, derive(PartialEq, Debug))]
pub enum Ordering {
    /// See [`std::cmp::Ordering::Less`]
    Less = -1,
    /// See [`std::cmp::Ordering::Equal`]
    Equal = 0,
    /// See [`std::cmp::Ordering::Greater`]
    Greater = 1,
}

/// See [`std::cmp::PartialOrd`]
#[hax_lib::attributes]
pub trait PartialOrd<Rhs>: PartialEq<Rhs>
where
    Rhs: ?Sized,
{
    /// See [`std::cmp::PartialOrd::partial_cmp`]
    #[hax_lib::requires(true)]
    fn partial_cmp(&self, other: &Rhs) -> Option<Ordering>;

    // hax/F* does not support default methods. We work around that using the `PartialOrdDefaults`
    // trait below.
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::requires(true)]
    fn lt(&self, other: &Rhs) -> bool {
        matches!(self.partial_cmp(other), Option::Some(Ordering::Less))
    }
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::requires(true)]
    fn le(&self, other: &Rhs) -> bool {
        matches!(
            self.partial_cmp(other),
            Option::Some(Ordering::Less | Ordering::Equal)
        )
    }
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::requires(true)]
    fn gt(&self, other: &Rhs) -> bool {
        matches!(self.partial_cmp(other), Option::Some(Ordering::Greater))
    }
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::requires(true)]
    fn ge(&self, other: &Rhs) -> bool {
        matches!(
            self.partial_cmp(other),
            Option::Some(Ordering::Greater | Ordering::Equal)
        )
    }
}

#[hax_lib::attributes]
trait Neq<Rhs> {
    #[hax_lib::requires(true)]
    fn neq(&self, y: &Rhs) -> bool;
}

impl<T: PartialEq<T>> Neq<T> for T {
    fn neq(&self, y: &T) -> bool {
        // Not using negation is a workaround for the F* lib
        self.eq(y) == false
    }
}

// These methods in core are provided using trait defaults, but this is not supported by hax/F*
// so we have to define them in a different way.
#[cfg(any(hax_backend_fstar, test))]
#[hax_lib::attributes]
trait PartialOrdDefaults<Rhs> {
    #[hax_lib::requires(true)]
    fn lt(&self, y: &Rhs) -> bool
    where
        Self: PartialOrd<Rhs>;
    #[hax_lib::requires(true)]
    fn le(&self, y: &Rhs) -> bool
    where
        Self: PartialOrd<Rhs>;
    #[hax_lib::requires(true)]
    fn gt(&self, y: &Rhs) -> bool
    where
        Self: PartialOrd<Rhs>;
    #[hax_lib::requires(true)]
    fn ge(&self, y: &Rhs) -> bool
    where
        Self: PartialOrd<Rhs>;
}

#[cfg(any(hax_backend_fstar, test))]
impl<T: PartialOrd<T>> PartialOrdDefaults<T> for T {
    fn lt(&self, y: &T) -> bool
    where
        T: PartialOrd<T>,
    {
        matches!(self.partial_cmp(y), Option::Some(Ordering::Less))
    }
    fn le(&self, y: &T) -> bool
    where
        T: PartialOrd<T>,
    {
        matches!(
            self.partial_cmp(y),
            Option::Some(Ordering::Less | Ordering::Equal)
        )
    }
    fn gt(&self, y: &T) -> bool
    where
        T: PartialOrd<T>,
    {
        matches!(self.partial_cmp(y), Option::Some(Ordering::Greater))
    }
    fn ge(&self, y: &T) -> bool
    where
        T: PartialOrd<T>,
    {
        matches!(
            self.partial_cmp(y),
            Option::Some(Ordering::Greater | Ordering::Equal)
        )
    }
}

/// See [`std::cmp::Ord`]
#[hax_lib::attributes]
pub trait Ord: Eq + PartialOrd<Self> {
    /// See [`std::cmp::Ord::cmp`]
    #[hax_lib::requires(true)]
    fn cmp(&self, other: &Self) -> Ordering;
}

/// See [`std::cmp::max`]
pub fn max<T: Ord>(v1: T, v2: T) -> T {
    match v1.cmp(&v2) {
        Ordering::Greater => v1,
        _ => v2,
    }
}

/// See [`std::cmp::min`]
pub fn min<T: Ord>(v1: T, v2: T) -> T {
    match v1.cmp(&v2) {
        Ordering::Greater => v2,
        _ => v1,
    }
}

/// See [`std::cmp::Reverse`]
pub struct Reverse<T>(pub T);

impl<T: PartialOrd<T>> PartialOrd<Reverse<T>> for Reverse<T> {
    fn partial_cmp(&self, other: &Reverse<T>) -> Option<Ordering> {
        other.0.partial_cmp(&self.0)
    }
}

impl<T: PartialEq<T>> PartialEq<Reverse<T>> for Reverse<T> {
    #[cfg(not(hax_backend_fstar))]
    fn ne(&self, other: &Reverse<T>) -> bool {
        self.eq(other) == false
    }
    fn eq(&self, other: &Reverse<T>) -> bool {
        other.0.eq(&self.0)
    }
}

impl<T: Eq> Eq for Reverse<T> {}

impl<T: Ord> Ord for Reverse<T> {
    fn cmp(&self, other: &Reverse<T>) -> Ordering {
        other.0.cmp(&self.0)
    }
}

macro_rules! int_impls {
    ($($t:ty)*) => ($(
        #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
        #[hax_lib::attributes]
        #[cfg_attr(charon, hax_lib::exclude)]
        impl PartialOrd<$t> for $t {
            #[hax_lib::ensures(|res| {
                match res {
                    Option::Some(Ordering::Less) => self < other,
                    Option::Some(Ordering::Equal) => self == other,
                    Option::Some(Ordering::Greater) => self > other,
                    Option::None => false
                }
            })]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                if self < other {Option::Some(Ordering::Less)}
                else if self > other {Option::Some(Ordering::Greater)}
                else {Option::Some(Ordering::Equal)}
            }
        }
        #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
        #[hax_lib::attributes]
        #[cfg_attr(charon, hax_lib::exclude)]
        impl Ord for $t {
            #[hax_lib::ensures(|res| {
                match res {
                    Ordering::Less => self < other,
                    Ordering::Equal => self == other,
                    Ordering::Greater => self > other,
                }
            })]
            fn cmp(&self, other: &Self) -> Ordering {
                if self < other {Ordering::Less}
                else if self > other {Ordering::Greater}
                else {Ordering::Equal}
            }
        }
        #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
        #[cfg_attr(charon, hax_lib::exclude)]
        impl PartialEq<$t> for $t {
            fn eq(&self, other: &Self) -> bool {
                self == other
            }
        }
        #[cfg_attr(charon, hax_lib::exclude)]
        #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
        impl Eq for $t {}
    )*)
}

int_impls! { u8 i8 u16 i16 u32 i32 u64 i64 u128 i128 usize isize }

#[hax_lib::attributes]
impl Ordering {
    /// See [`std::cmp::Ordering::is_eq`]
    pub fn is_eq(self) -> bool {
        matches!(self, Ordering::Equal)
    }
    /// See [`std::cmp::Ordering::is_ne`]
    pub fn is_ne(self) -> bool {
        matches!(self, Ordering::Less | Ordering::Greater)
    }
    /// See [`std::cmp::Ordering::is_lt`]
    pub fn is_lt(self) -> bool {
        matches!(self, Ordering::Less)
    }
    /// See [`std::cmp::Ordering::is_gt`]
    pub fn is_gt(self) -> bool {
        matches!(self, Ordering::Greater)
    }
    /// See [`std::cmp::Ordering::is_le`]
    pub fn is_le(self) -> bool {
        matches!(self, Ordering::Less | Ordering::Equal)
    }
    /// See [`std::cmp::Ordering::is_ge`]
    pub fn is_ge(self) -> bool {
        matches!(self, Ordering::Greater | Ordering::Equal)
    }
    /// See [`std::cmp::Ordering::reverse`]
    pub fn reverse(self) -> Ordering {
        match self {
            Ordering::Less => Ordering::Greater,
            Ordering::Equal => Ordering::Equal,
            Ordering::Greater => Ordering::Less,
        }
    }
    /// See [`std::cmp::Ordering::then`]
    pub fn then(self, other: Ordering) -> Ordering {
        match self {
            Ordering::Equal => other,
            _ => self,
        }
    }
    /// See [`std::cmp::Ordering::then_with`]
    pub fn then_with<F: FnOnce() -> Ordering>(self, f: F) -> Ordering {
        match self {
            Ordering::Equal => f(),
            _ => self,
        }
    }
}

// `max_by`, `min_by` and `minmax_by` all ask `compare(&v2, &v1)`, like core: the
// answer decides in favour of `v1` for `min*` and of `v2` for `max*` on `Equal`.
// They also test the answer with `is_lt` rather than matching on it, again like
// core: the F* backend types a closure's result as its `FnOnce::Output`
// projection, which a pattern of type `Ordering` does not match.

/// See [`std::cmp::max_by`]
pub fn max_by<T, F: FnOnce(&T, &T) -> Ordering>(v1: T, v2: T, compare: F) -> T {
    if compare(&v2, &v1).is_lt() { v1 } else { v2 }
}

/// See [`std::cmp::min_by`]
pub fn min_by<T, F: FnOnce(&T, &T) -> Ordering>(v1: T, v2: T, compare: F) -> T {
    if compare(&v2, &v1).is_lt() { v2 } else { v1 }
}

// The key functions below are bounded by `Fn`, not std's `FnMut`: they call `f`
// twice, and `core::iter`'s model takes the same shortcut for the same reason.
//
// Each also has an F*-only twin taking a plain `fn` pointer, exactly like
// `array::map`: hax does not carry a `Fn`/`FnMut` bound's `Output` constraint into
// F*, so `f`'s result there is an unconstrained `FnOnce::Output` projection that
// `K`'s `Ord` instance cannot be applied to. The phantom `F` parameter keeps the
// generic list the same as core's.

/// See [`std::cmp::max_by_key`]
#[cfg(not(hax_backend_fstar))]
pub fn max_by_key<T, F, K>(v1: T, v2: T, f: F) -> T
where
    F: Fn(&T) -> K,
    K: Ord,
{
    if f(&v2).cmp(&f(&v1)).is_lt() { v1 } else { v2 }
}
#[cfg(hax_backend_fstar)]
pub fn max_by_key<T, F: crate::ops::function::FnOnce<T, Output = K>, K: Ord>(
    v1: T,
    v2: T,
    f: fn(&T) -> K,
) -> T {
    if f(&v2).cmp(&f(&v1)).is_lt() { v1 } else { v2 }
}

/// See [`std::cmp::min_by_key`]
#[cfg(not(hax_backend_fstar))]
pub fn min_by_key<T, F, K>(v1: T, v2: T, f: F) -> T
where
    F: Fn(&T) -> K,
    K: Ord,
{
    if f(&v2).cmp(&f(&v1)).is_lt() { v2 } else { v1 }
}
#[cfg(hax_backend_fstar)]
pub fn min_by_key<T, F: crate::ops::function::FnOnce<T, Output = K>, K: Ord>(
    v1: T,
    v2: T,
    f: fn(&T) -> K,
) -> T {
    if f(&v2).cmp(&f(&v1)).is_lt() { v2 } else { v1 }
}

/// See [`std::cmp::minmax`]
pub fn minmax<T: Ord>(v1: T, v2: T) -> [T; 2] {
    if v2.cmp(&v1).is_lt() {
        array_pair(v2, v1)
    } else {
        array_pair(v1, v2)
    }
}

/// See [`std::cmp::minmax_by`]
pub fn minmax_by<T, F: FnOnce(&T, &T) -> Ordering>(v1: T, v2: T, compare: F) -> [T; 2] {
    if compare(&v2, &v1).is_lt() {
        array_pair(v2, v1)
    } else {
        array_pair(v1, v2)
    }
}

/// See [`std::cmp::minmax_by_key`]
#[cfg(not(hax_backend_fstar))]
pub fn minmax_by_key<T, F, K>(v1: T, v2: T, f: F) -> [T; 2]
where
    F: Fn(&T) -> K,
    K: Ord,
{
    if f(&v2).cmp(&f(&v1)).is_lt() {
        array_pair(v2, v1)
    } else {
        array_pair(v1, v2)
    }
}
#[cfg(hax_backend_fstar)]
pub fn minmax_by_key<T, F: crate::ops::function::FnOnce<T, Output = K>, K: Ord>(
    v1: T,
    v2: T,
    f: fn(&T) -> K,
) -> [T; 2] {
    if f(&v2).cmp(&f(&v1)).is_lt() {
        array_pair(v2, v1)
    } else {
        array_pair(v1, v2)
    }
}

// `Ord::{max, min, clamp}` are trait defaults in core, which hax does not
// support, so they live in a companion trait like `Neq` and
// `PartialOrdDefaults` are. They sit here, after `impl Ordering`, so that
// `is_le` is not a forward reference for the aeneas backend.
//
// `not(hax_backend_fstar)`: the F* backend names trait impls by a global
// disambiguator (https://github.com/cryspen/hax/issues/828), so the extra
// blanket impl below renumbers every `impl_NN` in `Core_models.{Cmp,Convert}`,
// renaming published names for no gain there — F* keeps the free `max`/`min`/
// `clamp` functions.
#[cfg(not(hax_backend_fstar))]
#[hax_lib::attributes]
trait OrdDefaults {
    #[hax_lib::requires(true)]
    fn max(self, other: Self) -> Self
    where
        Self: Ord;
    #[hax_lib::requires(true)]
    fn min(self, other: Self) -> Self
    where
        Self: Ord;
    #[hax_lib::requires(min.cmp(&max).is_le())]
    fn clamp(self, min: Self, max: Self) -> Self
    where
        Self: Ord;
}

#[cfg(not(hax_backend_fstar))]
impl<T: Ord> OrdDefaults for T {
    // Both `max` and `min` compare `other` against `self`, like core, so that
    // `max` returns `other` and `min` returns `self` when the two are equal.
    fn max(self, other: T) -> T {
        match other.cmp(&self) {
            Ordering::Less => self,
            _ => other,
        }
    }
    fn min(self, other: T) -> T {
        match other.cmp(&self) {
            Ordering::Less => other,
            _ => self,
        }
    }
    fn clamp(self, min: T, max: T) -> T {
        if !min.cmp(&max).is_le() {
            crate::panicking::internal::panic()
        }
        match self.cmp(&min) {
            Ordering::Less => min,
            _ => match self.cmp(&max) {
                Ordering::Greater => max,
                _ => self,
            },
        }
    }
}

/// See [`std::cmp::clamp`]
#[hax_lib::requires(min.cmp(&max).is_le())]
pub fn clamp<T: Ord>(value: T, min: T, max: T) -> T {
    if !min.cmp(&max).is_le() {
        crate::panicking::internal::panic()
    }
    match value.cmp(&min) {
        Ordering::Less => min,
        Ordering::Equal => value,
        Ordering::Greater => match value.cmp(&max) {
            Ordering::Greater => max,
            _ => value,
        },
    }
}

#[cfg(test)]
mod tests {
    #[cfg(not(hax_backend_fstar))]
    use super::OrdDefaults;
    use super::{Ord, PartialEq, PartialOrd};
    use crate::testing::Inject;
    use proptest::prelude::*;

    /// A key/tag pair ordered on the key alone: two distinct values can compare
    /// `Equal`, which is what makes the `*_by*` tie-breaks (return `v1` or
    /// `v2`?) observable. `u8` alone cannot show them.
    type Tagged = (u8, u8);

    fn model_by(x: &Tagged, y: &Tagged) -> super::Ordering {
        <u8 as Ord>::cmp(&x.0, &y.0)
    }

    fn std_by(x: &Tagged, y: &Tagged) -> std::cmp::Ordering {
        std::cmp::Ord::cmp(&x.0, &y.0)
    }

    fn key(x: &Tagged) -> u8 {
        x.0
    }

    proptest! {
        // Ints don't override `ne`, so this exercises the trait's default.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_partial_eq_ne_default(x in 0u8..4, y in 0u8..4) {
            prop_assert_eq!(PartialEq::ne(&x.inject(), &y.inject()), x != y);
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_reverse_ne(x in 0u8..4, y in 0u8..4) {
            let a = std::cmp::Reverse(x);
            let b = std::cmp::Reverse(y);
            prop_assert_eq!(PartialEq::ne(&a.inject(), &b.inject()), a != b);
        }

        #[test]
        fn test_ordering_is_eq(x in any::<u8>(), y in any::<u8>()) {
            let model_ord = <u8 as Ord>::cmp(&x.inject(), &y.inject());
            let std_ord = std::cmp::Ord::cmp(&x, &y);
            prop_assert_eq!(model_ord.is_eq(), std_ord.is_eq());
        }

        #[test]
        fn test_ordering_is_ne(x in any::<u8>(), y in any::<u8>()) {
            let model_ord = <u8 as Ord>::cmp(&x.inject(), &y.inject());
            let std_ord = std::cmp::Ord::cmp(&x, &y);
            prop_assert_eq!(model_ord.is_ne(), std_ord.is_ne());
        }

        #[test]
        fn test_ordering_is_lt(x in any::<u8>(), y in any::<u8>()) {
            let model_ord = <u8 as Ord>::cmp(&x.inject(), &y.inject());
            let std_ord = std::cmp::Ord::cmp(&x, &y);
            prop_assert_eq!(model_ord.is_lt(), std_ord.is_lt());
        }

        #[test]
        fn test_ordering_is_gt(x in any::<u8>(), y in any::<u8>()) {
            let model_ord = <u8 as Ord>::cmp(&x.inject(), &y.inject());
            let std_ord = std::cmp::Ord::cmp(&x, &y);
            prop_assert_eq!(model_ord.is_gt(), std_ord.is_gt());
        }

        #[test]
        fn test_ordering_is_le(x in any::<u8>(), y in any::<u8>()) {
            let model_ord = <u8 as Ord>::cmp(&x.inject(), &y.inject());
            let std_ord = std::cmp::Ord::cmp(&x, &y);
            prop_assert_eq!(model_ord.is_le(), std_ord.is_le());
        }

        #[test]
        fn test_ordering_is_ge(x in any::<u8>(), y in any::<u8>()) {
            let model_ord = <u8 as Ord>::cmp(&x.inject(), &y.inject());
            let std_ord = std::cmp::Ord::cmp(&x, &y);
            prop_assert_eq!(model_ord.is_ge(), std_ord.is_ge());
        }

        #[test]
        fn test_ordering_reverse(x in any::<u8>(), y in any::<u8>()) {
            let model_ord = <u8 as Ord>::cmp(&x.inject(), &y.inject());
            let std_ord = std::cmp::Ord::cmp(&x, &y);
            prop_assert_eq!(model_ord.reverse(), std_ord.reverse().inject());
        }

        #[test]
        fn test_ordering_then(x in any::<u8>(), y in any::<u8>(), a in any::<u8>(), b in any::<u8>()) {
            let model_ord1 = <u8 as Ord>::cmp(&x.inject(), &y.inject());
            let model_ord2 = <u8 as Ord>::cmp(&a.inject(), &b.inject());
            let std_ord1 = std::cmp::Ord::cmp(&x, &y);
            let std_ord2 = std::cmp::Ord::cmp(&a, &b);
            prop_assert_eq!(model_ord1.then(model_ord2), std_ord1.then(std_ord2).inject());
        }

        // The `Equal` arms of `reverse`/`then`/`then_with`/`clamp` need both sides
        // of a comparison to agree, which a pair of independent draws never does.
        // Two independent draws are essentially never equal, so the `Equal` input
        // of each predicate needs a reflexive comparison. `Ordering` is not
        // `Copy`, hence the closure.
        #[test]
        fn test_ordering_predicates_on_equal(x in any::<u8>()) {
            let m = || <u8 as Ord>::cmp(&x.inject(), &x.inject());
            let s = std::cmp::Ord::cmp(&x, &x);
            prop_assert_eq!(m().is_eq(), s.is_eq());
            prop_assert_eq!(m().is_ne(), s.is_ne());
            prop_assert_eq!(m().is_lt(), s.is_lt());
            prop_assert_eq!(m().is_gt(), s.is_gt());
            prop_assert_eq!(m().is_le(), s.is_le());
            prop_assert_eq!(m().is_ge(), s.is_ge());
        }

        #[test]
        fn test_ordering_reverse_equal(x in any::<u8>()) {
            let model_ord = <u8 as Ord>::cmp(&x.inject(), &x.inject());
            let std_ord = std::cmp::Ord::cmp(&x, &x);
            prop_assert_eq!(model_ord.reverse(), std_ord.reverse().inject());
        }

        #[test]
        fn test_ordering_then_equal(x in any::<u8>(), a in any::<u8>(), b in any::<u8>()) {
            let model_ord2 = <u8 as Ord>::cmp(&a.inject(), &b.inject());
            let std_ord2 = std::cmp::Ord::cmp(&a, &b);
            prop_assert_eq!(
                <u8 as Ord>::cmp(&x.inject(), &x.inject()).then(model_ord2),
                std::cmp::Ord::cmp(&x, &x).then(std_ord2).inject()
            );
        }

        // One test, not one per arm: `then_with` is generic in the closure, so a
        // second test would be a second instantiation reaching only one arm.
        // `equal` decides whether the first ordering is `Equal`.
        #[test]
        fn test_ordering_then_with(
            x in any::<u8>(),
            y in any::<u8>(),
            equal in any::<bool>(),
            a in any::<u8>(),
            b in any::<u8>(),
        ) {
            let y = if equal { x } else { y };
            let model_ord2 = <u8 as Ord>::cmp(&a.inject(), &b.inject());
            let std_ord2 = std::cmp::Ord::cmp(&a, &b);
            prop_assert_eq!(
                <u8 as Ord>::cmp(&x.inject(), &y.inject()).then_with(|| model_ord2),
                std::cmp::Ord::cmp(&x, &y).then_with(|| std_ord2).inject()
            );
        }

        #[test]
        fn test_clamp_at_min(x in any::<u8>(), hi in any::<u8>()) {
            let hi = std::cmp::max(x, hi);
            prop_assert_eq!(
                super::clamp(x.inject(), x.inject(), hi.inject()),
                std::cmp::Ord::clamp(x, x, hi)
            );
        }

        #[test]
        fn test_clamp(x in any::<u8>(), a in any::<u8>(), b in any::<u8>()) {
            let lo = std::cmp::min(a, b);
            let hi = std::cmp::max(a, b);
            prop_assert_eq!(
                super::clamp(x.inject(), lo.inject(), hi.inject()),
                std::cmp::Ord::clamp(x, lo, hi)
            );
        }

        #[test]
        fn test_max(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(super::max(x.inject(), y.inject()).inject(), std::cmp::max(x, y));
        }

        #[test]
        fn test_min(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(super::min(x.inject(), y.inject()).inject(), std::cmp::min(x, y));
        }

        #[test]
        fn test_reverse_partial_cmp(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                super::Reverse(x.inject()).partial_cmp(&super::Reverse(y.inject())),
                std::cmp::Reverse(x).partial_cmp(&std::cmp::Reverse(y)).inject()
            );
        }

        #[test]
        fn test_reverse_inject(x in any::<u8>()) {
            prop_assert_eq!(std::cmp::Reverse(x).inject().0, x);
        }

        #[test]
        fn test_reverse_eq(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                super::Reverse(x.inject()).eq(&super::Reverse(y.inject())),
                std::cmp::Reverse(x).eq(&std::cmp::Reverse(y))
            );
        }

        #[test]
        fn test_reverse_cmp(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                super::Reverse(x.inject()).cmp(&super::Reverse(y.inject())),
                std::cmp::Reverse(x).cmp(&std::cmp::Reverse(y)).inject()
            );
        }

        #[test]
        fn test_int_partial_cmp(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                <u8 as PartialOrd<u8>>::partial_cmp(&x.inject(), &y.inject()),
                std::cmp::PartialOrd::partial_cmp(&x, &y).inject()
            );
        }

        #[test]
        fn test_int_cmp(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                <u8 as Ord>::cmp(&x.inject(), &y.inject()),
                std::cmp::Ord::cmp(&x, &y).inject()
            );
        }

        #[test]
        fn test_int_eq(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(<u8 as PartialEq<u8>>::eq(&x.inject(), &y.inject()), std::cmp::PartialEq::eq(&x, &y));
        }

        #[test]
        fn test_int_neq(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                super::Neq::neq(&x.inject(), &y.inject()),
                x != y
            );
        }

        // `PartialOrd::lt` only exists off the F* backend; the workaround
        // trait is covered by `test_defaults_lt`.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_int_lt(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                <u8 as PartialOrd<u8>>::lt(&x.inject(), &y.inject()),
                x < y
            );
        }

        // `PartialOrd::le` only exists off the F* backend; the workaround
        // trait is covered by `test_defaults_le`.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_int_le(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                <u8 as PartialOrd<u8>>::le(&x.inject(), &y.inject()),
                x <= y
            );
        }

        // `PartialOrd::gt` only exists off the F* backend; the workaround
        // trait is covered by `test_defaults_gt`.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_int_gt(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                <u8 as PartialOrd<u8>>::gt(&x.inject(), &y.inject()),
                x > y
            );
        }

        // `PartialOrd::ge` only exists off the F* backend; the workaround
        // trait is covered by `test_defaults_ge`.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_int_ge(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                <u8 as PartialOrd<u8>>::ge(&x.inject(), &y.inject()),
                x >= y
            );
        }

        #[test]
        fn test_defaults_lt(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                super::PartialOrdDefaults::lt(&x.inject(), &y.inject()),
                x < y
            );
        }

        #[test]
        fn test_defaults_le(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                super::PartialOrdDefaults::le(&x.inject(), &y.inject()),
                x <= y
            );
        }

        #[test]
        fn test_defaults_gt(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                super::PartialOrdDefaults::gt(&x.inject(), &y.inject()),
                x > y
            );
        }

        #[test]
        fn test_defaults_ge(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                super::PartialOrdDefaults::ge(&x.inject(), &y.inject()),
                x >= y
            );
        }
    }

    #[test]
    fn test_clamp_min_above_max_panics() {
        crate::testing::panics_like_core(
            || super::clamp(5u8, 7u8, 3u8),
            || std::cmp::Ord::clamp(5u8, 7u8, 3u8),
        );
    }

    // `OrdDefaults` has no F* model (see its definition).
    #[cfg(not(hax_backend_fstar))]
    #[test]
    fn test_ord_clamp_min_above_max_panics() {
        crate::testing::panics_like_core(
            || OrdDefaults::clamp(5u8, 7u8, 3u8),
            || std::cmp::Ord::clamp(5u8, 7u8, 3u8),
        );
    }

    proptest! {
        // ----- Ord's default methods (modelled by `OrdDefaults`) -------------

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_ord_max(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                OrdDefaults::max(x.inject(), y.inject()),
                std::cmp::Ord::max(x, y)
            );
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_ord_min(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(
                OrdDefaults::min(x.inject(), y.inject()),
                std::cmp::Ord::min(x, y)
            );
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_ord_clamp(x in any::<u8>(), a in any::<u8>(), b in any::<u8>()) {
            let lo = std::cmp::min(a, b);
            let hi = std::cmp::max(a, b);
            prop_assert_eq!(
                OrdDefaults::clamp(x.inject(), lo.inject(), hi.inject()),
                std::cmp::Ord::clamp(x, lo, hi)
            );
        }

        // ----- max_by / min_by / max_by_key / min_by_key --------------------

        #[test]
        fn test_max_by(x in any::<Tagged>(), y in any::<Tagged>()) {
            prop_assert_eq!(
                super::max_by(x.inject(), y.inject(), model_by),
                std::cmp::max_by(x, y, std_by).inject()
            );
        }

        #[test]
        fn test_min_by(x in any::<Tagged>(), y in any::<Tagged>()) {
            prop_assert_eq!(
                super::min_by(x.inject(), y.inject(), model_by),
                std::cmp::min_by(x, y, std_by).inject()
            );
        }

        // Under the F* cfg these take a `fn` and a phantom `F` that no call
        // site can infer (same as `array::map`).
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_max_by_key(x in any::<Tagged>(), y in any::<Tagged>()) {
            prop_assert_eq!(
                super::max_by_key(x.inject(), y.inject(), key),
                std::cmp::max_by_key(x, y, key).inject()
            );
        }

        // Under the F* cfg these take a `fn` and a phantom `F` that no call
        // site can infer (same as `array::map`).
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_min_by_key(x in any::<Tagged>(), y in any::<Tagged>()) {
            prop_assert_eq!(
                super::min_by_key(x.inject(), y.inject(), key),
                std::cmp::min_by_key(x, y, key).inject()
            );
        }

        // ----- minmax / minmax_by / minmax_by_key ---------------------------

        #[test]
        fn test_minmax(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(super::minmax(x.inject(), y.inject()), std::cmp::minmax(x, y));
        }

        #[test]
        fn test_minmax_by(x in any::<Tagged>(), y in any::<Tagged>()) {
            prop_assert_eq!(
                super::minmax_by(x.inject(), y.inject(), model_by),
                std::cmp::minmax_by(x, y, std_by).inject()
            );
        }

        // Under the F* cfg these take a `fn` and a phantom `F` that no call
        // site can infer (same as `array::map`).
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_minmax_by_key(x in any::<Tagged>(), y in any::<Tagged>()) {
            prop_assert_eq!(
                super::minmax_by_key(x.inject(), y.inject(), key),
                std::cmp::minmax_by_key(x, y, key).inject()
            );
        }
    }

    // The F* variants of the three `*_by_key` functions take the function as a
    // `fn` pointer plus a phantom `F: FnOnce<..>` the backend types it through.
    // Nothing in the model implements that trait, so the tests name a witness
    // and turbofish it (same shape as `array`'s `fstar_map`).
    #[cfg(hax_backend_fstar)]
    mod fstar_by_key {
        use super::{Tagged, key};
        use crate::testing::Inject;
        use proptest::prelude::*;

        struct Key;

        impl crate::ops::function::FnOnce<Tagged> for Key {
            type Output = u8;
            fn call_once(&self, args: Tagged) -> u8 {
                args.0
            }
        }

        proptest! {
            #[test]
            fn test_max_by_key(x in any::<Tagged>(), y in any::<Tagged>()) {
                prop_assert_eq!(
                    super::super::max_by_key::<Tagged, Key, u8>(x.inject(), y.inject(), key),
                    std::cmp::max_by_key(x, y, key).inject()
                );
            }

            #[test]
            fn test_min_by_key(x in any::<Tagged>(), y in any::<Tagged>()) {
                prop_assert_eq!(
                    super::super::min_by_key::<Tagged, Key, u8>(x.inject(), y.inject(), key),
                    std::cmp::min_by_key(x, y, key).inject()
                );
            }

            #[test]
            fn test_minmax_by_key(x in any::<Tagged>(), y in any::<Tagged>()) {
                prop_assert_eq!(
                    super::super::minmax_by_key::<Tagged, Key, u8>(x.inject(), y.inject(), key),
                    std::cmp::minmax_by_key(x, y, key).inject()
                );
            }

            // The witness's own body, so it is exercised rather than declared.
            #[test]
            fn test_witness_call_once(x in any::<Tagged>()) {
                prop_assert_eq!(
                    crate::ops::function::FnOnce::call_once(&Key, x),
                    key(&x)
                );
            }
        }
    }
}
