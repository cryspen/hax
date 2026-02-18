use crate::option::Option;

/// See [`std::cmp::PartialEq`]
#[hax_lib::attributes]
pub trait PartialEq<Rhs>
where
    Rhs: ?Sized,
{
    /// See [`std::cmp::PartialEq::eq`]
    #[hax_lib::requires(true)]
    fn eq(&self, other: &Rhs) -> bool;
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
}

// These methods in core are provided using trait defaults, but this is not supported by hax
// so we have to define them in a different way.
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
        #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
        #[hax_lib::attributes]
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
        #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
        #[hax_lib::attributes]
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
        #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
        impl PartialEq<$t> for $t {
            fn eq(&self, other: &Self) -> bool {
                self == other
            }
        }
        #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
        impl Eq for $t {}
    )*)
}

int_impls! { u8 i8 u16 i16 u32 i32 u64 i64 u128 i128 usize isize }

#[cfg(test)]
mod tests {
    use super::{Ord, PartialEq, PartialOrd};
    use crate::testing::Inject;
    use proptest::prelude::*;

    proptest! {
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
    }
}
