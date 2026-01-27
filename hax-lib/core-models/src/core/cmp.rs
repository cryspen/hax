use crate::option::Option;

#[hax_lib::attributes]
pub trait PartialEq<Rhs>
where
    Rhs: ?Sized,
{
    #[hax_lib::requires(true)]
    fn eq(&self, other: &Rhs) -> bool;
}

pub trait Eq: PartialEq<Self> {}

pub enum Ordering {
    Less = -1,
    Equal = 0,
    Greater = 1,
}

#[hax_lib::attributes]
pub trait PartialOrd<Rhs>: PartialEq<Rhs>
where
    Rhs: ?Sized,
{
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

#[hax_lib::attributes]
pub trait Ord: Eq + PartialOrd<Self> {
    #[hax_lib::requires(true)]
    fn cmp(&self, other: &Self) -> Ordering;
}

pub fn max<T: Ord>(v1: T, v2: T) -> T {
    match v1.cmp(&v2) {
        Ordering::Greater => v1,
        _ => v2,
    }
}

pub fn min<T: Ord>(v1: T, v2: T) -> T {
    match v1.cmp(&v2) {
        Ordering::Greater => v2,
        _ => v1,
    }
}

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
        impl PartialEq<$t> for $t {
            fn eq(&self, other: &Self) -> bool {
                self == other
            }
        }
        impl Eq for $t {}
    )*)
}

int_impls! { u8 i8 u16 i16 u32 i32 u64 i64 u128 i128 usize isize }
