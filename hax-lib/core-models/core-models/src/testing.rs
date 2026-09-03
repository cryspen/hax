pub trait Inject {
    type Model;
    fn inject(&self) -> Self::Model;
}

impl<T: Inject> Inject for &T {
    type Model = T::Model;

    fn inject(&self) -> Self::Model {
        (*self).inject()
    }
}

macro_rules! inject_as_self {
    ($($t:ty)*) => {
        $(
            impl Inject for $t {
                type Model = $t;
                fn inject(&self) -> $t {
                    *self
                }
            }
        )*
    }
}

inject_as_self! {u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize bool}

impl<T: Inject> Inject for Option<T> {
    type Model = crate::option::Option<T::Model>;
    fn inject(&self) -> Self::Model {
        match self {
            Some(v) => crate::option::Option::Some(v.inject()),
            None => crate::option::Option::None,
        }
    }
}

impl<T: Inject, E: Inject> Inject for Result<T, E> {
    type Model = crate::result::Result<T::Model, E::Model>;
    fn inject(&self) -> Self::Model {
        match self {
            Ok(v) => crate::result::Result::Ok(v.inject()),
            Err(e) => crate::result::Result::Err(e.inject()),
        }
    }
}

impl Inject for std::cmp::Ordering {
    type Model = crate::cmp::Ordering;
    fn inject(&self) -> Self::Model {
        match self {
            std::cmp::Ordering::Less => crate::cmp::Ordering::Less,
            std::cmp::Ordering::Equal => crate::cmp::Ordering::Equal,
            std::cmp::Ordering::Greater => crate::cmp::Ordering::Greater,
        }
    }
}

impl<T: Inject> Inject for std::cmp::Reverse<T> {
    type Model = crate::cmp::Reverse<T::Model>;
    fn inject(&self) -> Self::Model {
        crate::cmp::Reverse(self.0.inject())
    }
}

impl Inject for std::num::TryFromIntError {
    type Model = crate::num::error::TryFromIntError;
    fn inject(&self) -> Self::Model {
        crate::num::error::TryFromIntError(())
    }
}

impl<'a, T> Inject for &'a [T] {
    type Model = &'a [T];
    fn inject(&self) -> Self::Model {
        self
    }
}

impl<'a> Inject for &'a str {
    type Model = &'a str;
    fn inject(&self) -> Self::Model {
        self
    }
}

impl<A: Inject, B: Inject> Inject for (A, B) {
    type Model = (A::Model, B::Model);
    fn inject(&self) -> Self::Model {
        (self.0.inject(), self.1.inject())
    }
}

/// Asserts the model and real `core` both panic on the same input. `should_panic`
/// alone only shows the model panics; the second arm checks that is what Rust does.
#[track_caller]
pub fn panics_like_core<A, B>(model: impl FnOnce() -> A, core: impl FnOnce() -> B) {
    use std::panic::{AssertUnwindSafe, catch_unwind};
    let m = catch_unwind(AssertUnwindSafe(model));
    let c = catch_unwind(AssertUnwindSafe(core));
    assert!(m.is_err(), "the model did not panic");
    assert!(
        c.is_err(),
        "real `core` did not panic, so the model must not either"
    );
}

/// A value that records whether it was cloned, so a model that drops the
/// element `Clone` dictionary is observable.
///
/// Not built under `hax_backend_fstar`, whose blanket `impl<T> Clone for T`
/// would collide.
#[cfg(not(hax_backend_fstar))]
#[derive(Debug, PartialEq)]
pub struct CloneWitness {
    pub value: u8,
    pub cloned: bool,
}

#[cfg(not(hax_backend_fstar))]
impl CloneWitness {
    pub fn new(value: u8) -> Self {
        CloneWitness {
            value,
            cloned: false,
        }
    }
}

#[cfg(not(hax_backend_fstar))]
impl std::clone::Clone for CloneWitness {
    fn clone(&self) -> Self {
        CloneWitness {
            value: self.value,
            cloned: true,
        }
    }
}

#[cfg(not(hax_backend_fstar))]
impl crate::clone::Clone for CloneWitness {
    fn clone(self) -> Self {
        CloneWitness {
            value: self.value,
            cloned: true,
        }
    }
}

/// An `Ord` coarser than equality: two `Keyed` compare `Equal` when their
/// `key` matches, while staying distinguishable by `tag`.
#[derive(Debug, Clone, Copy)]
pub struct Keyed {
    pub key: u8,
    pub tag: u8,
}

pub fn keyed(key: u8, tag: u8) -> Keyed {
    Keyed { key, tag }
}

impl std::cmp::PartialEq for Keyed {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl std::cmp::Eq for Keyed {}

impl std::cmp::PartialOrd for Keyed {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(std::cmp::Ord::cmp(self, other))
    }
}

impl std::cmp::Ord for Keyed {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key.cmp(&other.key)
    }
}

impl crate::cmp::PartialEq<Keyed> for Keyed {
    fn eq(&self, other: &Keyed) -> bool {
        self.key == other.key
    }
}

impl crate::cmp::Eq for Keyed {}

impl crate::cmp::PartialOrd<Keyed> for Keyed {
    fn partial_cmp(&self, other: &Keyed) -> crate::option::Option<crate::cmp::Ordering> {
        crate::option::Option::Some(crate::cmp::Ord::cmp(self, other))
    }
}

impl crate::cmp::Ord for Keyed {
    fn cmp(&self, other: &Keyed) -> crate::cmp::Ordering {
        if self.key < other.key {
            crate::cmp::Ordering::Less
        } else if self.key > other.key {
            crate::cmp::Ordering::Greater
        } else {
            crate::cmp::Ordering::Equal
        }
    }
}
