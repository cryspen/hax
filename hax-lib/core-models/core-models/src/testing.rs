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

#[cfg(not(hax_backend_fstar))]
impl Inject for CloneWitness {
    type Model = CloneWitness;
    fn inject(&self) -> Self::Model {
        CloneWitness {
            value: self.value,
            cloned: self.cloned,
        }
    }
}

/// The model's `RangeBounds` forms under one type, so a test body can loop over
/// them. Each method delegates to the wrapped range's own impl.
pub enum ModelRange {
    Range(crate::ops::range::Range<usize>),
    From(crate::ops::range::RangeFrom<usize>),
    To(crate::ops::range::RangeTo<usize>),
    Full(crate::ops::range::RangeFull),
    Inclusive(crate::ops::range::RangeInclusive<usize>),
    ToInclusive(crate::ops::range::RangeToInclusive<usize>),
    Pair(
        (
            crate::ops::range::Bound<usize>,
            crate::ops::range::Bound<usize>,
        ),
    ),
}

macro_rules! on_model_range {
    ($range:expr, |$r:ident| $body:expr) => {
        match $range {
            ModelRange::Range($r) => $body,
            ModelRange::From($r) => $body,
            ModelRange::To($r) => $body,
            ModelRange::Full($r) => $body,
            ModelRange::Inclusive($r) => $body,
            ModelRange::ToInclusive($r) => $body,
            ModelRange::Pair($r) => $body,
        }
    };
}

impl crate::ops::range::RangeBounds<usize> for ModelRange {
    fn start_bound(&self) -> crate::ops::range::Bound<&usize> {
        on_model_range!(self, |r| {
            crate::ops::range::RangeBounds::<usize>::start_bound(r)
        })
    }
    fn end_bound(&self) -> crate::ops::range::Bound<&usize> {
        on_model_range!(
            self,
            |r| crate::ops::range::RangeBounds::<usize>::end_bound(r)
        )
    }
    fn contains<U>(&self, item: &U) -> bool
    where
        usize: crate::cmp::PartialOrd<U>,
        U: ?Sized + crate::cmp::PartialOrd<usize>,
    {
        on_model_range!(self, |r| crate::ops::range::RangeBounds::<usize>::contains(
            r, item
        ))
    }
}

fn bound(kind: u8, x: usize) -> (crate::ops::range::Bound<usize>, std::ops::Bound<usize>) {
    use crate::ops::range::Bound as M;
    use std::ops::Bound as S;
    match kind {
        0 => (M::Included(x), S::Included(x)),
        1 => (M::Excluded(x), S::Excluded(x)),
        _ => (M::Unbounded, S::Unbounded),
    }
}

/// Every `RangeBounds` form of the model built from `start` and `end`, each
/// paired with the bounds std gives the same range.
pub fn range_forms(
    start: usize,
    end: usize,
) -> std::vec::Vec<(ModelRange, (std::ops::Bound<usize>, std::ops::Bound<usize>))> {
    use crate::ops::range as m;
    use std::ops::RangeBounds;
    fn bounds<R: RangeBounds<usize>>(r: R) -> (std::ops::Bound<usize>, std::ops::Bound<usize>) {
        (r.start_bound().cloned(), r.end_bound().cloned())
    }
    let mut forms = vec![
        (
            ModelRange::Range(m::Range { start, end }),
            bounds(start..end),
        ),
        (ModelRange::From(m::RangeFrom { start }), bounds(start..)),
        (ModelRange::To(m::RangeTo { end }), bounds(..end)),
        (ModelRange::Full(m::RangeFull), bounds(..)),
        (
            ModelRange::Inclusive(m::RangeInclusive::new(start, end)),
            bounds(start..=end),
        ),
        (
            ModelRange::ToInclusive(m::RangeToInclusive { end }),
            bounds(..=end),
        ),
    ];
    // Iterating to the end leaves `start == end` with `exhausted` set.
    if start <= end {
        let mut exhausted = start..=end;
        exhausted.nth(end - start);
        forms.push((
            ModelRange::Inclusive(m::RangeInclusive {
                lo: end,
                hi: end,
                exhausted: true,
            }),
            bounds(exhausted),
        ));
    }
    for ks in 0..3 {
        for ke in 0..3 {
            let (model_start, std_start) = bound(ks, start);
            let (model_end, std_end) = bound(ke, end);
            forms.push((
                ModelRange::Pair((model_start, model_end)),
                (std_start, std_end),
            ));
        }
    }
    forms
}

/// Range endpoints around the slice lengths the tests use, plus the overflow edge.
pub fn range_endpoint() -> impl proptest::strategy::Strategy<Value = usize> {
    use proptest::prelude::*;
    prop_oneof![0usize..=10, Just(usize::MAX - 1), Just(usize::MAX)]
}
