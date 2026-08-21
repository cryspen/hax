//! Error types for conversion to integral types.
#![allow(unused_variables)]

/// See [`std::num::TryFromIntError`]
#[cfg_attr(test, derive(PartialEq, Debug))]
pub struct TryFromIntError(pub(crate) ());

/// Always `true` like std's derived instance — the type carries no payload.
/// F* compares structurally, so this is aeneas/lean only.
#[cfg(not(hax_backend_fstar))]
impl crate::cmp::PartialEq<TryFromIntError> for TryFromIntError {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

/// See [`std::num::ParseIntError`]
pub struct ParseIntError {
    pub(super) kind: IntErrorKind,
}

// Because of representations, enums bring a dependency to isize.
// TODO Fix the dependency issue and add `IntErrorKind`
/* pub enum IntErrorKind {
    Empty,
    InvalidDigit,
    PosOverflow,
    NegOverflow,
    Zero,
} */

/// See [`std::num::IntErrorKind`]
pub struct IntErrorKind;
