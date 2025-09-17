//! Error types for conversion to integral types.
#![allow(unused_variables)]

pub struct TryFromIntError(pub(crate) ());

pub struct ParseIntError {
    pub(super) kind: IntErrorKind,
}

// enums bring a dependency to isize, leaving this away for now.
/* pub enum IntErrorKind {
    Empty,
    InvalidDigit,
    PosOverflow,
    NegOverflow,
    Zero,
} */

pub struct IntErrorKind;
