//! Error types for conversion to integral types.
#![allow(unused_variables)]

pub struct TryFromIntError(pub(crate) ());

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

pub struct IntErrorKind;
