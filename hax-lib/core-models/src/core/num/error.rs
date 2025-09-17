//! Error types for conversion to integral types.
#![allow(unused_variables)]

use crate::convert::Infallible;
use crate::error::Error;
use crate::fmt;
/// The error type returned when a checked integral type conversion fails.
pub struct TryFromIntError(pub(crate) ());
impl fmt::Display for TryFromIntError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        panic!()
    }
}
impl Error for TryFromIntError {}
impl From<Infallible> for TryFromIntError {
    fn from(x: Infallible) -> TryFromIntError {
        panic!()
    }
}
/// An error which can be returned when parsing an integer.
///
/// This error is used as the error type for the `from_str_radix()` functions
/// on the primitive integer types, such as [`i8::from_str_radix`].
///
/// # Potential causes
///
/// Among other causes, `ParseIntError` can be thrown because of leading or trailing whitespace
/// in the string e.g., when it is obtained from the standard input.
/// Using the [`str::trim()`] method ensures that no whitespace remains before parsing.
///
/// # Example
///
/// ```
/// if let Err(e) = i32::from_str_radix("a12", 10) {
///     println!("Failed conversion to i32: {e}");
/// }
/// ```
pub struct ParseIntError {
    pub(super) kind: IntErrorKind,
}
/// Enum to store the various types of errors that can cause parsing an integer to fail.
///
/// # Example
///
/// ```
/// # fn main() {
/// if let Err(e) = i32::from_str_radix("a12", 10) {
///     println!("Failed conversion to i32: {:?}", e.kind());
/// }
/// # }
/// ```
pub enum IntErrorKind {
    /// Value being parsed is empty.
    ///
    /// This variant will be constructed when parsing an empty string.
    Empty,
    /// Contains an invalid digit in its context.
    ///
    /// Among other causes, this variant will be constructed when parsing a string that
    /// contains a non-ASCII char.
    ///
    /// This variant is also constructed when a `+` or `-` is misplaced within a string
    /// either on its own or in the middle of a number.
    InvalidDigit,
    /// Integer is too large to store in target integer type.
    PosOverflow,
    /// Integer is too small to store in target integer type.
    NegOverflow,
    /// Value was Zero
    ///
    /// This variant will be emitted when the parsing string has a value of zero, which
    /// would be illegal for non-zero types.
    Zero,
}
impl ParseIntError {
    /// Outputs the detailed cause of parsing an integer failing.
    pub const fn kind(&self) -> &IntErrorKind {
        &self.kind
    }
}
impl fmt::Display for ParseIntError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        panic!()
    }
}
impl Error for ParseIntError {}
