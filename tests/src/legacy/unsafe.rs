//! @off: ssprove, coq, proverif

#![allow(dead_code)]

enum Impossible {}

#[hax_lib::requires(false)]
/// @fail(extraction): ssprove(HAX0008), coq(HAX0008)
pub fn impossible() -> Impossible {
    unsafe { std::hint::unreachable_unchecked() }
}

#[hax_lib::requires(slice.len() > 10)]
/// @fail(extraction): ssprove(HAX0008), coq(HAX0008)
pub fn get_unchecked_example(slice: &[u8]) -> u8 {
    unsafe { *slice.get_unchecked(6) }
}
