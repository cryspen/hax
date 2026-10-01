#![allow(dead_code)]

/// @fail(extraction): ssprove(HAX0001)
pub fn project_tuple1() -> u8 {
    let tuple1: (u8,) = (3,);
    tuple1.0
}
