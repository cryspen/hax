//! The `else` branch of an `if c { panic!() } else { .. }` must survive the
//! assert reconstruction.

#![allow(dead_code)]

/// Value in the else branch.
pub fn checked_incr(c: bool, x: u32) -> u32 {
    if c { panic!() } else { x + 1 }
}

/// Nested panic-elses.
pub fn nested(c: bool, d: bool, x: u32) -> u32 {
    if c {
        panic!()
    } else if d {
        panic!()
    } else {
        x
    }
}

/// No else.
pub fn bare(c: bool) {
    if c { panic!() }
}
