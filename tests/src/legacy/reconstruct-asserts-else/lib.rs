//! An `if c { panic!() } else { .. }` is not an `assert!` expansion: it keeps
//! its `else` branch instead of being reconstructed into an assert.

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
