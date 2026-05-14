// Exercises Stage 2.2 — `#[hax_lib::pv_inline]` β-substitution.
//
// `apply_twice(x, f)` is marked `pv_inline`, so every call to it
// disappears from the output, replaced by an inlined match shape with
// the closure body β-reduced into the call positions.

#[hax_lib::pv_inline]
fn apply_twice(x: u8, f: fn(u8) -> u8) -> u8 {
    f(f(x))
}

// One concrete callee for the closure to reduce against.
fn increment(x: u8) -> u8 {
    x
}

// The use site. After resugaring, this should not contain a call to
// `apply_twice`; instead the body of `apply_twice` shows up in line
// here with the closure-arg β-reduced.
fn run(start: u8) -> u8 {
    apply_twice(start, |y| increment(y))
}
