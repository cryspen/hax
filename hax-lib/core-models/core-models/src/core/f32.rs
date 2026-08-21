//! Model of `core::f32` — a stub, and it cannot currently be more than that:
//! **neither backend can represent an IEEE-754 float.**
//!
//! - aeneas has no float type at all. Nothing in its Lean library defines
//!   `F32`/`F64`, so the `F32` in the extracted signature below is silently
//!   turned into a type *variable* by Lean's `autoImplicit`; it elaborates, but
//!   it means nothing. A float literal is worse than that: aeneas rejects it
//!   ("Improperly typed constant value") and emits `:= sorry`, so any modeled
//!   constant — `PI`, `MAX`, `EPSILON`, `NAN`, … — makes `make extract` fail.
//!   Float `+`/`-`/`*`/`/` give "Invalid inputs for binop", float comparison
//!   fails the same way, and an `as f64` cast crashes the pretty-printer.
//! - hax/F* has `Rust_primitives.Float.float`, an abstract `eqtype` whose only
//!   introduction form is `mk_float : string -> float`. It carries no
//!   arithmetic, no ordering and no bit-level view, `f32` and `f64` collapse
//!   onto the same type, and a literal extracts to an *uninterpreted*
//!   `mk_float "3.14159…"` — a name with no relation to pi.
//!
//! So none of the 106 missing `core::f32` items (the `consts`, the
//! classification predicates, `to_bits`/`from_bits`/`to_be_bytes`,
//! `total_cmp`, the arithmetic, the `algebraic_*` variants) can be modeled
//! honestly here. The prerequisite is float support in aeneas and a concrete
//! float representation in `Rust_primitives.Float` — not more Rust.

/// See [`std::primitive::f32`]
#[allow(non_camel_case_types)]
// F*-only: under `cfg(charon)` `hax_lib::exclude` now emits `charon::exclude`,
// which drops this dummy type while its `impl` block still references it.
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
struct f32;

impl f32 {
    /// See [`std::primitive::f32::abs`]
    #[hax_lib::opaque]
    fn abs(x: f64) -> f64 {
        rust_primitives::float::abs_f64(x)
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    proptest! {
        // Compared on bits so that NaN inputs (where `==` is false) still count.
        #[test]
        fn test_abs(x in any::<f64>()) {
            prop_assert_eq!(super::f32::abs(x).to_bits(), x.abs().to_bits());
        }
    }
}
