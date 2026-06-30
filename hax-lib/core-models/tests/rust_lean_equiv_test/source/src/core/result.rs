//! Equivalence tests for `core::result::Result::*`.

use rust_lean_test_macro::rust_lean_test;

// Local helpers: function-level return-type annotations survive Aeneas
// extraction even when the variant only pins one of the two type params.
// Without these, `Ok(0u8)` leaves `E` unknown and `Err(0u8)` leaves `T`
// unknown, producing Lean output that fails to elaborate.
fn ok_u8_u8(v: u8) -> Result<u8, u8> {
    Ok(v)
}
fn err_u8_u8(e: u8) -> Result<u8, u8> {
    Err(e)
}

// ----- is_ok / is_err --------------------------------------------------------

#[rust_lean_test]
pub fn test_is_ok_ok_zero() -> bool {
    ok_u8_u8(0).is_ok() == true
}

#[rust_lean_test]
pub fn test_is_ok_ok_max() -> bool {
    ok_u8_u8(u8::MAX).is_ok() == true
}

#[rust_lean_test]
pub fn test_is_ok_err_zero() -> bool {
    err_u8_u8(0).is_ok() == false
}

#[rust_lean_test]
pub fn test_is_ok_err_max() -> bool {
    err_u8_u8(u8::MAX).is_ok() == false
}

#[rust_lean_test]
pub fn test_is_err_ok_zero() -> bool {
    ok_u8_u8(0).is_err() == false
}

#[rust_lean_test]
pub fn test_is_err_err_zero() -> bool {
    err_u8_u8(0).is_err() == true
}

#[rust_lean_test]
pub fn test_is_err_err_max() -> bool {
    err_u8_u8(u8::MAX).is_err() == true
}

// ----- is_ok_and -------------------------------------------------------------

// TODO(result-method-missing: `Result::is_ok_and` missing from extracted Lean —
// the core-models `Result` impl is marked `aeneas::exclude`, so closure-taking
// methods have no model. Revisit once Result methods are exposed.)

// ----- is_err_and ------------------------------------------------------------

// TODO(result-method-missing: `Result::is_err_and` missing from extracted Lean
// (see is_ok_and).)

// ----- as_ref ----------------------------------------------------------------

// TODO(as_ref): as_ref returns Result<&T, &E> which involves references-to-references
// through extraction; skip until references are exercised.

// ----- expect ----------------------------------------------------------------

// TODO(result-method-missing: `Result::expect` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_expect_ok_zero() -> bool {
    ok_u8_u8(0).expect("msg") == 0
}
*/

// TODO(result-method-missing: `Result::expect` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_expect_ok_max() -> bool {
    ok_u8_u8(u8::MAX).expect("msg") == u8::MAX
}
*/

// TODO(result-method-missing: `Result::expect` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_expect_ok_mid() -> bool {
    ok_u8_u8(42).expect("msg") == 42
}
*/

// ----- unwrap ----------------------------------------------------------------

// TODO(result-method-missing: `Result::unwrap` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_unwrap_ok_zero() -> bool {
    ok_u8_u8(0).unwrap() == 0
}
*/

// TODO(result-method-missing: `Result::unwrap` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_unwrap_ok_max() -> bool {
    ok_u8_u8(u8::MAX).unwrap() == u8::MAX
}
*/

// TODO(result-method-missing: `Result::unwrap` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_unwrap_ok_mid() -> bool {
    ok_u8_u8(7).unwrap() == 7
}
*/

// ----- unwrap_err ------------------------------------------------------------

// TODO(result-method-missing: `Result::unwrap_err` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_unwrap_err_err_zero() -> bool {
    err_u8_u8(0).unwrap_err() == 0
}
*/

// TODO(result-method-missing: `Result::unwrap_err` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_unwrap_err_err_max() -> bool {
    err_u8_u8(u8::MAX).unwrap_err() == u8::MAX
}
*/

// TODO(result-method-missing: `Result::unwrap_err` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_unwrap_err_err_mid() -> bool {
    err_u8_u8(7).unwrap_err() == 7
}
*/

// ----- unwrap_or -------------------------------------------------------------

// TODO(result-method-missing: `Result::unwrap_or` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_unwrap_or_ok_zero() -> bool {
    ok_u8_u8(0).unwrap_or(99) == 0
}
*/

// TODO(result-method-missing: `Result::unwrap_or` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_unwrap_or_ok_max() -> bool {
    ok_u8_u8(u8::MAX).unwrap_or(0) == u8::MAX
}
*/

// TODO(result-method-missing: `Result::unwrap_or` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_unwrap_or_err_default_zero() -> bool {
    err_u8_u8(99).unwrap_or(0) == 0
}
*/

// TODO(result-method-missing: `Result::unwrap_or` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_unwrap_or_err_default_max() -> bool {
    err_u8_u8(0).unwrap_or(u8::MAX) == u8::MAX
}
*/

// ----- unwrap_or_else --------------------------------------------------------

// TODO(result-method-missing: `Result::unwrap_or_else` missing from extracted
// Lean — the core-models `Result` impl is `aeneas::exclude`.)

// ----- unwrap_or_default -----------------------------------------------------

// TODO(result-method-missing: `Result::unwrap_or_default` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_unwrap_or_default_ok_zero() -> bool {
    ok_u8_u8(0).unwrap_or_default() == 0
}
*/

// TODO(result-method-missing: `Result::unwrap_or_default` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_unwrap_or_default_ok_max() -> bool {
    ok_u8_u8(u8::MAX).unwrap_or_default() == u8::MAX
}
*/

// TODO(result-method-missing: `Result::unwrap_or_default` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_unwrap_or_default_err() -> bool {
    err_u8_u8(u8::MAX).unwrap_or_default() == 0
}
*/

// ----- map -------------------------------------------------------------------

// TODO(result-method-missing: `Result::map` missing from extracted Lean —
// the core-models `Result` impl is `aeneas::exclude`.)

// ----- map_or ----------------------------------------------------------------

// TODO(result-method-missing: `Result::map_or` missing from extracted Lean
// (see map).)

// ----- map_or_else -----------------------------------------------------------

// TODO(result-method-missing: `Result::map_or_else` missing from extracted
// Lean (see map).)

// ----- map_or_default --------------------------------------------------------

// TODO(result-method-missing: `Result::map_or_default` missing from extracted
// Lean (see map).)

// ----- map_err ---------------------------------------------------------------

// TODO(result-method-missing: `Result::map_err` missing from extracted Lean
// (see map).)

// ----- inspect / inspect_err -------------------------------------------------

// TODO(result-method-missing: `Result::inspect` and `Result::inspect_err`
// missing from extracted Lean (see map). They also take `&T`/`&E` closures,
// which Aeneas would reject even if the methods were present.)

// ----- ok --------------------------------------------------------------------

// TODO(result-method-missing: `Result::unwrap_or` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_ok_ok_zero() -> bool {
    ok_u8_u8(0).ok().unwrap_or(99) == 0
}
*/

// TODO(result-method-missing: `Result::unwrap_or` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_ok_ok_max() -> bool {
    ok_u8_u8(u8::MAX).ok().unwrap_or(0) == u8::MAX
}
*/

#[rust_lean_test]
pub fn test_ok_err() -> bool {
    err_u8_u8(7).ok().is_none()
}

// ----- err -------------------------------------------------------------------

// TODO(result-method-missing: `Result::unwrap_or` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_err_err_zero() -> bool {
    err_u8_u8(0).err().unwrap_or(99) == 0
}
*/

// TODO(result-method-missing: `Result::unwrap_or` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_err_err_max() -> bool {
    err_u8_u8(u8::MAX).err().unwrap_or(0) == u8::MAX
}
*/

#[rust_lean_test]
pub fn test_err_ok() -> bool {
    ok_u8_u8(7).err().is_none()
}

// ----- and -------------------------------------------------------------------

// TODO(result-method-missing: `Result::unwrap_or` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_and_ok_ok() -> bool {
    ok_u8_u8(0).and(ok_u8_u8(7)).unwrap_or(99) == 7
}
*/

// TODO(result-method-missing: `Result::unwrap_err` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_and_ok_err() -> bool {
    ok_u8_u8(0).and(err_u8_u8(42)).unwrap_err() == 42
}
*/

// TODO(result-method-missing: `Result::unwrap_err` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_and_err_ok() -> bool {
    err_u8_u8(99).and(ok_u8_u8(0)).unwrap_err() == 99
}
*/

// TODO(result-method-missing: `Result::unwrap_err` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_and_err_err() -> bool {
    err_u8_u8(u8::MAX).and(err_u8_u8(0)).unwrap_err() == u8::MAX
}
*/

// ----- and_then --------------------------------------------------------------

// TODO(result-method-missing: `Result::and_then` missing from extracted Lean —
// the core-models `Result` impl is `aeneas::exclude`.)

// ----- or --------------------------------------------------------------------

// TODO(result-method-missing: `Result::unwrap_or` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_or_ok_ok() -> bool {
    ok_u8_u8(0).or(ok_u8_u8(99)).unwrap_or(7) == 0
}
*/

// TODO(result-method-missing: `Result::unwrap_or` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_or_ok_err() -> bool {
    ok_u8_u8(u8::MAX).or(err_u8_u8(42)).unwrap_or(0) == u8::MAX
}
*/

// TODO(result-method-missing: `Result::unwrap_or` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_or_err_ok() -> bool {
    err_u8_u8(99).or(ok_u8_u8(42)).unwrap_or(0) == 42
}
*/

// TODO(result-method-missing: `Result::unwrap_err` missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_or_err_err() -> bool {
    err_u8_u8(99).or(err_u8_u8(7)).unwrap_err() == 7
}
*/

// ----- or_else ---------------------------------------------------------------

// TODO(result-method-missing: `Result::or_else` missing from extracted Lean —
// the core-models `Result` impl is `aeneas::exclude`.)

// ----- cloned ----------------------------------------------------------------

// TODO(result-cloned-shape): the model's `cloned` takes `self` and returns
// `Result<T, E>` (an identity over our clone-by-value `Clone`). Std's
// `Result::cloned` lives on `Result<&T, E>` and is unstable, so calling
// `.cloned()` directly from the Rust side does not type-check on stable.
// Revisit when references/shared semantics get a typed test surface.

// ----- transpose -------------------------------------------------------------

// Helpers for Result<Option<u8>, u8>: typed via function return type.
fn ok_some_u8(v: u8) -> Result<Option<u8>, u8> {
    Ok(Some(v))
}
fn ok_none_u8() -> Result<Option<u8>, u8> {
    let mut x: Option<u8> = Some(0);
    x.take();
    Ok(x)
}
fn err_outer_u8(e: u8) -> Result<Option<u8>, u8> {
    Err(e)
}

// TODO(result-method-missing: `Result::transpose` and `Option::transpose` are missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_transpose_ok_some_zero() -> bool {
    match ok_some_u8(0).transpose() {
        Some(Ok(v)) => v == 0,
        _ => false,
    }
}
*/

// TODO(result-method-missing: `Result::transpose` and `Option::transpose` are missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_transpose_ok_some_max() -> bool {
    match ok_some_u8(u8::MAX).transpose() {
        Some(Ok(v)) => v == u8::MAX,
        _ => false,
    }
}
*/

// TODO(result-method-missing: `Result::transpose` and `Option::transpose` are missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_transpose_ok_none() -> bool {
    ok_none_u8().transpose().is_none()
}
*/

// TODO(result-method-missing: `Result::transpose` and `Option::transpose` are missing from extracted Lean.)
/*
#[rust_lean_test]
pub fn test_transpose_err() -> bool {
    match err_outer_u8(7).transpose() {
        Some(Err(e)) => e == 7,
        _ => false,
    }
}
*/

// ----- flatten ---------------------------------------------------------------

// TODO(result-flatten-unstable): `Result::flatten` is gated behind the
// `result_flattening` feature on stable std. The model defines `flatten`
// directly so the Lean side works, but the Rust side cannot call
// `r.flatten()` on stable. Revisit once `result_flattening` stabilises.
