//! Equivalence tests for `core::option::Option::*`.

use crate::helpers::none_u8;
use rust_lean_test_macro::rust_lean_test;

// ----- is_some / is_none -----------------------------------------------------

#[rust_lean_test]
pub fn test_is_some_none_u8() -> bool {
    none_u8().is_some() == false
}

#[rust_lean_test]
pub fn test_is_some_some_zero() -> bool {
    Some(0u8).is_some() == true
}

#[rust_lean_test]
pub fn test_is_some_some_max() -> bool {
    Some(u8::MAX).is_some() == true
}

#[rust_lean_test]
pub fn test_is_none_none_u8() -> bool {
    none_u8().is_none() == true
}

#[rust_lean_test]
pub fn test_is_none_some_zero() -> bool {
    Some(0u8).is_none() == false
}

#[rust_lean_test]
pub fn test_is_none_some_max() -> bool {
    Some(u8::MAX).is_none() == false
}

// ----- is_some_and -----------------------------------------------------------

#[rust_lean_test]
pub fn test_is_some_and_some_true() -> bool {
    Some(4u8).is_some_and(|x| x > 0) == true
}

#[rust_lean_test]
pub fn test_is_some_and_some_false() -> bool {
    Some(0u8).is_some_and(|x| x > 0) == false
}

#[rust_lean_test]
pub fn test_is_some_and_none() -> bool {
    none_u8().is_some_and(|x| x > 0) == false
}

// ----- is_none_or ------------------------------------------------------------

#[rust_lean_test]
pub fn test_is_none_or_some_true() -> bool {
    Some(4u8).is_none_or(|x| x > 0) == true
}

#[rust_lean_test]
pub fn test_is_none_or_some_false() -> bool {
    Some(0u8).is_none_or(|x| x > 0) == false
}

#[rust_lean_test]
pub fn test_is_none_or_none() -> bool {
    none_u8().is_none_or(|x| x > 0) == true
}

// ----- as_ref ----------------------------------------------------------------

// TODO(as_ref): as_ref returns Option<&T> which involves references-to-references
// through extraction; skip until references are exercised.

// ----- expect ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_expect_some_zero() -> bool {
    Some(0u8).expect("msg") == 0
}

#[rust_lean_test]
pub fn test_expect_some_max() -> bool {
    Some(u8::MAX).expect("msg") == u8::MAX
}

#[rust_lean_test]
pub fn test_expect_some_mid() -> bool {
    Some(42u8).expect("msg") == 42
}

// ----- unwrap ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_some_zero() -> bool {
    Some(0u8).unwrap() == 0
}

#[rust_lean_test]
pub fn test_unwrap_some_max() -> bool {
    Some(u8::MAX).unwrap() == u8::MAX
}

#[rust_lean_test]
pub fn test_unwrap_some_mid() -> bool {
    Some(7u8).unwrap() == 7
}

// ----- unwrap_or -------------------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_or_some_zero() -> bool {
    Some(0u8).unwrap_or(42) == 0
}

#[rust_lean_test]
pub fn test_unwrap_or_some_max() -> bool {
    Some(u8::MAX).unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_unwrap_or_none_default_zero() -> bool {
    none_u8().unwrap_or(0) == 0
}

#[rust_lean_test]
pub fn test_unwrap_or_none_default_max() -> bool {
    none_u8().unwrap_or(u8::MAX) == u8::MAX
}

// ----- unwrap_or_else --------------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_or_else_some_zero() -> bool {
    Some(0u8).unwrap_or_else(|| 42) == 0
}

#[rust_lean_test]
pub fn test_unwrap_or_else_some_max() -> bool {
    Some(u8::MAX).unwrap_or_else(|| 0) == u8::MAX
}

#[rust_lean_test]
pub fn test_unwrap_or_else_none() -> bool {
    none_u8().unwrap_or_else(|| 7) == 7
}

// ----- unwrap_or_default -----------------------------------------------------

#[rust_lean_test]
pub fn test_unwrap_or_default_some_zero() -> bool {
    Some(0u8).unwrap_or_default() == 0
}

#[rust_lean_test]
pub fn test_unwrap_or_default_some_max() -> bool {
    Some(u8::MAX).unwrap_or_default() == u8::MAX
}

#[rust_lean_test]
pub fn test_unwrap_or_default_none() -> bool {
    none_u8().unwrap_or_default() == 0
}

// ----- map -------------------------------------------------------------------

// TODO(closure-extraction-map): `Option::map` returns `Option<U>`; observing the
// result requires either `Option::PartialEq` (blocked by option-eq-extraction)
// or destructuring through `match`, but the latter goes back through
// `Option::PartialEq` once we compare the inner value. Revisit alongside
// option-eq-extraction.

#[rust_lean_test]
pub fn test_map_some_via_unwrap_or() -> bool {
    Some(3u8).map(|x| x + 1).unwrap_or(0) == 4
}

#[rust_lean_test]
pub fn test_map_none_via_unwrap_or() -> bool {
    none_u8().map(|x| x + 1).unwrap_or(99) == 99
}

#[rust_lean_test]
pub fn test_map_some_is_some() -> bool {
    Some(3u8).map(|x| x + 1).is_some()
}

#[rust_lean_test]
pub fn test_map_none_is_none() -> bool {
    none_u8().map(|x| x + 1).is_none()
}

// ----- map_or ----------------------------------------------------------------

#[rust_lean_test]
pub fn test_map_or_some_zero() -> bool {
    Some(3u8).map_or(0u8, |x| x + 1) == 4
}

#[rust_lean_test]
pub fn test_map_or_some_max() -> bool {
    Some(0u8).map_or(99u8, |x| x + 1) == 1
}

#[rust_lean_test]
pub fn test_map_or_none() -> bool {
    none_u8().map_or(99u8, |x| x + 1) == 99
}

// ----- map_or_else -----------------------------------------------------------

// TODO(closure-extraction-order): `Option::map_or_else` takes (default: D, f: F)
// in source order but the model lists the trait instances in (F, D) order, so
// Aeneas emits them swapped and the Lean elaboration fails for the `None`
// branch. Revisit once the closure-instance ordering is fixed.

// ----- map_or_default --------------------------------------------------------

// TODO(map_or_default-unstable): `Option::map_or_default` is gated behind
// `result_option_map_or_default` on stable. Revisit once it stabilises.

// ----- ok_or -----------------------------------------------------------------

#[rust_lean_test]
pub fn test_ok_or_some_zero() -> bool {
    matches!(Some(0u8).ok_or(99u8), Ok(0))
}

#[rust_lean_test]
pub fn test_ok_or_some_max() -> bool {
    matches!(Some(u8::MAX).ok_or(0u8), Ok(v) if v == u8::MAX)
}

#[rust_lean_test]
pub fn test_ok_or_none_err_zero() -> bool {
    matches!(none_u8().ok_or(0u8), Err(0))
}

#[rust_lean_test]
pub fn test_ok_or_none_err_max() -> bool {
    matches!(none_u8().ok_or(u8::MAX), Err(v) if v == u8::MAX)
}

// ----- ok_or_else ------------------------------------------------------------

#[rust_lean_test]
pub fn test_ok_or_else_some() -> bool {
    matches!(Some(7u8).ok_or_else(|| 99u8), Ok(7))
}

#[rust_lean_test]
pub fn test_ok_or_else_none() -> bool {
    matches!(none_u8().ok_or_else(|| 42u8), Err(42))
}

// ----- and_then --------------------------------------------------------------

#[rust_lean_test]
pub fn test_and_then_some_to_some() -> bool {
    Some(3u8).and_then(|x| Some(x + 1)).unwrap_or(0) == 4
}

#[rust_lean_test]
pub fn test_and_then_some_to_none() -> bool {
    Some(3u8).and_then(|_| none_u8()).is_none()
}

#[rust_lean_test]
pub fn test_and_then_none() -> bool {
    none_u8().and_then(|x| Some(x + 1)).is_none()
}

// ----- filter ----------------------------------------------------------------

// TODO(closure-by-ref-extraction): `Option::filter` takes `FnOnce(&T) -> bool`;
// Aeneas trips on the borrow with "Region ids should not be visited directly".
// Revisit once closures whose parameter is a reference extract.

// ----- or --------------------------------------------------------------------

#[rust_lean_test]
pub fn test_or_some_some() -> bool {
    Some(0u8).or(Some(99u8)).unwrap_or(7) == 0
}

#[rust_lean_test]
pub fn test_or_some_none() -> bool {
    Some(u8::MAX).or(none_u8()).unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_or_none_some() -> bool {
    none_u8().or(Some(42u8)).unwrap_or(0) == 42
}

#[rust_lean_test]
pub fn test_or_none_none() -> bool {
    none_u8().or(none_u8()).is_none()
}

// ----- or_else ---------------------------------------------------------------

#[rust_lean_test]
pub fn test_or_else_some_kept() -> bool {
    Some(0u8).or_else(|| Some(99u8)).unwrap_or(7) == 0
}

#[rust_lean_test]
pub fn test_or_else_some_max_kept() -> bool {
    Some(u8::MAX).or_else(|| none_u8()).unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_or_else_none_to_some() -> bool {
    none_u8().or_else(|| Some(42u8)).unwrap_or(0) == 42
}

#[rust_lean_test]
pub fn test_or_else_none_to_none() -> bool {
    none_u8().or_else(|| none_u8()).is_none()
}

// ----- xor -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_xor_some_none() -> bool {
    Some(7u8).xor(none_u8()).unwrap_or(0) == 7
}

#[rust_lean_test]
pub fn test_xor_none_some() -> bool {
    none_u8().xor(Some(u8::MAX)).unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_xor_some_some() -> bool {
    Some(0u8).xor(Some(99u8)).is_none()
}

#[rust_lean_test]
pub fn test_xor_none_none() -> bool {
    none_u8().xor(none_u8()).is_none()
}

// ----- zip -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_zip_some_some_zero() -> bool {
    match Some(0u8).zip(Some(0u8)) {
        Some((a, b)) => a == 0 && b == 0,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_zip_some_some_max() -> bool {
    match Some(u8::MAX).zip(Some(0u8)) {
        Some((a, b)) => a == u8::MAX && b == 0,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_zip_some_none() -> bool {
    Some(7u8).zip(none_u8()).is_none()
}

#[rust_lean_test]
pub fn test_zip_none_some() -> bool {
    none_u8().zip(Some(7u8)).is_none()
}

#[rust_lean_test]
pub fn test_zip_none_none() -> bool {
    none_u8().zip(none_u8()).is_none()
}

// ----- inspect ---------------------------------------------------------------

// TODO(closure-by-ref-extraction): `Option::inspect` takes `FnOnce(&T)`;
// Aeneas trips on the borrow with "Region ids should not be visited directly".
// Revisit once closures whose parameter is a reference extract.

// ----- flatten ---------------------------------------------------------------

#[rust_lean_test]
pub fn test_flatten_some_some_zero() -> bool {
    Some(Some(0u8)).flatten().unwrap_or(99) == 0
}

#[rust_lean_test]
pub fn test_flatten_some_some_max() -> bool {
    Some(Some(u8::MAX)).flatten().unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_flatten_some_none() -> bool {
    Some(none_u8()).flatten().is_none()
}

// ----- Default ---------------------------------------------------------------

// TODO(default-trait): testing Default for Option<T> via the model trait requires
// importing the model's Default trait; revisit alongside Default coverage.

// ----------------------------------------------------------------------------
// The four methods below — `is_some`, `is_none`, `unwrap_or`, `take` — are
// listed in `CHARON_EXCLUDES`, so Aeneas does not extract their bodies.
// The Lean side routes through the name map to manually-written
// definitions in `lean/CoreModels/FunsPrologue.lean` / `FunsExternal.lean`.
// The Rust call site looks identical to the extracted variants exercised
// above; the value of having both sections is that one round-trips
// through extraction, the other through the hand-written Lean def.
// ----------------------------------------------------------------------------

use crate::helpers::{none_i32, none_u32};

// ----- is_some (manually defined in Lean, not extracted) --------------------

#[rust_lean_test]
pub fn test_manual_is_some_some_u8_zero() -> bool {
    Some(0u8).is_some() == true
}

#[rust_lean_test]
pub fn test_manual_is_some_some_u8_max() -> bool {
    Some(u8::MAX).is_some() == true
}

#[rust_lean_test]
pub fn test_manual_is_some_none_u8() -> bool {
    none_u8().is_some() == false
}

#[rust_lean_test]
pub fn test_manual_is_some_some_u32() -> bool {
    Some(123u32).is_some() == true
}

#[rust_lean_test]
pub fn test_manual_is_some_none_u32() -> bool {
    none_u32().is_some() == false
}

#[rust_lean_test]
pub fn test_manual_is_some_some_bool() -> bool {
    Some(true).is_some() == true
}

#[rust_lean_test]
pub fn test_manual_is_some_none_bool() -> bool {
    crate::helpers::none_bool().is_some() == false
}

// ----- is_none (manually defined in Lean, not extracted) --------------------

#[rust_lean_test]
pub fn test_manual_is_none_some_u8_zero() -> bool {
    Some(0u8).is_none() == false
}

#[rust_lean_test]
pub fn test_manual_is_none_some_u8_max() -> bool {
    Some(u8::MAX).is_none() == false
}

#[rust_lean_test]
pub fn test_manual_is_none_none_u8() -> bool {
    none_u8().is_none() == true
}

#[rust_lean_test]
pub fn test_manual_is_none_some_i32() -> bool {
    Some(-1i32).is_none() == false
}

#[rust_lean_test]
pub fn test_manual_is_none_none_i32() -> bool {
    none_i32().is_none() == true
}

#[rust_lean_test]
pub fn test_manual_is_none_some_bool() -> bool {
    Some(false).is_none() == false
}

#[rust_lean_test]
pub fn test_manual_is_none_none_bool() -> bool {
    crate::helpers::none_bool().is_none() == true
}

// ----- unwrap_or (manually defined in Lean, not extracted) ------------------

#[rust_lean_test]
pub fn test_manual_unwrap_or_some_u8_zero() -> bool {
    Some(0u8).unwrap_or(42) == 0
}

#[rust_lean_test]
pub fn test_manual_unwrap_or_some_u8_max() -> bool {
    Some(u8::MAX).unwrap_or(0) == u8::MAX
}

#[rust_lean_test]
pub fn test_manual_unwrap_or_none_u8_small_default() -> bool {
    none_u8().unwrap_or(7) == 7
}

#[rust_lean_test]
pub fn test_manual_unwrap_or_none_u8_max_default() -> bool {
    none_u8().unwrap_or(u8::MAX) == u8::MAX
}

#[rust_lean_test]
pub fn test_manual_unwrap_or_some_u32_small() -> bool {
    Some(5u32).unwrap_or(99) == 5
}

#[rust_lean_test]
pub fn test_manual_unwrap_or_none_u32_max_default() -> bool {
    none_u32().unwrap_or(u32::MAX) == u32::MAX
}

#[rust_lean_test]
pub fn test_manual_unwrap_or_some_bool() -> bool {
    Some(true).unwrap_or(false) == true
}

#[rust_lean_test]
pub fn test_manual_unwrap_or_none_bool() -> bool {
    crate::helpers::none_bool().unwrap_or(true) == true
}

// ----- take (manually defined in Lean, not extracted) -----------------------

#[rust_lean_test]
pub fn test_manual_take_some_u8_returns_old() -> bool {
    let mut x: Option<u8> = Some(9);
    let old = x.take();
    old == Some(9)
}

#[rust_lean_test]
pub fn test_manual_take_some_u8_replaces_with_none() -> bool {
    let mut x: Option<u8> = Some(9);
    let _ = x.take();
    x.is_some() == false
}

#[rust_lean_test]
pub fn test_manual_take_some_u8_max_returns_old() -> bool {
    let mut x: Option<u8> = Some(u8::MAX);
    let old = x.take();
    old == Some(u8::MAX) && x.is_none()
}

#[rust_lean_test]
pub fn test_manual_take_none_u8_returns_none() -> bool {
    let mut x: Option<u8> = none_u8();
    let old = x.take();
    old.is_none() && x.is_none()
}

#[rust_lean_test]
pub fn test_manual_take_some_u32() -> bool {
    let mut x: Option<u32> = Some(123);
    let old = x.take();
    old == Some(123) && x.is_none()
}

#[rust_lean_test]
pub fn test_manual_take_none_u32() -> bool {
    let mut x: Option<u32> = none_u32();
    let old = x.take();
    old.is_none() && x.is_none()
}

#[rust_lean_test]
pub fn test_manual_take_some_bool() -> bool {
    let mut x: Option<bool> = Some(true);
    let old = x.take();
    old == Some(true) && x.is_none()
}

// ----- PartialEq: `Option<T> == Option<T>` -----------------------------------

#[rust_lean_test]
pub fn test_option_eq_some_same() -> bool {
    (Some(5u8) == Some(5u8)) == true
}

#[rust_lean_test]
pub fn test_option_eq_some_diff() -> bool {
    (Some(5u8) == Some(6u8)) == false
}

#[rust_lean_test]
pub fn test_option_eq_none_none() -> bool {
    (none_u8() == none_u8()) == true
}

#[rust_lean_test]
pub fn test_option_eq_some_none() -> bool {
    (Some(5u8) == none_u8()) == false
}

#[rust_lean_test]
pub fn test_option_eq_none_some() -> bool {
    (none_u8() == Some(5u8)) == false
}

// ----- and -------------------------------------------------------------------

#[rust_lean_test]
pub fn test_and_some_some() -> bool {
    Some(0u8).and(Some(7u8)).unwrap_or(99) == 7
}

#[rust_lean_test]
pub fn test_and_some_some_max() -> bool {
    Some(u8::MAX).and(Some(0u8)).unwrap_or(99) == 0
}

#[rust_lean_test]
pub fn test_and_some_none() -> bool {
    Some(0u8).and(none_u8()).is_none()
}

#[rust_lean_test]
pub fn test_and_none_some() -> bool {
    none_u8().and(Some(7u8)).is_none()
}

#[rust_lean_test]
pub fn test_and_none_none() -> bool {
    none_u8().and(none_u8()).is_none()
}

// ----- unwrap_unchecked ------------------------------------------------------
// Only the `Some` case is pinned: std's version is undefined behaviour on
// `None`, so there is no agreed answer to compare.

#[rust_lean_test]
pub fn test_unwrap_unchecked_some_zero() -> bool {
    unsafe { Some(0u8).unwrap_unchecked() == 0 }
}

#[rust_lean_test]
pub fn test_unwrap_unchecked_some_max() -> bool {
    unsafe { Some(u8::MAX).unwrap_unchecked() == u8::MAX }
}

#[rust_lean_test]
pub fn test_unwrap_unchecked_some_mid() -> bool {
    unsafe { Some(7u8).unwrap_unchecked() == 7 }
}

// ----- unzip -----------------------------------------------------------------

#[rust_lean_test]
pub fn test_unzip_some_zero() -> bool {
    let (a, b) = Some((0u8, 0u8)).unzip();
    a.unwrap_or(99) == 0 && b.unwrap_or(99) == 0
}

#[rust_lean_test]
pub fn test_unzip_some_edges() -> bool {
    let (a, b) = Some((u8::MAX, 0u8)).unzip();
    a.unwrap_or(0) == u8::MAX && b.unwrap_or(99) == 0
}

#[rust_lean_test]
pub fn test_unzip_none() -> bool {
    let (a, b) = crate::helpers::none_pair_u8().unzip();
    a.is_none() && b.is_none()
}

// ----- transpose -------------------------------------------------------------

// Typed via the return type: `Some(Ok(0))` alone leaves both `Result` params
// unpinned, which Aeneas cannot print.
fn some_ok_u8(v: u8) -> Option<Result<u8, u8>> {
    Some(Ok(v))
}
fn some_err_u8(e: u8) -> Option<Result<u8, u8>> {
    Some(Err(e))
}
fn none_result_u8() -> Option<Result<u8, u8>> {
    let mut x: Option<Result<u8, u8>> = Some(Ok(0));
    x.take();
    x
}

#[rust_lean_test]
pub fn test_transpose_some_ok_zero() -> bool {
    match some_ok_u8(0).transpose() {
        Ok(o) => o.unwrap_or(99) == 0,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_transpose_some_ok_max() -> bool {
    match some_ok_u8(u8::MAX).transpose() {
        Ok(o) => o.unwrap_or(0) == u8::MAX,
        Err(_) => false,
    }
}

#[rust_lean_test]
pub fn test_transpose_some_err() -> bool {
    match some_err_u8(3).transpose() {
        Ok(_) => false,
        Err(e) => e == 3,
    }
}

#[rust_lean_test]
pub fn test_transpose_none() -> bool {
    match none_result_u8().transpose() {
        Ok(o) => o.is_none(),
        Err(_) => false,
    }
}

// ----- iter / iter_mut / into_iter -------------------------------------------

// Rust-only: observing an iterator goes through the `IteratorMethods` surface,
// which does not translate (see `core::iter`).
#[cfg(test)]
mod iterators {
    #[test]
    fn test_iter_some_yields_the_value() {
        let o: Option<u8> = Some(7);
        assert_eq!(o.iter().copied().collect::<Vec<u8>>(), vec![7]);
    }

    #[test]
    fn test_iter_some_zero() {
        let o: Option<u8> = Some(0);
        assert_eq!(o.iter().copied().collect::<Vec<u8>>(), vec![0]);
    }

    #[test]
    fn test_iter_none_is_empty() {
        let o: Option<u8> = None;
        assert!(o.iter().next().is_none());
    }

    #[test]
    fn test_iter_mut_mutates_some() {
        let mut o: Option<u8> = Some(u8::MAX - 1);
        for v in o.iter_mut() {
            *v += 1;
        }
        assert_eq!(o, Some(u8::MAX));
    }

    #[test]
    fn test_iter_mut_none_is_empty() {
        let mut o: Option<u8> = None;
        assert!(o.iter_mut().next().is_none());
        assert_eq!(o, None);
    }

    #[test]
    fn test_into_iter_some() {
        let o: Option<u8> = Some(0);
        assert_eq!(o.into_iter().collect::<Vec<u8>>(), vec![0]);
    }

    #[test]
    fn test_into_iter_none() {
        let o: Option<u8> = None;
        assert_eq!(o.into_iter().collect::<Vec<u8>>(), Vec::<u8>::new());
    }
}

// ----- as_mut / as_slice / as_mut_slice (not extracted) ----------------------

// Rust-only: like `Result::as_mut`, these are `aeneas::exclude`d in the model
// (`as_slice`/`as_mut_slice` additionally need a `&T -> &[T]` primitive neither
// backend has), so no extracted Lean definition exists to guard against.
#[cfg(test)]
mod views {
    #[test]
    fn test_as_mut_some_mutates() {
        let mut o: Option<u8> = Some(0);
        if let Some(v) = o.as_mut() {
            *v = u8::MAX;
        }
        assert_eq!(o, Some(u8::MAX));
    }

    #[test]
    fn test_as_mut_none() {
        let mut o: Option<u8> = None;
        assert!(o.as_mut().is_none());
    }

    #[test]
    fn test_as_slice_some() {
        let o: Option<u8> = Some(7);
        assert_eq!(o.as_slice(), &[7u8]);
    }

    #[test]
    fn test_as_slice_none() {
        let o: Option<u8> = None;
        assert_eq!(o.as_slice(), &[] as &[u8]);
    }

    #[test]
    fn test_as_mut_slice_some() {
        let mut o: Option<u8> = Some(0);
        o.as_mut_slice()[0] = u8::MAX;
        assert_eq!(o, Some(u8::MAX));
    }

    #[test]
    fn test_as_mut_slice_none() {
        let mut o: Option<u8> = None;
        assert!(o.as_mut_slice().is_empty());
    }

    #[test]
    fn test_as_deref_some() {
        let v: u8 = 7;
        let o: Option<&u8> = Some(&v);
        assert_eq!(o.as_deref(), Some(&7u8));
    }

    #[test]
    fn test_as_deref_none() {
        let o: Option<&u8> = None;
        assert!(o.as_deref().is_none());
    }

    #[test]
    fn test_as_deref_mut_some_mutates_through() {
        let mut v: u8 = 0;
        let mut o: Option<&mut u8> = Some(&mut v);
        if let Some(inner) = o.as_deref_mut() {
            *inner = u8::MAX;
        }
        drop(o);
        assert_eq!(v, u8::MAX);
    }

    #[test]
    fn test_cloned_some() {
        let v: u8 = 7;
        let o: Option<&u8> = Some(&v);
        assert_eq!(o.cloned(), Some(7u8));
    }

    #[test]
    fn test_copied_some_and_none() {
        let v: u8 = u8::MAX;
        assert_eq!(Some(&v).copied(), Some(u8::MAX));
        assert_eq!(None::<&u8>.copied(), None);
    }
}

// ----- insert / get_or_insert* / replace / take_if (not extracted) -----------

// Rust-only: the model's versions are pure (they return the updated option
// rather than mutating through `&mut self`), so they are `aeneas::exclude`d —
// an extracted definition would not match a std call site. Same reason `take`
// sits in `CHARON_EXCLUDES`.
#[cfg(test)]
mod insertion {
    #[test]
    fn test_insert_over_none() {
        let mut o: Option<u8> = None;
        assert_eq!(*o.insert(7), 7);
        assert_eq!(o, Some(7));
    }

    #[test]
    fn test_insert_over_some_replaces() {
        let mut o: Option<u8> = Some(0);
        assert_eq!(*o.insert(u8::MAX), u8::MAX);
        assert_eq!(o, Some(u8::MAX));
    }

    #[test]
    fn test_get_or_insert_keeps_some() {
        let mut o: Option<u8> = Some(0);
        assert_eq!(*o.get_or_insert(u8::MAX), 0);
        assert_eq!(o, Some(0));
    }

    #[test]
    fn test_get_or_insert_fills_none() {
        let mut o: Option<u8> = None;
        assert_eq!(*o.get_or_insert(u8::MAX), u8::MAX);
        assert_eq!(o, Some(u8::MAX));
    }

    #[test]
    fn test_get_or_insert_with_fills_none() {
        let mut o: Option<u8> = None;
        assert_eq!(*o.get_or_insert_with(|| 7), 7);
        assert_eq!(o, Some(7));
    }

    #[test]
    fn test_get_or_insert_default_fills_none() {
        let mut o: Option<u8> = None;
        assert_eq!(*o.get_or_insert_default(), 0);
        assert_eq!(o, Some(0));
    }

    #[test]
    fn test_replace_some_returns_old() {
        let mut o: Option<u8> = Some(0);
        assert_eq!(o.replace(u8::MAX), Some(0));
        assert_eq!(o, Some(u8::MAX));
    }

    #[test]
    fn test_replace_none_returns_none() {
        let mut o: Option<u8> = None;
        assert_eq!(o.replace(7), None);
        assert_eq!(o, Some(7));
    }

    #[test]
    fn test_take_if_true_takes() {
        let mut o: Option<u8> = Some(7);
        assert_eq!(o.take_if(|v| *v == 7), Some(7));
        assert_eq!(o, None);
    }

    // A predicate that mutates and answers `false` must leave the mutation behind.
    #[test]
    fn test_take_if_false_keeps_the_mutation() {
        let mut o: Option<u8> = Some(0);
        assert_eq!(
            o.take_if(|v| {
                *v = u8::MAX;
                false
            }),
            None
        );
        assert_eq!(o, Some(u8::MAX));
    }

    #[test]
    fn test_take_if_none() {
        let mut o: Option<u8> = None;
        assert_eq!(o.take_if(|_| true), None);
    }
}

// ----- flatten_ref / flatten_mut / into_flat_iter / zip_with / reduce --------
// ----- get_or_try_insert_with -----------------------------------------------

// No callable std counterpart: all six are unstable in std (`option_reduce`,
// `option_zip`, `option_reference_flattening`, `option_into_flat_iter`,
// `option_get_or_try_insert_with`), so the equivalence tests cannot construct
// the observation from the std side. Their behaviour is pinned by the proptests
// in `core-models/src/core/option.rs`.

// ----- as_pin_ref / as_pin_mut ----------------------------------------------

// Not modeled: both take `self: Pin<&Self>`, and the model has no `core::pin`
// (the `pin` module is at 0% coverage). See COVERAGE.md.
