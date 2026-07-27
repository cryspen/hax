//! Equivalence tests for `[T; N]` (`core::array`) operations.

use rust_lean_test_macro::rust_lean_test;

// ----- Index<RangeTo<usize>> -------------------------------------------------

// TODO(array-eq-literal-extraction: comparing the extracted array to a literal array routes through `core_models.Slice.PartialEqArray.eq` (not in the Lean library).)
/*
#[rust_lean_test]
pub fn test_index_range_to_zero() -> bool {
    let a: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    a[..0] == []
}
*/

// TODO(array-eq-literal-extraction: comparing the extracted array to a literal array routes through `core_models.Slice.PartialEqArray.eq` (not in the Lean library).)
/*
#[rust_lean_test]
pub fn test_index_range_to_three() -> bool {
    let a: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    a[..3] == [1, 2, 3]
}
*/

// TODO(array-eq-literal-extraction: comparing the extracted array to a literal array routes through `core_models.Slice.PartialEqArray.eq` (not in the Lean library).)
/*
#[rust_lean_test]
pub fn test_index_range_to_full() -> bool {
    let a: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    a[..8] == [1, 2, 3, 4, 5, 6, 7, 8]
}
*/

// ----- PartialEq -------------------------------------------------------------

#[rust_lean_test]
pub fn test_eq_same() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let b: [u8; 4] = [1, 2, 3, 4];
    a == b
}

#[rust_lean_test]
pub fn test_eq_different_last() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let b: [u8; 4] = [1, 2, 3, 5];
    (a == b) == false
}

#[rust_lean_test]
pub fn test_eq_different_first() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let b: [u8; 4] = [0, 2, 3, 4];
    (a == b) == false
}

#[rust_lean_test]
pub fn test_eq_all_zeros() -> bool {
    let a: [u8; 4] = [0, 0, 0, 0];
    let b: [u8; 4] = [0, 0, 0, 0];
    a == b
}

#[rust_lean_test]
pub fn test_from_fn_identity() -> bool {
    let a: [u8; 4] = core::array::from_fn(|i| i as u8);
    a == [0, 1, 2, 3]
}

// ----- map / from_fn / each_ref ---------------------------------------------

// TODO: `[T; N]::map` is not defined yet
/* pub fn test_map_add_one() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.map(|x| x + 1) == [2, 3, 4, 5]
} */

// TODO(each-ref-refs): `each_ref` returns `[&T; N]`; arrays of references
// through Aeneas extraction are tricky. Revisit when references-in-arrays
// modelling lands.
/* pub fn test_each_ref_first() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let refs: [&u8; 4] = a.each_ref();
    *refs[0] == 1
} */
