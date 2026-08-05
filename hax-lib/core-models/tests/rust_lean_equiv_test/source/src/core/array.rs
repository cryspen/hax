//! Equivalence tests for `[T; N]` (`core::array`) operations.

use rust_lean_test_macro::rust_lean_test;

// ----- Index<RangeTo<usize>> -------------------------------------------------

#[rust_lean_test(
    skip_lean = "Aeneas's `Slice.subslice` requires `start < end`, so an empty subslice fails; needs AeneasVerif/aeneas#1238"
)]
pub fn test_index_range_to_zero() -> bool {
    let a: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    a[..0] == []
}

#[rust_lean_test]
pub fn test_index_range_to_three() -> bool {
    let a: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    a[..3] == [1, 2, 3]
}

#[rust_lean_test]
pub fn test_index_range_to_full() -> bool {
    let a: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    a[..8] == [1, 2, 3, 4, 5, 6, 7, 8]
}

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

// ----- map / each_ref --------------------------------------------------------

#[rust_lean_test]
pub fn test_map_add_one() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    a.map(|x| x + 1) == [2, 3, 4, 5]
}

#[rust_lean_test]
pub fn test_each_ref_first() -> bool {
    let a: [u8; 4] = [1, 2, 3, 4];
    let refs: [&u8; 4] = a.each_ref();
    *refs[0] == 1
}
