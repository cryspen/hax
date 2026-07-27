//! Equivalence tests for `core::num::*` (integer primitive methods).
//!
//! Mirrors the proptest blocks in `core-models/src/core/num/mod.rs`,
//! which exercise (for each `{u,i}{8,16,32,64,128,size}`):
//!   - `MIN`, `MAX`, `BITS` constants,
//!   - `wrapping_{add,sub,mul}`, `saturating_{add,sub,mul}`,
//!     `overflowing_{add,sub,mul}`,
//!   - `rem_euclid`, `pow`, `count_ones`,
//!   - `rotate_left`, `rotate_right`, `leading_zeros`,
//!   - `from_{be,le}_bytes`, `to_{be,le}_bytes`,
//!   - `checked_div`, `checked_rem`,
//!   - `is_power_of_two` (unsigned), `abs` and `signum` (signed),
//!   - `ilog2`,
//!   - `Default::default()`.
//!
//! We pick a handful of representative widths and a few corner cases
//! per method (zero, MIN, MAX, overflow boundaries, sign flips). The
//! upstream proptest omits `checked_{add,sub,mul}` (see the comment
//! there about `to_int()` stub returning 0); we do the same.

use crate::helpers::{none_i8, none_i16, none_i32, none_u8, none_u16, none_u32};
use rust_lean_test_macro::rust_lean_test;

// =============================================================================
// Constants: MIN / MAX / BITS
// =============================================================================

#[rust_lean_test]
pub fn test_u8_min() -> bool {
    u8::MIN == 0u8
}

#[rust_lean_test]
pub fn test_u8_max() -> bool {
    u8::MAX == 255u8
}

#[rust_lean_test]
pub fn test_u8_bits() -> bool {
    u8::BITS == 8u32
}

#[rust_lean_test]
pub fn test_u16_min() -> bool {
    u16::MIN == 0u16
}

#[rust_lean_test]
pub fn test_u16_max() -> bool {
    u16::MAX == 65535u16
}

#[rust_lean_test]
pub fn test_u16_bits() -> bool {
    u16::BITS == 16u32
}

#[rust_lean_test]
pub fn test_u32_min() -> bool {
    u32::MIN == 0u32
}

#[rust_lean_test]
pub fn test_u32_max() -> bool {
    u32::MAX == 4294967295u32
}

#[rust_lean_test]
pub fn test_u32_bits() -> bool {
    u32::BITS == 32u32
}

#[rust_lean_test]
pub fn test_i8_min() -> bool {
    i8::MIN == -128i8
}

#[rust_lean_test]
pub fn test_i8_max() -> bool {
    i8::MAX == 127i8
}

#[rust_lean_test]
pub fn test_i8_bits() -> bool {
    i8::BITS == 8u32
}

#[rust_lean_test]
pub fn test_i16_min() -> bool {
    i16::MIN == -32768i16
}

#[rust_lean_test]
pub fn test_i16_max() -> bool {
    i16::MAX == 32767i16
}

#[rust_lean_test]
pub fn test_i32_min() -> bool {
    i32::MIN == -2147483648i32
}

#[rust_lean_test]
pub fn test_i32_max() -> bool {
    i32::MAX == 2147483647i32
}

// =============================================================================
// wrapping_add
// =============================================================================

#[rust_lean_test]
pub fn test_u8_wrapping_add_zero() -> bool {
    0u8.wrapping_add(0u8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_add_no_overflow() -> bool {
    100u8.wrapping_add(50u8) == 150u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_add_at_max() -> bool {
    u8::MAX.wrapping_add(1u8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_add_overflow() -> bool {
    200u8.wrapping_add(100u8) == 44u8
}

#[rust_lean_test]
pub fn test_i8_wrapping_add_at_max() -> bool {
    i8::MAX.wrapping_add(1i8) == i8::MIN
}

#[rust_lean_test]
pub fn test_i8_wrapping_add_neg() -> bool {
    (-1i8).wrapping_add(1i8) == 0i8
}

#[rust_lean_test]
pub fn test_u32_wrapping_add_at_max() -> bool {
    u32::MAX.wrapping_add(1u32) == 0u32
}

// =============================================================================
// wrapping_sub
// =============================================================================

#[rust_lean_test]
pub fn test_u8_wrapping_sub_zero() -> bool {
    0u8.wrapping_sub(0u8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_sub_underflow() -> bool {
    0u8.wrapping_sub(1u8) == u8::MAX
}

#[rust_lean_test]
pub fn test_u8_wrapping_sub_no_underflow() -> bool {
    100u8.wrapping_sub(50u8) == 50u8
}

#[rust_lean_test]
pub fn test_i8_wrapping_sub_at_min() -> bool {
    i8::MIN.wrapping_sub(1i8) == i8::MAX
}

#[rust_lean_test]
pub fn test_u32_wrapping_sub_underflow() -> bool {
    0u32.wrapping_sub(1u32) == u32::MAX
}

// =============================================================================
// wrapping_mul
// =============================================================================

#[rust_lean_test]
pub fn test_u8_wrapping_mul_zero() -> bool {
    0u8.wrapping_mul(42u8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_mul_one() -> bool {
    42u8.wrapping_mul(1u8) == 42u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_mul_overflow() -> bool {
    // 16 * 16 == 256 -> wraps to 0
    16u8.wrapping_mul(16u8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_mul_max() -> bool {
    // 255 * 255 == 65025 mod 256 == 1
    u8::MAX.wrapping_mul(u8::MAX) == 1u8
}

#[rust_lean_test]
pub fn test_i8_wrapping_mul_neg() -> bool {
    (-1i8).wrapping_mul(2i8) == -2i8
}

// =============================================================================
// saturating_add
// =============================================================================

#[rust_lean_test]
pub fn test_u8_saturating_add_zero() -> bool {
    0u8.saturating_add(0u8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_saturating_add_no_overflow() -> bool {
    100u8.saturating_add(50u8) == 150u8
}

#[rust_lean_test]
pub fn test_u8_saturating_add_at_max() -> bool {
    u8::MAX.saturating_add(1u8) == u8::MAX
}

#[rust_lean_test]
pub fn test_u8_saturating_add_overflow() -> bool {
    200u8.saturating_add(100u8) == u8::MAX
}

#[rust_lean_test]
pub fn test_i8_saturating_add_at_max() -> bool {
    i8::MAX.saturating_add(1i8) == i8::MAX
}

#[rust_lean_test]
pub fn test_i8_saturating_add_at_min() -> bool {
    i8::MIN.saturating_add(-1i8) == i8::MIN
}

// =============================================================================
// saturating_sub
// =============================================================================

#[rust_lean_test]
pub fn test_u8_saturating_sub_zero() -> bool {
    0u8.saturating_sub(0u8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_saturating_sub_no_underflow() -> bool {
    100u8.saturating_sub(50u8) == 50u8
}

#[rust_lean_test]
pub fn test_u8_saturating_sub_at_min() -> bool {
    0u8.saturating_sub(1u8) == 0u8
}

#[rust_lean_test]
pub fn test_i8_saturating_sub_at_min() -> bool {
    i8::MIN.saturating_sub(1i8) == i8::MIN
}

// =============================================================================
// saturating_mul
// =============================================================================

#[rust_lean_test]
pub fn test_u8_saturating_mul_zero() -> bool {
    0u8.saturating_mul(42u8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_saturating_mul_no_overflow() -> bool {
    10u8.saturating_mul(10u8) == 100u8
}

#[rust_lean_test]
pub fn test_u8_saturating_mul_overflow() -> bool {
    16u8.saturating_mul(16u8) == u8::MAX
}

#[rust_lean_test]
pub fn test_i8_saturating_mul_neg_overflow() -> bool {
    i8::MIN.saturating_mul(2i8) == i8::MIN
}

// =============================================================================
// overflowing_add
// =============================================================================

// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_overflowing_add_zero() -> bool {
    0u8.overflowing_add(0u8) == (0u8, false)
}
*/
*/

// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_overflowing_add_no_overflow() -> bool {
    100u8.overflowing_add(50u8) == (150u8, false)
}
*/
*/

// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_overflowing_add_at_max() -> bool {
    u8::MAX.overflowing_add(1u8) == (0u8, true)
}
*/
*/

// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_overflowing_add_overflow() -> bool {
    200u8.overflowing_add(100u8) == (44u8, true)
}
*/
*/

// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_i8_overflowing_add_at_max() -> bool {
    i8::MAX.overflowing_add(1i8) == (i8::MIN, true)
}
*/
*/

// =============================================================================
// overflowing_sub
// =============================================================================

// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_overflowing_sub_zero() -> bool {
    0u8.overflowing_sub(0u8) == (0u8, false)
}
*/
*/

// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_overflowing_sub_no_underflow() -> bool {
    100u8.overflowing_sub(50u8) == (50u8, false)
}
*/
*/

// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_overflowing_sub_underflow() -> bool {
    0u8.overflowing_sub(1u8) == (u8::MAX, true)
}
*/
*/

// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_i8_overflowing_sub_at_min() -> bool {
    i8::MIN.overflowing_sub(1i8) == (i8::MAX, true)
}
*/
*/

// =============================================================================
// overflowing_mul
// =============================================================================

// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_overflowing_mul_zero() -> bool {
    0u8.overflowing_mul(42u8) == (0u8, false)
}
*/
*/

// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_overflowing_mul_no_overflow() -> bool {
    10u8.overflowing_mul(10u8) == (100u8, false)
}
*/
*/

// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_overflowing_mul_overflow() -> bool {
    16u8.overflowing_mul(16u8) == (0u8, true)
}
*/
*/

// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
// TODO(tuple-eq-extraction: `<T>::overflowing_*` returns `(T, bool)` and our tests compare with `== (_, _)`; `core_models.Pair.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_overflowing_mul_max() -> bool {
    u8::MAX.overflowing_mul(u8::MAX) == (1u8, true)
}
*/
*/

// =============================================================================
// rem_euclid
// =============================================================================

#[rust_lean_test]
pub fn test_u8_rem_euclid_basic() -> bool {
    10u8.rem_euclid(3u8) == 1u8
}

#[rust_lean_test]
pub fn test_u8_rem_euclid_divisible() -> bool {
    12u8.rem_euclid(3u8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_rem_euclid_zero_dividend() -> bool {
    0u8.rem_euclid(5u8) == 0u8
}

#[rust_lean_test]
pub fn test_i8_rem_euclid_pos() -> bool {
    10i8.rem_euclid(3i8) == 1i8
}

#[rust_lean_test]
pub fn test_i8_rem_euclid_neg() -> bool {
    (-7i8).rem_euclid(3i8) == 2i8
}

// =============================================================================
// pow
// =============================================================================

#[rust_lean_test]
pub fn test_u8_pow_zero_exp() -> bool {
    2u8.pow(0u32) == 1u8
}

#[rust_lean_test]
pub fn test_u8_pow_one_exp() -> bool {
    2u8.pow(1u32) == 2u8
}

#[rust_lean_test]
pub fn test_u8_pow_two_exp() -> bool {
    2u8.pow(2u32) == 4u8
}

#[rust_lean_test]
pub fn test_u8_pow_zero_base() -> bool {
    0u8.pow(2u32) == 0u8
}

#[rust_lean_test]
pub fn test_i8_pow_neg_base() -> bool {
    (-2i8).pow(2u32) == 4i8
}

// =============================================================================
// count_ones
// =============================================================================

#[rust_lean_test]
pub fn test_u8_count_ones_zero() -> bool {
    0u8.count_ones() == 0u32
}

#[rust_lean_test]
pub fn test_u8_count_ones_max() -> bool {
    u8::MAX.count_ones() == 8u32
}

#[rust_lean_test]
pub fn test_u8_count_ones_one() -> bool {
    1u8.count_ones() == 1u32
}

#[rust_lean_test]
pub fn test_u8_count_ones_pattern() -> bool {
    // 0b10101010 -> 4
    170u8.count_ones() == 4u32
}

#[rust_lean_test]
pub fn test_u32_count_ones_max() -> bool {
    u32::MAX.count_ones() == 32u32
}

// =============================================================================
// rotate_left / rotate_right
// =============================================================================

#[rust_lean_test]
pub fn test_u8_rotate_left_zero() -> bool {
    0b10000001u8.rotate_left(0u32) == 0b10000001u8
}

#[rust_lean_test]
pub fn test_u8_rotate_left_one() -> bool {
    0b10000001u8.rotate_left(1u32) == 0b00000011u8
}

#[rust_lean_test]
pub fn test_u8_rotate_left_full() -> bool {
    0b10000001u8.rotate_left(8u32) == 0b10000001u8
}

#[rust_lean_test]
pub fn test_u8_rotate_right_zero() -> bool {
    0b10000001u8.rotate_right(0u32) == 0b10000001u8
}

#[rust_lean_test]
pub fn test_u8_rotate_right_one() -> bool {
    0b10000001u8.rotate_right(1u32) == 0b11000000u8
}

#[rust_lean_test]
pub fn test_u8_rotate_right_full() -> bool {
    0b10000001u8.rotate_right(8u32) == 0b10000001u8
}

// =============================================================================
// leading_zeros
// =============================================================================

#[rust_lean_test]
pub fn test_u8_leading_zeros_zero() -> bool {
    0u8.leading_zeros() == 8u32
}

#[rust_lean_test]
pub fn test_u8_leading_zeros_max() -> bool {
    u8::MAX.leading_zeros() == 0u32
}

#[rust_lean_test]
pub fn test_u8_leading_zeros_one() -> bool {
    1u8.leading_zeros() == 7u32
}

#[rust_lean_test]
pub fn test_u32_leading_zeros_max() -> bool {
    u32::MAX.leading_zeros() == 0u32
}

// =============================================================================
// ilog2 (skipped for x == 0; that case panics)
// =============================================================================

#[rust_lean_test]
pub fn test_u8_ilog2_one() -> bool {
    1u8.ilog2() == 0u32
}

#[rust_lean_test]
pub fn test_u8_ilog2_max() -> bool {
    u8::MAX.ilog2() == 7u32
}

#[rust_lean_test]
pub fn test_u8_ilog2_two() -> bool {
    2u8.ilog2() == 1u32
}

#[rust_lean_test]
pub fn test_u32_ilog2_max() -> bool {
    u32::MAX.ilog2() == 31u32
}

// =============================================================================
// is_power_of_two (unsigned only)
// =============================================================================

#[rust_lean_test]
pub fn test_u8_is_power_of_two_zero() -> bool {
    0u8.is_power_of_two() == false
}

#[rust_lean_test]
pub fn test_u8_is_power_of_two_one() -> bool {
    1u8.is_power_of_two() == true
}

#[rust_lean_test]
pub fn test_u8_is_power_of_two_two() -> bool {
    2u8.is_power_of_two() == true
}

#[rust_lean_test]
pub fn test_u8_is_power_of_two_three() -> bool {
    3u8.is_power_of_two() == false
}

#[rust_lean_test]
pub fn test_u8_is_power_of_two_128() -> bool {
    128u8.is_power_of_two() == true
}

#[rust_lean_test]
pub fn test_u8_is_power_of_two_max() -> bool {
    u8::MAX.is_power_of_two() == false
}

// =============================================================================
// abs (signed only)
// =============================================================================

#[rust_lean_test]
pub fn test_i8_abs_zero() -> bool {
    0i8.abs() == 0i8
}

#[rust_lean_test]
pub fn test_i8_abs_pos() -> bool {
    42i8.abs() == 42i8
}

#[rust_lean_test]
pub fn test_i8_abs_neg() -> bool {
    (-42i8).abs() == 42i8
}

#[rust_lean_test]
pub fn test_i8_abs_max() -> bool {
    i8::MAX.abs() == i8::MAX
}

#[rust_lean_test]
pub fn test_i16_abs_neg() -> bool {
    (-100i16).abs() == 100i16
}

// =============================================================================
// signum (signed only)
// =============================================================================

#[rust_lean_test]
pub fn test_i8_signum_zero() -> bool {
    0i8.signum() == 0i8
}

#[rust_lean_test]
pub fn test_i8_signum_pos() -> bool {
    42i8.signum() == 1i8
}

#[rust_lean_test]
pub fn test_i8_signum_neg() -> bool {
    (-42i8).signum() == -1i8
}

#[rust_lean_test]
pub fn test_i8_signum_max() -> bool {
    i8::MAX.signum() == 1i8
}

#[rust_lean_test]
pub fn test_i8_signum_min() -> bool {
    i8::MIN.signum() == -1i8
}

// =============================================================================
// checked_div / checked_rem
// =============================================================================

// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_checked_div_basic() -> bool {
    10u8.checked_div(3u8) == Some(3u8)
}
*/
*/

// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_checked_div_zero_divisor() -> bool {
    10u8.checked_div(0u8) == none_u8()
}
*/
*/

// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_checked_div_zero_dividend() -> bool {
    0u8.checked_div(5u8) == Some(0u8)
}
*/
*/

// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_i8_checked_div_min_by_neg_one() -> bool {
    // i8::MIN / -1 would overflow -> None.
    i8::MIN.checked_div(-1i8) == none_i8()
}
*/
*/

// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_i8_checked_div_zero_divisor() -> bool {
    10i8.checked_div(0i8) == none_i8()
}
*/
*/

// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_checked_rem_basic() -> bool {
    10u8.checked_rem(3u8) == Some(1u8)
}
*/
*/

// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u8_checked_rem_zero_divisor() -> bool {
    10u8.checked_rem(0u8) == none_u8()
}
*/
*/

// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_i8_checked_rem_min_by_neg_one() -> bool {
    i8::MIN.checked_rem(-1i8) == none_i8()
}
*/
*/

// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_i8_checked_rem_zero_divisor() -> bool {
    10i8.checked_rem(0i8) == none_i8()
}
*/
*/

// =============================================================================
// from_be_bytes / from_le_bytes / to_be_bytes / to_le_bytes
// =============================================================================

#[rust_lean_test]
pub fn test_u16_from_be_bytes_basic() -> bool {
    u16::from_be_bytes([0x12, 0x34]) == 0x1234u16
}

#[rust_lean_test]
pub fn test_u16_from_le_bytes_basic() -> bool {
    u16::from_le_bytes([0x34, 0x12]) == 0x1234u16
}

#[rust_lean_test]
pub fn test_u16_from_be_bytes_zero() -> bool {
    u16::from_be_bytes([0u8, 0u8]) == 0u16
}

#[rust_lean_test]
pub fn test_u16_from_be_bytes_max() -> bool {
    u16::from_be_bytes([0xff, 0xff]) == u16::MAX
}

#[rust_lean_test]
pub fn test_u32_from_be_bytes_basic() -> bool {
    u32::from_be_bytes([0x12, 0x34, 0x56, 0x78]) == 0x12345678u32
}

#[rust_lean_test]
pub fn test_u32_from_le_bytes_basic() -> bool {
    u32::from_le_bytes([0x78, 0x56, 0x34, 0x12]) == 0x12345678u32
}

#[rust_lean_test]
pub fn test_u16_to_be_bytes_basic() -> bool {
    0x1234u16.to_be_bytes() == [0x12u8, 0x34u8]
}

#[rust_lean_test]
pub fn test_u16_to_le_bytes_basic() -> bool {
    0x1234u16.to_le_bytes() == [0x34u8, 0x12u8]
}

#[rust_lean_test]
pub fn test_u16_to_be_bytes_zero() -> bool {
    0u16.to_be_bytes() == [0u8, 0u8]
}

#[rust_lean_test]
pub fn test_u16_to_be_bytes_max() -> bool {
    u16::MAX.to_be_bytes() == [0xffu8, 0xffu8]
}

#[rust_lean_test]
pub fn test_u32_to_be_bytes_basic() -> bool {
    0x12345678u32.to_be_bytes() == [0x12u8, 0x34u8, 0x56u8, 0x78u8]
}

#[rust_lean_test]
pub fn test_u32_to_le_bytes_basic() -> bool {
    0x12345678u32.to_le_bytes() == [0x78u8, 0x56u8, 0x34u8, 0x12u8]
}

// =============================================================================
// Default
// =============================================================================

#[rust_lean_test]
pub fn test_u8_default() -> bool {
    <u8 as Default>::default() == 0u8
}

#[rust_lean_test]
pub fn test_u16_default() -> bool {
    <u16 as Default>::default() == 0u16
}

#[rust_lean_test]
pub fn test_u32_default() -> bool {
    <u32 as Default>::default() == 0u32
}

#[rust_lean_test]
pub fn test_i8_default() -> bool {
    <i8 as Default>::default() == 0i8
}

#[rust_lean_test]
pub fn test_i16_default() -> bool {
    <i16 as Default>::default() == 0i16
}

#[rust_lean_test]
pub fn test_i32_default() -> bool {
    <i32 as Default>::default() == 0i32
}

#[rust_lean_test]
pub fn test_bool_default() -> bool {
    <bool as Default>::default() == false
}

// =============================================================================
// Cross-type sanity (suppress unused-import warning in case some specific
// helpers aren't otherwise exercised in this file).
// =============================================================================

// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u16_checked_div_zero() -> bool {
    10u16.checked_div(0u16) == none_u16()
}
*/
*/

// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_u32_checked_div_zero() -> bool {
    10u32.checked_div(0u32) == none_u32()
}
*/
*/

// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_i16_checked_div_zero() -> bool {
    10i16.checked_div(0i16) == none_i16()
}
*/
*/

// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
// TODO(option-eq-extraction: `<T>::checked_*` returns `Option<T>` and our tests compare with `== Some(_)` / `== none_*()`; `core_models.option.Option.PartialEq.eq` is not in the Lean library.)
/*
#[rust_lean_test]
pub fn test_i32_checked_div_zero() -> bool {
    10i32.checked_div(0i32) == none_i32()
}
*/
*/
