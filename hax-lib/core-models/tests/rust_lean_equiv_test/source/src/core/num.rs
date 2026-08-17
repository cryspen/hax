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

#[rust_lean_test]
pub fn test_u8_overflowing_add_zero() -> bool {
    0u8.overflowing_add(0u8) == (0u8, false)
}

#[rust_lean_test]
pub fn test_u8_overflowing_add_no_overflow() -> bool {
    100u8.overflowing_add(50u8) == (150u8, false)
}

#[rust_lean_test]
pub fn test_u8_overflowing_add_at_max() -> bool {
    u8::MAX.overflowing_add(1u8) == (0u8, true)
}

#[rust_lean_test]
pub fn test_u8_overflowing_add_overflow() -> bool {
    200u8.overflowing_add(100u8) == (44u8, true)
}

#[rust_lean_test]
pub fn test_i8_overflowing_add_at_max() -> bool {
    i8::MAX.overflowing_add(1i8) == (i8::MIN, true)
}

// =============================================================================
// overflowing_sub
// =============================================================================

#[rust_lean_test]
pub fn test_u8_overflowing_sub_zero() -> bool {
    0u8.overflowing_sub(0u8) == (0u8, false)
}

#[rust_lean_test]
pub fn test_u8_overflowing_sub_no_underflow() -> bool {
    100u8.overflowing_sub(50u8) == (50u8, false)
}

#[rust_lean_test]
pub fn test_u8_overflowing_sub_underflow() -> bool {
    0u8.overflowing_sub(1u8) == (u8::MAX, true)
}

#[rust_lean_test]
pub fn test_i8_overflowing_sub_at_min() -> bool {
    i8::MIN.overflowing_sub(1i8) == (i8::MAX, true)
}

// =============================================================================
// overflowing_mul
// =============================================================================

#[rust_lean_test]
pub fn test_u8_overflowing_mul_zero() -> bool {
    0u8.overflowing_mul(42u8) == (0u8, false)
}

#[rust_lean_test]
pub fn test_u8_overflowing_mul_no_overflow() -> bool {
    10u8.overflowing_mul(10u8) == (100u8, false)
}

#[rust_lean_test]
pub fn test_u8_overflowing_mul_overflow() -> bool {
    16u8.overflowing_mul(16u8) == (0u8, true)
}

#[rust_lean_test]
pub fn test_u8_overflowing_mul_max() -> bool {
    u8::MAX.overflowing_mul(u8::MAX) == (1u8, true)
}

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
// overflowing_pow
// =============================================================================

#[rust_lean_test]
pub fn test_u8_overflowing_pow_no_overflow() -> bool {
    2u8.overflowing_pow(3u32) == (8u8, false)
}

#[rust_lean_test]
pub fn test_u8_overflowing_pow_overflow() -> bool {
    // 4^4 = 256 wraps to 0.
    4u8.overflowing_pow(4u32) == (0u8, true)
}

#[rust_lean_test]
pub fn test_u8_overflowing_pow_zero_exp() -> bool {
    u8::MAX.overflowing_pow(0u32) == (1u8, false)
}

#[rust_lean_test]
pub fn test_i8_overflowing_pow_neg_base() -> bool {
    (-2i8).overflowing_pow(2u32) == (4i8, false)
}

#[rust_lean_test]
pub fn test_i8_overflowing_pow_overflow() -> bool {
    // (-2)^7 = -128 fits; (-2)^8 = 256 wraps to 0 with overflow.
    (-2i8).overflowing_pow(8u32) == (0i8, true)
}

// =============================================================================
// checked_pow
// =============================================================================

#[rust_lean_test]
pub fn test_u8_checked_pow_basic() -> bool {
    2u8.checked_pow(3u32).unwrap_or(0) == 8u8
}

#[rust_lean_test]
pub fn test_u8_checked_pow_zero_exp() -> bool {
    u8::MAX.checked_pow(0u32).unwrap_or(0) == 1u8
}

#[rust_lean_test]
pub fn test_u8_checked_pow_zero_base() -> bool {
    0u8.checked_pow(3u32).unwrap_or(1) == 0u8
}

#[rust_lean_test]
pub fn test_u8_checked_pow_at_max() -> bool {
    // 2^7 = 128 fits, 2^8 = 256 does not.
    2u8.checked_pow(7u32).unwrap_or(0) == 128u8
}

#[rust_lean_test]
pub fn test_u8_checked_pow_overflow() -> bool {
    2u8.checked_pow(8u32).is_none()
}

#[rust_lean_test]
pub fn test_u8_checked_pow_max_base_overflow() -> bool {
    u8::MAX.checked_pow(2u32).is_none()
}

#[rust_lean_test]
pub fn test_u32_checked_pow_basic() -> bool {
    10u32.checked_pow(9u32).unwrap_or(0) == 1_000_000_000u32
}

#[rust_lean_test]
pub fn test_u32_checked_pow_overflow() -> bool {
    10u32.checked_pow(10u32).is_none()
}

#[rust_lean_test]
pub fn test_i8_checked_pow_neg_base() -> bool {
    (-2i8).checked_pow(2u32).unwrap_or(0) == 4i8
}

#[rust_lean_test]
pub fn test_i8_checked_pow_neg_base_odd_exp() -> bool {
    (-2i8).checked_pow(3u32).unwrap_or(0) == -8i8
}

#[rust_lean_test]
pub fn test_i8_checked_pow_at_min() -> bool {
    // (-2)^7 = -128 = i8::MIN fits exactly.
    (-2i8).checked_pow(7u32).unwrap_or(0) == i8::MIN
}

#[rust_lean_test]
pub fn test_i8_checked_pow_overflow() -> bool {
    // (-2)^8 = 256 > i8::MAX.
    (-2i8).checked_pow(8u32).is_none()
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

#[rust_lean_test]
pub fn test_u8_checked_div_basic() -> bool {
    10u8.checked_div(3u8) == Some(3u8)
}

#[rust_lean_test]
pub fn test_u8_checked_div_zero_divisor() -> bool {
    10u8.checked_div(0u8) == none_u8()
}

#[rust_lean_test]
pub fn test_u8_checked_div_zero_dividend() -> bool {
    0u8.checked_div(5u8) == Some(0u8)
}

#[rust_lean_test]
pub fn test_i8_checked_div_min_by_neg_one() -> bool {
    // i8::MIN / -1 would overflow -> None.
    i8::MIN.checked_div(-1i8) == none_i8()
}

#[rust_lean_test]
pub fn test_i8_checked_div_zero_divisor() -> bool {
    10i8.checked_div(0i8) == none_i8()
}

#[rust_lean_test]
pub fn test_u8_checked_rem_basic() -> bool {
    10u8.checked_rem(3u8) == Some(1u8)
}

#[rust_lean_test]
pub fn test_u8_checked_rem_zero_divisor() -> bool {
    10u8.checked_rem(0u8) == none_u8()
}

#[rust_lean_test]
pub fn test_i8_checked_rem_min_by_neg_one() -> bool {
    i8::MIN.checked_rem(-1i8) == none_i8()
}

#[rust_lean_test]
pub fn test_i8_checked_rem_zero_divisor() -> bool {
    10i8.checked_rem(0i8) == none_i8()
}

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

#[rust_lean_test]
pub fn test_u16_checked_div_zero() -> bool {
    10u16.checked_div(0u16) == none_u16()
}

#[rust_lean_test]
pub fn test_u32_checked_div_zero() -> bool {
    10u32.checked_div(0u32) == none_u32()
}

#[rust_lean_test]
pub fn test_i16_checked_div_zero() -> bool {
    10i16.checked_div(0i16) == none_i16()
}

#[rust_lean_test]
pub fn test_i32_checked_div_zero() -> bool {
    10i32.checked_div(0i32) == none_i32()
}

// =============================================================================
// div_ceil (unsigned)
// =============================================================================
// Unsigned only: std's signed `div_ceil` is unstable (can't be called here); the
// signed model is covered by the `num` proptests.

#[rust_lean_test]
pub fn test_u8_div_ceil_exact() -> bool {
    8u8.div_ceil(4u8) == 2u8
}

#[rust_lean_test]
pub fn test_u8_div_ceil_round_up() -> bool {
    7u8.div_ceil(2u8) == 4u8
}

#[rust_lean_test]
pub fn test_u8_div_ceil_by_one() -> bool {
    200u8.div_ceil(1u8) == 200u8
}

#[rust_lean_test]
pub fn test_u8_div_ceil_zero_dividend() -> bool {
    0u8.div_ceil(7u8) == 0u8
}

#[rust_lean_test]
pub fn test_u32_div_ceil_round_up() -> bool {
    1000u32.div_ceil(3u32) == 334u32
}

// =============================================================================
// is_multiple_of (unsigned)
// =============================================================================

#[rust_lean_test]
pub fn test_u8_is_multiple_of_true() -> bool {
    8u8.is_multiple_of(4u8) == true
}

#[rust_lean_test]
pub fn test_u8_is_multiple_of_false() -> bool {
    7u8.is_multiple_of(4u8) == false
}

#[rust_lean_test]
pub fn test_u8_is_multiple_of_one() -> bool {
    7u8.is_multiple_of(1u8) == true
}

// 0 divides only 0
#[rust_lean_test]
pub fn test_u8_is_multiple_of_zero_rhs_zero() -> bool {
    0u8.is_multiple_of(0u8) == true
}

#[rust_lean_test]
pub fn test_u8_is_multiple_of_zero_rhs_nonzero() -> bool {
    5u8.is_multiple_of(0u8) == false
}

#[rust_lean_test]
pub fn test_u32_is_multiple_of_true() -> bool {
    1000u32.is_multiple_of(8u32) == true
}

// =============================================================================
// min_value / max_value (deprecated aliases of MIN / MAX)
// =============================================================================

#[rust_lean_test]
#[allow(deprecated)]
pub fn test_u8_min_value() -> bool {
    u8::min_value() == 0u8
}

#[rust_lean_test]
#[allow(deprecated)]
pub fn test_u8_max_value() -> bool {
    u8::max_value() == 255u8
}

#[rust_lean_test]
#[allow(deprecated)]
pub fn test_i8_min_value() -> bool {
    i8::min_value() == -128i8
}

#[rust_lean_test]
#[allow(deprecated)]
pub fn test_i8_max_value() -> bool {
    i8::max_value() == 127i8
}

#[rust_lean_test]
#[allow(deprecated)]
pub fn test_u32_max_value() -> bool {
    u32::max_value() == 4294967295u32
}

// =============================================================================
// cast_signed / cast_unsigned
// =============================================================================

#[rust_lean_test]
pub fn test_u8_cast_signed_low() -> bool {
    127u8.cast_signed() == 127i8
}

#[rust_lean_test]
pub fn test_u8_cast_signed_high() -> bool {
    128u8.cast_signed() == -128i8
}

#[rust_lean_test]
pub fn test_u8_cast_signed_max() -> bool {
    255u8.cast_signed() == -1i8
}

#[rust_lean_test]
pub fn test_i8_cast_unsigned_neg() -> bool {
    (-1i8).cast_unsigned() == 255u8
}

#[rust_lean_test]
pub fn test_i8_cast_unsigned_min() -> bool {
    i8::MIN.cast_unsigned() == 128u8
}

#[rust_lean_test]
pub fn test_i32_cast_unsigned_zero() -> bool {
    0i32.cast_unsigned() == 0u32
}

// =============================================================================
// count_zeros
// =============================================================================

#[rust_lean_test]
pub fn test_u8_count_zeros_zero() -> bool {
    0u8.count_zeros() == 8u32
}

#[rust_lean_test]
pub fn test_u8_count_zeros_max() -> bool {
    255u8.count_zeros() == 0u32
}

#[rust_lean_test]
pub fn test_u8_count_zeros_mixed() -> bool {
    0b1010_1010u8.count_zeros() == 4u32
}

#[rust_lean_test]
pub fn test_i8_count_zeros_neg_one() -> bool {
    (-1i8).count_zeros() == 0u32
}

#[rust_lean_test]
pub fn test_i8_count_zeros_min() -> bool {
    i8::MIN.count_zeros() == 7u32
}

#[rust_lean_test]
pub fn test_u32_count_zeros_one() -> bool {
    1u32.count_zeros() == 31u32
}

// =============================================================================
// checked_ilog2
// =============================================================================

#[rust_lean_test]
pub fn test_u8_checked_ilog2_zero() -> bool {
    0u8.checked_ilog2() == none_u32()
}

#[rust_lean_test]
pub fn test_u8_checked_ilog2_one() -> bool {
    1u8.checked_ilog2() == Some(0u32)
}

#[rust_lean_test]
pub fn test_u8_checked_ilog2_max() -> bool {
    255u8.checked_ilog2() == Some(7u32)
}

#[rust_lean_test]
pub fn test_i8_checked_ilog2_negative() -> bool {
    (-1i8).checked_ilog2() == none_u32()
}

#[rust_lean_test]
pub fn test_i8_checked_ilog2_max() -> bool {
    127i8.checked_ilog2() == Some(6u32)
}

// =============================================================================
// wrapping_neg / overflowing_neg / checked_neg / strict_neg
// =============================================================================

#[rust_lean_test]
pub fn test_u8_wrapping_neg_zero() -> bool {
    0u8.wrapping_neg() == 0u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_neg_one() -> bool {
    1u8.wrapping_neg() == 255u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_neg_max() -> bool {
    255u8.wrapping_neg() == 1u8
}

#[rust_lean_test]
pub fn test_i8_wrapping_neg_min() -> bool {
    i8::MIN.wrapping_neg() == i8::MIN
}

#[rust_lean_test]
pub fn test_i8_wrapping_neg_max() -> bool {
    127i8.wrapping_neg() == -127i8
}

#[rust_lean_test]
pub fn test_u8_overflowing_neg_zero() -> bool {
    0u8.overflowing_neg() == (0u8, false)
}

#[rust_lean_test]
pub fn test_u8_overflowing_neg_one() -> bool {
    1u8.overflowing_neg() == (255u8, true)
}

#[rust_lean_test]
pub fn test_i8_overflowing_neg_min() -> bool {
    i8::MIN.overflowing_neg() == (i8::MIN, true)
}

#[rust_lean_test]
pub fn test_i8_overflowing_neg_one() -> bool {
    1i8.overflowing_neg() == (-1i8, false)
}

#[rust_lean_test]
pub fn test_u8_checked_neg_zero() -> bool {
    0u8.checked_neg() == Some(0u8)
}

#[rust_lean_test]
pub fn test_u8_checked_neg_nonzero() -> bool {
    1u8.checked_neg() == none_u8()
}

#[rust_lean_test]
pub fn test_i8_checked_neg_min() -> bool {
    i8::MIN.checked_neg() == none_i8()
}

#[rust_lean_test]
pub fn test_i8_checked_neg_min_plus_one() -> bool {
    (i8::MIN + 1).checked_neg() == Some(127i8)
}

#[rust_lean_test]
pub fn test_u8_strict_neg_zero() -> bool {
    0u8.strict_neg() == 0u8
}

#[rust_lean_test]
pub fn test_i8_strict_neg_max() -> bool {
    127i8.strict_neg() == -127i8
}

#[rust_lean_test]
pub fn test_i8_strict_neg_min_plus_one() -> bool {
    (i8::MIN + 1).strict_neg() == 127i8
}

// =============================================================================
// wrapping_pow / saturating_pow / strict_pow
// =============================================================================

#[rust_lean_test]
pub fn test_u8_wrapping_pow_zero_exp() -> bool {
    200u8.wrapping_pow(0u32) == 1u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_pow_no_overflow() -> bool {
    3u8.wrapping_pow(4u32) == 81u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_pow_overflow() -> bool {
    16u8.wrapping_pow(2u32) == 0u8
}

#[rust_lean_test]
pub fn test_i8_wrapping_pow_negative_base() -> bool {
    (-3i8).wrapping_pow(3u32) == -27i8
}

#[rust_lean_test]
pub fn test_u8_saturating_pow_overflow() -> bool {
    16u8.saturating_pow(2u32) == 255u8
}

#[rust_lean_test]
pub fn test_u8_saturating_pow_exact() -> bool {
    2u8.saturating_pow(7u32) == 128u8
}

#[rust_lean_test]
pub fn test_i8_saturating_pow_negative_odd() -> bool {
    (-3i8).saturating_pow(5u32) == i8::MIN
}

#[rust_lean_test]
pub fn test_i8_saturating_pow_negative_even() -> bool {
    (-3i8).saturating_pow(6u32) == i8::MAX
}

#[rust_lean_test]
pub fn test_u8_strict_pow_zero_exp() -> bool {
    200u8.strict_pow(0u32) == 1u8
}

#[rust_lean_test]
pub fn test_u8_strict_pow_max_fit() -> bool {
    15u8.strict_pow(2u32) == 225u8
}

#[rust_lean_test]
pub fn test_i8_strict_pow_negative() -> bool {
    (-5i8).strict_pow(3u32) == -125i8
}

// =============================================================================
// strict_add / strict_sub / strict_mul
// =============================================================================

#[rust_lean_test]
pub fn test_u8_strict_add_boundary() -> bool {
    254u8.strict_add(1u8) == 255u8
}

#[rust_lean_test]
pub fn test_u8_strict_add_zero() -> bool {
    0u8.strict_add(0u8) == 0u8
}

#[rust_lean_test]
pub fn test_i8_strict_add_to_min() -> bool {
    (-127i8).strict_add(-1i8) == i8::MIN
}

#[rust_lean_test]
pub fn test_u8_strict_sub_to_zero() -> bool {
    5u8.strict_sub(5u8) == 0u8
}

#[rust_lean_test]
pub fn test_i8_strict_sub_to_max() -> bool {
    126i8.strict_sub(-1i8) == 127i8
}

#[rust_lean_test]
pub fn test_u8_strict_mul_boundary() -> bool {
    51u8.strict_mul(5u8) == 255u8
}

#[rust_lean_test]
pub fn test_i8_strict_mul_negative() -> bool {
    (-16i8).strict_mul(8i8) == i8::MIN
}

#[rust_lean_test]
pub fn test_u32_strict_mul_zero() -> bool {
    u32::MAX.strict_mul(0u32) == 0u32
}

// =============================================================================
// wrapping_div / wrapping_rem / wrapping_div_euclid / wrapping_rem_euclid
// =============================================================================

#[rust_lean_test]
pub fn test_u8_wrapping_div() -> bool {
    255u8.wrapping_div(2u8) == 127u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_div_by_one() -> bool {
    0u8.wrapping_div(1u8) == 0u8
}

#[rust_lean_test]
pub fn test_i8_wrapping_div_min_by_neg_one() -> bool {
    i8::MIN.wrapping_div(-1i8) == i8::MIN
}

#[rust_lean_test]
pub fn test_i8_wrapping_div_truncates_towards_zero() -> bool {
    (-7i8).wrapping_div(2i8) == -3i8
}

#[rust_lean_test]
pub fn test_u8_wrapping_rem() -> bool {
    255u8.wrapping_rem(2u8) == 1u8
}

#[rust_lean_test]
pub fn test_i8_wrapping_rem_min_by_neg_one() -> bool {
    i8::MIN.wrapping_rem(-1i8) == 0i8
}

#[rust_lean_test]
pub fn test_i8_wrapping_rem_negative() -> bool {
    (-7i8).wrapping_rem(2i8) == -1i8
}

#[rust_lean_test]
pub fn test_u8_wrapping_div_euclid() -> bool {
    7u8.wrapping_div_euclid(2u8) == 3u8
}

#[rust_lean_test]
pub fn test_i8_wrapping_div_euclid_negative() -> bool {
    (-7i8).wrapping_div_euclid(2i8) == -4i8
}

#[rust_lean_test]
pub fn test_i8_wrapping_div_euclid_min_by_neg_one() -> bool {
    i8::MIN.wrapping_div_euclid(-1i8) == i8::MIN
}

#[rust_lean_test]
pub fn test_u8_wrapping_rem_euclid() -> bool {
    7u8.wrapping_rem_euclid(2u8) == 1u8
}

#[rust_lean_test]
pub fn test_i8_wrapping_rem_euclid_negative() -> bool {
    (-7i8).wrapping_rem_euclid(2i8) == 1i8
}

#[rust_lean_test]
pub fn test_i8_wrapping_rem_euclid_min_by_neg_one() -> bool {
    i8::MIN.wrapping_rem_euclid(-1i8) == 0i8
}

// =============================================================================
// saturating_div
// =============================================================================

#[rust_lean_test]
pub fn test_u8_saturating_div() -> bool {
    255u8.saturating_div(3u8) == 85u8
}

#[rust_lean_test]
pub fn test_i8_saturating_div_min_by_neg_one() -> bool {
    i8::MIN.saturating_div(-1i8) == i8::MAX
}

#[rust_lean_test]
pub fn test_i8_saturating_div_negative() -> bool {
    (-8i8).saturating_div(2i8) == -4i8
}

// =============================================================================
// overflowing_div / overflowing_rem / overflowing_div_euclid / overflowing_rem_euclid
// =============================================================================

#[rust_lean_test]
pub fn test_u8_overflowing_div() -> bool {
    255u8.overflowing_div(2u8) == (127u8, false)
}

#[rust_lean_test]
pub fn test_i8_overflowing_div_min_by_neg_one() -> bool {
    i8::MIN.overflowing_div(-1i8) == (i8::MIN, true)
}

#[rust_lean_test]
pub fn test_i8_overflowing_div_ok() -> bool {
    (-8i8).overflowing_div(2i8) == (-4i8, false)
}

#[rust_lean_test]
pub fn test_u8_overflowing_rem() -> bool {
    255u8.overflowing_rem(2u8) == (1u8, false)
}

#[rust_lean_test]
pub fn test_i8_overflowing_rem_min_by_neg_one() -> bool {
    i8::MIN.overflowing_rem(-1i8) == (0i8, true)
}

#[rust_lean_test]
pub fn test_i8_overflowing_rem_by_neg_one() -> bool {
    7i8.overflowing_rem(-1i8) == (0i8, false)
}

#[rust_lean_test]
pub fn test_u8_overflowing_div_euclid() -> bool {
    7u8.overflowing_div_euclid(2u8) == (3u8, false)
}

#[rust_lean_test]
pub fn test_i8_overflowing_div_euclid_min_by_neg_one() -> bool {
    i8::MIN.overflowing_div_euclid(-1i8) == (i8::MIN, true)
}

#[rust_lean_test]
pub fn test_i8_overflowing_div_euclid_negative() -> bool {
    (-7i8).overflowing_div_euclid(2i8) == (-4i8, false)
}

#[rust_lean_test]
pub fn test_u8_overflowing_rem_euclid() -> bool {
    7u8.overflowing_rem_euclid(2u8) == (1u8, false)
}

#[rust_lean_test]
pub fn test_i8_overflowing_rem_euclid_min_by_neg_one() -> bool {
    i8::MIN.overflowing_rem_euclid(-1i8) == (0i8, true)
}

#[rust_lean_test]
pub fn test_i8_overflowing_rem_euclid_negative() -> bool {
    (-7i8).overflowing_rem_euclid(2i8) == (1i8, false)
}

// =============================================================================
// checked_div_euclid / checked_rem_euclid
// =============================================================================

#[rust_lean_test]
pub fn test_u8_checked_div_euclid_by_zero() -> bool {
    7u8.checked_div_euclid(0u8) == none_u8()
}

#[rust_lean_test]
pub fn test_u8_checked_div_euclid_ok() -> bool {
    7u8.checked_div_euclid(2u8) == Some(3u8)
}

#[rust_lean_test]
pub fn test_i8_checked_div_euclid_min_by_neg_one() -> bool {
    i8::MIN.checked_div_euclid(-1i8) == none_i8()
}

#[rust_lean_test]
pub fn test_i8_checked_div_euclid_negative() -> bool {
    (-7i8).checked_div_euclid(2i8) == Some(-4i8)
}

#[rust_lean_test]
pub fn test_u8_checked_rem_euclid_by_zero() -> bool {
    7u8.checked_rem_euclid(0u8) == none_u8()
}

#[rust_lean_test]
pub fn test_i8_checked_rem_euclid_min_by_neg_one() -> bool {
    i8::MIN.checked_rem_euclid(-1i8) == none_i8()
}

#[rust_lean_test]
pub fn test_i8_checked_rem_euclid_negative() -> bool {
    (-7i8).checked_rem_euclid(2i8) == Some(1i8)
}

// =============================================================================
// div_euclid / div_floor / strict_div / strict_rem / strict_div_euclid / strict_rem_euclid
// =============================================================================

#[rust_lean_test]
pub fn test_u8_div_euclid() -> bool {
    255u8.div_euclid(4u8) == 63u8
}

#[rust_lean_test]
pub fn test_i8_div_euclid_negative_dividend() -> bool {
    (-7i8).div_euclid(2i8) == -4i8
}

#[rust_lean_test]
pub fn test_i8_div_euclid_negative_divisor() -> bool {
    (-7i8).div_euclid(-2i8) == 4i8
}

#[rust_lean_test]
pub fn test_i8_div_euclid_min_by_one() -> bool {
    i8::MIN.div_euclid(1i8) == i8::MIN
}

#[rust_lean_test]
pub fn test_u8_div_floor() -> bool {
    7u8.div_floor(2u8) == 3u8
}

#[rust_lean_test]
pub fn test_i8_div_floor_negative_dividend() -> bool {
    (-7i8).div_floor(2i8) == -4i8
}

#[rust_lean_test]
pub fn test_i8_div_floor_negative_divisor() -> bool {
    7i8.div_floor(-2i8) == -4i8
}

#[rust_lean_test]
pub fn test_i8_div_floor_exact() -> bool {
    (-8i8).div_floor(2i8) == -4i8
}

#[rust_lean_test]
pub fn test_u8_strict_div() -> bool {
    255u8.strict_div(5u8) == 51u8
}

#[rust_lean_test]
pub fn test_i8_strict_div_min_by_one() -> bool {
    i8::MIN.strict_div(1i8) == i8::MIN
}

#[rust_lean_test]
pub fn test_u8_strict_rem() -> bool {
    255u8.strict_rem(4u8) == 3u8
}

#[rust_lean_test]
pub fn test_i8_strict_rem_by_neg_one() -> bool {
    127i8.strict_rem(-1i8) == 0i8
}

#[rust_lean_test]
pub fn test_u8_strict_div_euclid() -> bool {
    7u8.strict_div_euclid(2u8) == 3u8
}

#[rust_lean_test]
pub fn test_i8_strict_div_euclid_negative() -> bool {
    (-7i8).strict_div_euclid(2i8) == -4i8
}

#[rust_lean_test]
pub fn test_u8_strict_rem_euclid() -> bool {
    7u8.strict_rem_euclid(2u8) == 1u8
}

#[rust_lean_test]
pub fn test_i8_strict_rem_euclid_negative() -> bool {
    (-7i8).strict_rem_euclid(2i8) == 1i8
}

// =============================================================================
// abs_diff / midpoint
// =============================================================================

#[rust_lean_test]
pub fn test_u8_abs_diff_larger_first() -> bool {
    255u8.abs_diff(1u8) == 254u8
}

#[rust_lean_test]
pub fn test_u8_abs_diff_smaller_first() -> bool {
    1u8.abs_diff(255u8) == 254u8
}

#[rust_lean_test]
pub fn test_u8_abs_diff_equal() -> bool {
    7u8.abs_diff(7u8) == 0u8
}

#[rust_lean_test]
pub fn test_i8_abs_diff_extremes() -> bool {
    i8::MIN.abs_diff(i8::MAX) == 255u8
}

#[rust_lean_test]
pub fn test_i8_abs_diff_negatives() -> bool {
    (-5i8).abs_diff(-2i8) == 3u8
}

#[rust_lean_test]
pub fn test_u8_midpoint_max() -> bool {
    255u8.midpoint(255u8) == 255u8
}

#[rust_lean_test]
pub fn test_u8_midpoint_rounds_down() -> bool {
    255u8.midpoint(254u8) == 254u8
}

#[rust_lean_test]
pub fn test_u8_midpoint_zero() -> bool {
    0u8.midpoint(0u8) == 0u8
}

#[rust_lean_test]
pub fn test_i8_midpoint_extremes() -> bool {
    i8::MIN.midpoint(i8::MAX) == 0i8
}

#[rust_lean_test]
pub fn test_i8_midpoint_negative_odd_sum() -> bool {
    (-7i8).midpoint(2i8) == -2i8
}

#[rust_lean_test]
pub fn test_i8_midpoint_min_min() -> bool {
    i8::MIN.midpoint(i8::MIN) == i8::MIN
}

// =============================================================================
// next_multiple_of (unsigned) / checked_next_multiple_of
// =============================================================================

#[rust_lean_test]
pub fn test_u8_next_multiple_of_exact() -> bool {
    8u8.next_multiple_of(4u8) == 8u8
}

#[rust_lean_test]
pub fn test_u8_next_multiple_of_rounds_up() -> bool {
    7u8.next_multiple_of(4u8) == 8u8
}

#[rust_lean_test]
pub fn test_u8_next_multiple_of_zero() -> bool {
    0u8.next_multiple_of(5u8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_next_multiple_of_max_exact() -> bool {
    255u8.next_multiple_of(5u8) == 255u8
}

#[rust_lean_test]
pub fn test_u8_checked_next_multiple_of_overflow() -> bool {
    255u8.checked_next_multiple_of(4u8) == none_u8()
}

#[rust_lean_test]
pub fn test_u8_checked_next_multiple_of_by_zero() -> bool {
    7u8.checked_next_multiple_of(0u8) == none_u8()
}

#[rust_lean_test]
pub fn test_u8_checked_next_multiple_of_ok() -> bool {
    7u8.checked_next_multiple_of(4u8) == Some(8u8)
}

#[rust_lean_test]
pub fn test_i8_checked_next_multiple_of_neg_one() -> bool {
    i8::MIN.checked_next_multiple_of(-1i8) == Some(i8::MIN)
}

#[rust_lean_test]
pub fn test_i8_checked_next_multiple_of_negative_rhs() -> bool {
    5i8.checked_next_multiple_of(-3i8) == Some(3i8)
}

#[rust_lean_test]
pub fn test_i8_checked_next_multiple_of_overflow() -> bool {
    127i8.checked_next_multiple_of(4i8) == none_i8()
}

// =============================================================================
// checked_signed_diff (unsigned)
// =============================================================================

#[rust_lean_test]
pub fn test_u8_checked_signed_diff_positive() -> bool {
    10u8.checked_signed_diff(3u8) == Some(7i8)
}

#[rust_lean_test]
pub fn test_u8_checked_signed_diff_negative() -> bool {
    3u8.checked_signed_diff(10u8) == Some(-7i8)
}

#[rust_lean_test]
pub fn test_u8_checked_signed_diff_overflow() -> bool {
    255u8.checked_signed_diff(0u8) == none_i8()
}

#[rust_lean_test]
pub fn test_u8_checked_signed_diff_min_boundary() -> bool {
    0u8.checked_signed_diff(128u8) == Some(i8::MIN)
}

// =============================================================================
// unsigned + signed argument: {wrapping,overflowing,saturating,checked,strict}_{add,sub}_signed
// =============================================================================

#[rust_lean_test]
pub fn test_u8_wrapping_add_signed_negative() -> bool {
    0u8.wrapping_add_signed(-1i8) == 255u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_add_signed_positive() -> bool {
    255u8.wrapping_add_signed(1i8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_sub_signed_negative() -> bool {
    255u8.wrapping_sub_signed(-1i8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_overflowing_add_signed_no_overflow() -> bool {
    10u8.overflowing_add_signed(-5i8) == (5u8, false)
}

#[rust_lean_test]
pub fn test_u8_overflowing_add_signed_underflow() -> bool {
    0u8.overflowing_add_signed(-1i8) == (255u8, true)
}

#[rust_lean_test]
pub fn test_u8_overflowing_sub_signed_overflow() -> bool {
    255u8.overflowing_sub_signed(-1i8) == (0u8, true)
}

#[rust_lean_test]
pub fn test_u8_saturating_add_signed_saturates_low() -> bool {
    0u8.saturating_add_signed(-1i8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_saturating_add_signed_saturates_high() -> bool {
    255u8.saturating_add_signed(127i8) == 255u8
}

#[rust_lean_test]
pub fn test_u8_saturating_sub_signed_saturates_high() -> bool {
    255u8.saturating_sub_signed(i8::MIN) == 255u8
}

#[rust_lean_test]
pub fn test_u8_saturating_sub_signed_saturates_low() -> bool {
    0u8.saturating_sub_signed(1i8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_checked_add_signed_none() -> bool {
    0u8.checked_add_signed(-1i8) == none_u8()
}

#[rust_lean_test]
pub fn test_u8_checked_add_signed_some() -> bool {
    10u8.checked_add_signed(-10i8) == Some(0u8)
}

#[rust_lean_test]
pub fn test_u8_checked_sub_signed_none() -> bool {
    255u8.checked_sub_signed(-1i8) == none_u8()
}

#[rust_lean_test]
pub fn test_u8_strict_add_signed_ok() -> bool {
    1u8.strict_add_signed(-1i8) == 0u8
}

#[rust_lean_test]
pub fn test_u8_strict_sub_signed_ok() -> bool {
    254u8.strict_sub_signed(-1i8) == 255u8
}

// =============================================================================
// signed + unsigned argument: {wrapping,overflowing,saturating,strict}_{add,sub}_unsigned
// =============================================================================

#[rust_lean_test]
pub fn test_i8_wrapping_add_unsigned_wraps() -> bool {
    127i8.wrapping_add_unsigned(1u8) == i8::MIN
}

#[rust_lean_test]
pub fn test_i8_wrapping_add_unsigned_large() -> bool {
    0i8.wrapping_add_unsigned(255u8) == -1i8
}

#[rust_lean_test]
pub fn test_i8_wrapping_sub_unsigned_wraps() -> bool {
    i8::MIN.wrapping_sub_unsigned(1u8) == 127i8
}

#[rust_lean_test]
pub fn test_i8_overflowing_add_unsigned_overflow() -> bool {
    127i8.overflowing_add_unsigned(1u8) == (i8::MIN, true)
}

#[rust_lean_test]
pub fn test_i8_overflowing_add_unsigned_ok() -> bool {
    (-1i8).overflowing_add_unsigned(1u8) == (0i8, false)
}

#[rust_lean_test]
pub fn test_i8_overflowing_sub_unsigned_overflow() -> bool {
    i8::MIN.overflowing_sub_unsigned(1u8) == (127i8, true)
}

#[rust_lean_test]
pub fn test_i8_saturating_add_unsigned_saturates() -> bool {
    0i8.saturating_add_unsigned(255u8) == 127i8
}

#[rust_lean_test]
pub fn test_i8_saturating_sub_unsigned_saturates() -> bool {
    0i8.saturating_sub_unsigned(255u8) == i8::MIN
}

#[rust_lean_test]
pub fn test_i8_strict_add_unsigned_ok() -> bool {
    126i8.strict_add_unsigned(1u8) == 127i8
}

#[rust_lean_test]
pub fn test_i8_strict_sub_unsigned_ok() -> bool {
    (-127i8).strict_sub_unsigned(1u8) == i8::MIN
}

// =============================================================================
// abs family (signed): wrapping_abs / overflowing_abs / checked_abs /
// saturating_abs / unsigned_abs / saturating_neg
// =============================================================================

#[rust_lean_test]
pub fn test_i8_wrapping_abs_min() -> bool {
    i8::MIN.wrapping_abs() == i8::MIN
}

#[rust_lean_test]
pub fn test_i8_wrapping_abs_negative() -> bool {
    (-7i8).wrapping_abs() == 7i8
}

#[rust_lean_test]
pub fn test_i8_wrapping_abs_positive() -> bool {
    7i8.wrapping_abs() == 7i8
}

#[rust_lean_test]
pub fn test_i8_overflowing_abs_min() -> bool {
    i8::MIN.overflowing_abs() == (i8::MIN, true)
}

#[rust_lean_test]
pub fn test_i8_overflowing_abs_ok() -> bool {
    (-7i8).overflowing_abs() == (7i8, false)
}

#[rust_lean_test]
pub fn test_i8_checked_abs_min() -> bool {
    i8::MIN.checked_abs() == none_i8()
}

#[rust_lean_test]
pub fn test_i8_checked_abs_ok() -> bool {
    (-7i8).checked_abs() == Some(7i8)
}

#[rust_lean_test]
pub fn test_i8_saturating_abs_min() -> bool {
    i8::MIN.saturating_abs() == 127i8
}

#[rust_lean_test]
pub fn test_i8_saturating_abs_ok() -> bool {
    (-7i8).saturating_abs() == 7i8
}

#[rust_lean_test]
pub fn test_i8_unsigned_abs_min() -> bool {
    i8::MIN.unsigned_abs() == 128u8
}

#[rust_lean_test]
pub fn test_i8_unsigned_abs_negative() -> bool {
    (-7i8).unsigned_abs() == 7u8
}

#[rust_lean_test]
pub fn test_i8_unsigned_abs_zero() -> bool {
    0i8.unsigned_abs() == 0u8
}

#[rust_lean_test]
pub fn test_i8_saturating_neg_min() -> bool {
    i8::MIN.saturating_neg() == 127i8
}

#[rust_lean_test]
pub fn test_i8_saturating_neg_ok() -> bool {
    7i8.saturating_neg() == -7i8
}

#[rust_lean_test]
pub fn test_i8_strict_abs_ok() -> bool {
    (-127i8).strict_abs() == 127i8
}

// =============================================================================
// is_positive / is_negative (signed)
// =============================================================================

#[rust_lean_test]
pub fn test_i8_is_positive_zero() -> bool {
    0i8.is_positive() == false
}

#[rust_lean_test]
pub fn test_i8_is_positive_max() -> bool {
    127i8.is_positive() == true
}

#[rust_lean_test]
pub fn test_i8_is_negative_min() -> bool {
    i8::MIN.is_negative() == true
}

#[rust_lean_test]
pub fn test_i8_is_negative_zero() -> bool {
    0i8.is_negative() == false
}

#[rust_lean_test]
pub fn test_i32_is_negative_neg_one() -> bool {
    (-1i32).is_negative() == true
}

// =============================================================================
// usize / isize spot checks
// =============================================================================

#[rust_lean_test]
pub fn test_usize_wrapping_neg_one() -> bool {
    1usize.wrapping_neg() == usize::MAX
}

#[rust_lean_test]
pub fn test_usize_abs_diff() -> bool {
    3usize.abs_diff(10usize) == 7usize
}

#[rust_lean_test]
pub fn test_usize_midpoint() -> bool {
    usize::MAX.midpoint(usize::MAX) == usize::MAX
}

#[rust_lean_test]
pub fn test_isize_div_euclid_negative() -> bool {
    (-7isize).div_euclid(2isize) == -4isize
}

#[rust_lean_test]
pub fn test_isize_unsigned_abs_min() -> bool {
    isize::MIN.unsigned_abs() == 9223372036854775808usize
}

#[rust_lean_test]
pub fn test_usize_count_zeros_zero() -> bool {
    0usize.count_zeros() == 64u32
}

// =============================================================================
// trailing_zeros / trailing_ones / leading_ones
// =============================================================================

#[rust_lean_test]
pub fn test_u8_trailing_zeros_zero() -> bool {
    0u8.trailing_zeros() == 8u32
}

#[rust_lean_test]
pub fn test_u8_trailing_zeros_one() -> bool {
    1u8.trailing_zeros() == 0u32
}

#[rust_lean_test]
pub fn test_u8_trailing_zeros_top_bit() -> bool {
    128u8.trailing_zeros() == 7u32
}

#[rust_lean_test]
pub fn test_i8_trailing_zeros_min() -> bool {
    i8::MIN.trailing_zeros() == 7u32
}

#[rust_lean_test]
pub fn test_i8_trailing_zeros_neg_one() -> bool {
    (-1i8).trailing_zeros() == 0u32
}

#[rust_lean_test]
pub fn test_u8_trailing_ones_max() -> bool {
    255u8.trailing_ones() == 8u32
}

#[rust_lean_test]
pub fn test_u8_trailing_ones_zero() -> bool {
    0u8.trailing_ones() == 0u32
}

#[rust_lean_test]
pub fn test_i8_trailing_ones_neg_one() -> bool {
    (-1i8).trailing_ones() == 8u32
}

#[rust_lean_test]
pub fn test_u8_leading_ones_max() -> bool {
    255u8.leading_ones() == 8u32
}

#[rust_lean_test]
pub fn test_u8_leading_ones_zero() -> bool {
    0u8.leading_ones() == 0u32
}

#[rust_lean_test]
pub fn test_i8_leading_ones_min() -> bool {
    i8::MIN.leading_ones() == 1u32
}

#[rust_lean_test]
pub fn test_u32_trailing_zeros_power_of_two() -> bool {
    65536u32.trailing_zeros() == 16u32
}

// =============================================================================
// lowest_one / highest_one / isolate_lowest_one / isolate_highest_one
// =============================================================================

#[rust_lean_test]
pub fn test_u8_lowest_one_zero() -> bool {
    0u8.lowest_one() == none_u32()
}

#[rust_lean_test]
pub fn test_u8_lowest_one_twelve() -> bool {
    12u8.lowest_one() == Some(2u32)
}

#[rust_lean_test]
pub fn test_u8_highest_one_zero() -> bool {
    0u8.highest_one() == none_u32()
}

#[rust_lean_test]
pub fn test_u8_highest_one_max() -> bool {
    255u8.highest_one() == Some(7u32)
}

#[rust_lean_test]
pub fn test_i8_highest_one_neg_one() -> bool {
    (-1i8).highest_one() == Some(7u32)
}

#[rust_lean_test]
pub fn test_i8_lowest_one_min() -> bool {
    i8::MIN.lowest_one() == Some(7u32)
}

#[rust_lean_test]
pub fn test_u8_isolate_lowest_one_twelve() -> bool {
    12u8.isolate_lowest_one() == 4u8
}

#[rust_lean_test]
pub fn test_u8_isolate_lowest_one_zero() -> bool {
    0u8.isolate_lowest_one() == 0u8
}

#[rust_lean_test]
pub fn test_u8_isolate_highest_one_mixed() -> bool {
    0x60u8.isolate_highest_one() == 0x40u8
}

#[rust_lean_test]
pub fn test_u8_isolate_highest_one_zero() -> bool {
    0u8.isolate_highest_one() == 0u8
}

#[rust_lean_test]
pub fn test_i8_isolate_highest_one_neg_one() -> bool {
    (-1i8).isolate_highest_one() == i8::MIN
}

#[rust_lean_test]
pub fn test_i8_isolate_lowest_one_min() -> bool {
    i8::MIN.isolate_lowest_one() == i8::MIN
}

// =============================================================================
// bit_width (unsigned)
// =============================================================================

#[rust_lean_test]
pub fn test_u8_bit_width_zero() -> bool {
    0u8.bit_width() == 0u32
}

#[rust_lean_test]
pub fn test_u8_bit_width_one() -> bool {
    1u8.bit_width() == 1u32
}

#[rust_lean_test]
pub fn test_u8_bit_width_max() -> bool {
    255u8.bit_width() == 8u32
}

#[rust_lean_test]
pub fn test_u32_bit_width_power_of_two() -> bool {
    256u32.bit_width() == 9u32
}

// =============================================================================
// swap_bytes / to_be / to_le / from_be / from_le / to_ne_bytes / from_ne_bytes
// =============================================================================
// The model fixes a little-endian target, so `to_le`/`from_le` are the identity
// and `to_be`/`from_be`/`swap_bytes` all reverse the bytes.

#[rust_lean_test]
pub fn test_u8_swap_bytes_identity() -> bool {
    200u8.swap_bytes() == 200u8
}

#[rust_lean_test]
pub fn test_u16_swap_bytes() -> bool {
    0x1234u16.swap_bytes() == 0x3412u16
}

#[rust_lean_test]
pub fn test_u32_swap_bytes() -> bool {
    0x12345678u32.swap_bytes() == 0x78563412u32
}

#[rust_lean_test]
pub fn test_u16_swap_bytes_max() -> bool {
    u16::MAX.swap_bytes() == u16::MAX
}

#[rust_lean_test]
pub fn test_i16_swap_bytes_neg_one() -> bool {
    (-1i16).swap_bytes() == -1i16
}

#[rust_lean_test]
pub fn test_i16_swap_bytes_min() -> bool {
    i16::MIN.swap_bytes() == 128i16
}

#[rust_lean_test]
pub fn test_u16_to_be() -> bool {
    0x1234u16.to_be() == 0x3412u16
}

#[rust_lean_test]
pub fn test_u16_to_le() -> bool {
    0x1234u16.to_le() == 0x1234u16
}

#[rust_lean_test]
pub fn test_u16_from_be() -> bool {
    u16::from_be(0x1234u16) == 0x3412u16
}

#[rust_lean_test]
pub fn test_u16_from_le() -> bool {
    u16::from_le(0x1234u16) == 0x1234u16
}

#[rust_lean_test]
pub fn test_i32_to_be_zero() -> bool {
    0i32.to_be() == 0i32
}

#[rust_lean_test]
pub fn test_u16_to_ne_bytes() -> bool {
    0x1234u16.to_ne_bytes() == [0x34u8, 0x12u8]
}

#[rust_lean_test]
pub fn test_u16_from_ne_bytes() -> bool {
    u16::from_ne_bytes([0x34u8, 0x12u8]) == 0x1234u16
}

#[rust_lean_test]
pub fn test_u8_to_ne_bytes() -> bool {
    255u8.to_ne_bytes() == [255u8]
}

#[rust_lean_test]
pub fn test_i16_from_ne_bytes_neg_one() -> bool {
    i16::from_ne_bytes([0xffu8, 0xffu8]) == -1i16
}

// =============================================================================
// wrapping_shl / wrapping_shr / overflowing_shl / overflowing_shr
// =============================================================================

#[rust_lean_test]
pub fn test_u8_wrapping_shl_zero() -> bool {
    1u8.wrapping_shl(0u32) == 1u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_shl_last_bit() -> bool {
    1u8.wrapping_shl(7u32) == 128u8
}

// The shift count is taken modulo `BITS`, so `BITS` behaves like `0`.
#[rust_lean_test]
pub fn test_u8_wrapping_shl_bits() -> bool {
    1u8.wrapping_shl(8u32) == 1u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_shr_bits() -> bool {
    128u8.wrapping_shr(8u32) == 128u8
}

#[rust_lean_test]
pub fn test_i8_wrapping_shr_sign_extends() -> bool {
    (-8i8).wrapping_shr(1u32) == -4i8
}

#[rust_lean_test]
pub fn test_i8_wrapping_shl_min() -> bool {
    1i8.wrapping_shl(7u32) == i8::MIN
}

#[rust_lean_test]
pub fn test_u8_overflowing_shl_in_range() -> bool {
    1u8.overflowing_shl(7u32) == (128u8, false)
}

#[rust_lean_test]
pub fn test_u8_overflowing_shl_out_of_range() -> bool {
    1u8.overflowing_shl(8u32) == (1u8, true)
}

#[rust_lean_test]
pub fn test_u8_overflowing_shr_out_of_range() -> bool {
    128u8.overflowing_shr(8u32) == (128u8, true)
}

#[rust_lean_test]
pub fn test_i8_overflowing_shr_in_range() -> bool {
    (-8i8).overflowing_shr(1u32) == (-4i8, false)
}

// =============================================================================
// checked_shl / checked_shr / strict_shl / strict_shr
// =============================================================================

#[rust_lean_test]
pub fn test_u8_checked_shl_in_range() -> bool {
    1u8.checked_shl(7u32) == Some(128u8)
}

#[rust_lean_test]
pub fn test_u8_checked_shl_out_of_range() -> bool {
    1u8.checked_shl(8u32) == none_u8()
}

#[rust_lean_test]
pub fn test_u8_checked_shr_out_of_range() -> bool {
    128u8.checked_shr(8u32) == none_u8()
}

#[rust_lean_test]
pub fn test_i8_checked_shr_in_range() -> bool {
    (-8i8).checked_shr(1u32) == Some(-4i8)
}

#[rust_lean_test]
pub fn test_u8_strict_shl_zero() -> bool {
    1u8.strict_shl(0u32) == 1u8
}

#[rust_lean_test]
pub fn test_u8_strict_shl_last_bit() -> bool {
    1u8.strict_shl(7u32) == 128u8
}

#[rust_lean_test]
pub fn test_i8_strict_shr_last_bit() -> bool {
    i8::MIN.strict_shr(7u32) == -1i8
}

// =============================================================================
// unbounded_shl / unbounded_shr
// =============================================================================

#[rust_lean_test]
pub fn test_u8_unbounded_shl_in_range() -> bool {
    1u8.unbounded_shl(7u32) == 128u8
}

#[rust_lean_test]
pub fn test_u8_unbounded_shl_out_of_range() -> bool {
    255u8.unbounded_shl(8u32) == 0u8
}

#[rust_lean_test]
pub fn test_u8_unbounded_shr_out_of_range() -> bool {
    255u8.unbounded_shr(100u32) == 0u8
}

// A signed right shift fills with the sign bit, so shifting all the way out
// leaves -1 for a negative value and 0 for a non-negative one.
#[rust_lean_test]
pub fn test_i8_unbounded_shr_negative_out_of_range() -> bool {
    (-8i8).unbounded_shr(100u32) == -1i8
}

#[rust_lean_test]
pub fn test_i8_unbounded_shr_positive_out_of_range() -> bool {
    8i8.unbounded_shr(100u32) == 0i8
}

#[rust_lean_test]
pub fn test_i8_unbounded_shl_out_of_range() -> bool {
    (-1i8).unbounded_shl(8u32) == 0i8
}

// =============================================================================
// unchecked_shl / unchecked_shr
// =============================================================================

#[rust_lean_test]
pub fn test_u8_unchecked_shl() -> bool {
    unsafe { 1u8.unchecked_shl(7u32) == 128u8 }
}

#[rust_lean_test]
pub fn test_u8_unchecked_shr() -> bool {
    unsafe { 128u8.unchecked_shr(7u32) == 1u8 }
}

#[rust_lean_test]
pub fn test_i8_unchecked_shr_sign_extends() -> bool {
    unsafe { i8::MIN.unchecked_shr(7u32) == -1i8 }
}

// =============================================================================
// funnel_shl / funnel_shr (unsigned)
// =============================================================================

#[rust_lean_test]
pub fn test_u8_funnel_shl_zero_shift() -> bool {
    0xF0u8.funnel_shl(0x0Fu8, 0u32) == 0xF0u8
}

#[rust_lean_test]
pub fn test_u8_funnel_shl_four() -> bool {
    0xF0u8.funnel_shl(0x0Fu8, 4u32) == 0x00u8
}

#[rust_lean_test]
pub fn test_u8_funnel_shl_mixes_halves() -> bool {
    0x0Fu8.funnel_shl(0xF0u8, 4u32) == 0xFFu8
}

#[rust_lean_test]
pub fn test_u8_funnel_shr_zero_shift() -> bool {
    0xF0u8.funnel_shr(0x0Fu8, 0u32) == 0x0Fu8
}

#[rust_lean_test]
pub fn test_u8_funnel_shr_four() -> bool {
    0x0Fu8.funnel_shr(0xF0u8, 4u32) == 0xFFu8
}

#[rust_lean_test]
pub fn test_u8_funnel_shl_last() -> bool {
    0x01u8.funnel_shl(0x80u8, 7u32) == 0xC0u8
}

// =============================================================================
// unchecked_disjoint_bitor (unsigned)
// =============================================================================

#[rust_lean_test]
pub fn test_u8_unchecked_disjoint_bitor_halves() -> bool {
    unsafe { 0xF0u8.unchecked_disjoint_bitor(0x0Fu8) == 0xFFu8 }
}

#[rust_lean_test]
pub fn test_u8_unchecked_disjoint_bitor_zero() -> bool {
    unsafe { 0u8.unchecked_disjoint_bitor(0u8) == 0u8 }
}

#[rust_lean_test]
pub fn test_u8_unchecked_disjoint_bitor_max() -> bool {
    unsafe { 255u8.unchecked_disjoint_bitor(0u8) == 255u8 }
}

// =============================================================================
// next_power_of_two / checked_next_power_of_two / wrapping_next_power_of_two
// =============================================================================

#[rust_lean_test]
pub fn test_u8_next_power_of_two_zero() -> bool {
    0u8.next_power_of_two() == 1u8
}

#[rust_lean_test]
pub fn test_u8_next_power_of_two_one() -> bool {
    1u8.next_power_of_two() == 1u8
}

#[rust_lean_test]
pub fn test_u8_next_power_of_two_three() -> bool {
    3u8.next_power_of_two() == 4u8
}

#[rust_lean_test]
pub fn test_u8_next_power_of_two_largest() -> bool {
    128u8.next_power_of_two() == 128u8
}

#[rust_lean_test]
pub fn test_u8_checked_next_power_of_two_overflow() -> bool {
    129u8.checked_next_power_of_two() == none_u8()
}

#[rust_lean_test]
pub fn test_u8_checked_next_power_of_two_max() -> bool {
    255u8.checked_next_power_of_two() == none_u8()
}

#[rust_lean_test]
pub fn test_u8_checked_next_power_of_two_ok() -> bool {
    5u8.checked_next_power_of_two() == Some(8u8)
}

#[rust_lean_test]
pub fn test_u8_wrapping_next_power_of_two_overflow() -> bool {
    200u8.wrapping_next_power_of_two() == 0u8
}

#[rust_lean_test]
pub fn test_u8_wrapping_next_power_of_two_zero() -> bool {
    0u8.wrapping_next_power_of_two() == 1u8
}

#[rust_lean_test]
pub fn test_u32_next_power_of_two() -> bool {
    1000u32.next_power_of_two() == 1024u32
}

// =============================================================================
// shl_exact / shr_exact / unchecked_shl_exact / unchecked_shr_exact
// =============================================================================
// TODO(toolchain): the pinned toolchain (nightly-2025-11-08) has no
// `sh{l,r}_exact`/`unchecked_sh{l,r}_exact` on the integer primitives, so there
// is nothing to call here. The model's behaviour is pinned by the proptests in
// `core-models/src/core/num/mod.rs` instead.

// =============================================================================
// usize / isize bit-level spot checks
// =============================================================================

#[rust_lean_test]
pub fn test_usize_trailing_zeros_zero() -> bool {
    0usize.trailing_zeros() == 64u32
}

#[rust_lean_test]
pub fn test_usize_bit_width_max() -> bool {
    usize::MAX.bit_width() == 64u32
}

#[rust_lean_test]
pub fn test_usize_wrapping_shl_bits() -> bool {
    1usize.wrapping_shl(64u32) == 1usize
}

#[rust_lean_test]
pub fn test_isize_unbounded_shr_negative() -> bool {
    (-8isize).unbounded_shr(100u32) == -1isize
}

#[rust_lean_test]
pub fn test_usize_swap_bytes_one() -> bool {
    1usize.swap_bytes() == 72057594037927936usize
}

// =============================================================================
// carrying_add / borrowing_sub
// =============================================================================

#[rust_lean_test]
pub fn test_u8_carrying_add_no_carry() -> bool {
    10u8.carrying_add(20u8, false) == (30u8, false)
}

#[rust_lean_test]
pub fn test_u8_carrying_add_carry_in() -> bool {
    10u8.carrying_add(20u8, true) == (31u8, false)
}

#[rust_lean_test]
pub fn test_u8_carrying_add_carry_out() -> bool {
    200u8.carrying_add(100u8, true) == (45u8, true)
}

// The carry-in alone is enough to push MAX over the top.
#[rust_lean_test]
pub fn test_u8_carrying_add_carry_only() -> bool {
    255u8.carrying_add(0u8, true) == (0u8, true)
}

#[rust_lean_test]
pub fn test_i8_carrying_add_overflow() -> bool {
    127i8.carrying_add(0i8, true) == (i8::MIN, true)
}

// `MIN + MIN` overflows and the carry-in then lands on 1.
#[rust_lean_test]
pub fn test_i8_carrying_add_double_overflow() -> bool {
    i8::MIN.carrying_add(i8::MIN, true) == (1i8, true)
}

#[rust_lean_test]
pub fn test_u8_borrowing_sub_no_borrow() -> bool {
    30u8.borrowing_sub(20u8, false) == (10u8, false)
}

#[rust_lean_test]
pub fn test_u8_borrowing_sub_borrow_in() -> bool {
    30u8.borrowing_sub(20u8, true) == (9u8, false)
}

#[rust_lean_test]
pub fn test_u8_borrowing_sub_borrow_out() -> bool {
    5u8.borrowing_sub(10u8, true) == (250u8, true)
}

#[rust_lean_test]
pub fn test_u8_borrowing_sub_borrow_only() -> bool {
    0u8.borrowing_sub(0u8, true) == (255u8, true)
}

#[rust_lean_test]
pub fn test_i8_borrowing_sub_overflow() -> bool {
    i8::MIN.borrowing_sub(0i8, true) == (127i8, true)
}

#[rust_lean_test]
pub fn test_u32_carrying_add_max() -> bool {
    u32::MAX.carrying_add(u32::MAX, true) == (u32::MAX, true)
}

// =============================================================================
// u8 ASCII predicates
// =============================================================================

#[rust_lean_test]
pub fn test_u8_is_ascii_boundary() -> bool {
    127u8.is_ascii() == true
}

#[rust_lean_test]
pub fn test_u8_is_ascii_above_boundary() -> bool {
    128u8.is_ascii() == false
}

#[rust_lean_test]
pub fn test_u8_is_ascii_uppercase() -> bool {
    b'A'.is_ascii_uppercase() == true
}

#[rust_lean_test]
pub fn test_u8_is_ascii_uppercase_lower() -> bool {
    b'a'.is_ascii_uppercase() == false
}

#[rust_lean_test]
pub fn test_u8_is_ascii_lowercase_last() -> bool {
    b'z'.is_ascii_lowercase() == true
}

#[rust_lean_test]
pub fn test_u8_is_ascii_alphabetic_digit() -> bool {
    b'5'.is_ascii_alphabetic() == false
}

#[rust_lean_test]
pub fn test_u8_is_ascii_digit_zero() -> bool {
    b'0'.is_ascii_digit() == true
}

#[rust_lean_test]
pub fn test_u8_is_ascii_octdigit_eight() -> bool {
    b'8'.is_ascii_octdigit() == false
}

#[rust_lean_test]
pub fn test_u8_is_ascii_hexdigit_f() -> bool {
    b'f'.is_ascii_hexdigit() == true
}

#[rust_lean_test]
pub fn test_u8_is_ascii_hexdigit_g() -> bool {
    b'g'.is_ascii_hexdigit() == false
}

#[rust_lean_test]
pub fn test_u8_is_ascii_alphanumeric() -> bool {
    b'9'.is_ascii_alphanumeric() == true
}

#[rust_lean_test]
pub fn test_u8_is_ascii_punctuation_tilde() -> bool {
    b'~'.is_ascii_punctuation() == true
}

#[rust_lean_test]
pub fn test_u8_is_ascii_punctuation_letter() -> bool {
    b'a'.is_ascii_punctuation() == false
}

#[rust_lean_test]
pub fn test_u8_is_ascii_graphic_space() -> bool {
    b' '.is_ascii_graphic() == false
}

#[rust_lean_test]
pub fn test_u8_is_ascii_graphic_bang() -> bool {
    b'!'.is_ascii_graphic() == true
}

#[rust_lean_test]
pub fn test_u8_is_ascii_whitespace_tab() -> bool {
    b'\t'.is_ascii_whitespace() == true
}

#[rust_lean_test]
pub fn test_u8_is_ascii_whitespace_form_feed() -> bool {
    12u8.is_ascii_whitespace() == true
}

#[rust_lean_test]
pub fn test_u8_is_ascii_whitespace_vertical_tab() -> bool {
    11u8.is_ascii_whitespace() == false
}

#[rust_lean_test]
pub fn test_u8_is_ascii_control_nul() -> bool {
    0u8.is_ascii_control() == true
}

#[rust_lean_test]
pub fn test_u8_is_ascii_control_delete() -> bool {
    127u8.is_ascii_control() == true
}

#[rust_lean_test]
pub fn test_u8_is_ascii_control_space() -> bool {
    b' '.is_ascii_control() == false
}

// =============================================================================
// u8 ASCII case conversion
// =============================================================================

#[rust_lean_test]
pub fn test_u8_to_ascii_uppercase_letter() -> bool {
    b'a'.to_ascii_uppercase() == b'A'
}

#[rust_lean_test]
pub fn test_u8_to_ascii_uppercase_non_letter() -> bool {
    b'5'.to_ascii_uppercase() == b'5'
}

#[rust_lean_test]
pub fn test_u8_to_ascii_uppercase_non_ascii() -> bool {
    200u8.to_ascii_uppercase() == 200u8
}

#[rust_lean_test]
pub fn test_u8_to_ascii_lowercase_letter() -> bool {
    b'Z'.to_ascii_lowercase() == b'z'
}

#[rust_lean_test]
pub fn test_u8_to_ascii_lowercase_non_letter() -> bool {
    b'{'.to_ascii_lowercase() == b'{'
}

#[rust_lean_test]
pub fn test_u8_eq_ignore_ascii_case_true() -> bool {
    b'a'.eq_ignore_ascii_case(&b'A') == true
}

#[rust_lean_test]
pub fn test_u8_eq_ignore_ascii_case_false() -> bool {
    b'a'.eq_ignore_ascii_case(&b'B') == false
}

// The 0x20 bit difference must not make non-letters compare equal.
#[rust_lean_test]
pub fn test_u8_eq_ignore_ascii_case_non_letters() -> bool {
    b'{'.eq_ignore_ascii_case(&b'[') == false
}

#[rust_lean_test]
pub fn test_u8_make_ascii_uppercase() -> bool {
    let mut x = b'a';
    x.make_ascii_uppercase();
    x == b'A'
}

#[rust_lean_test]
pub fn test_u8_make_ascii_uppercase_non_letter() -> bool {
    let mut x = 200u8;
    x.make_ascii_uppercase();
    x == 200u8
}

#[rust_lean_test]
pub fn test_u8_make_ascii_lowercase() -> bool {
    let mut x = b'Z';
    x.make_ascii_lowercase();
    x == b'z'
}
