module Core_models.Num
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {impl_6__MIN as impl_u8__MIN}

include Core_models.Bundle {impl_6__MAX as impl_u8__MAX}

include Core_models.Bundle {impl_6__BITS as impl_u8__BITS}

include Core_models.Bundle {impl_6__wrapping_add as impl_u8__wrapping_add}

include Core_models.Bundle {impl_6__saturating_add as impl_u8__saturating_add}

include Core_models.Bundle {impl_6__overflowing_add as impl_u8__overflowing_add}

include Core_models.Bundle {impl_6__checked_add as impl_u8__checked_add}

include Core_models.Bundle {impl_6__unchecked_add as impl_u8__unchecked_add}

include Core_models.Bundle {impl_6__wrapping_sub as impl_u8__wrapping_sub}

include Core_models.Bundle {impl_6__saturating_sub as impl_u8__saturating_sub}

include Core_models.Bundle {impl_6__overflowing_sub as impl_u8__overflowing_sub}

include Core_models.Bundle {impl_6__checked_sub as impl_u8__checked_sub}

include Core_models.Bundle {impl_6__unchecked_sub as impl_u8__unchecked_sub}

include Core_models.Bundle {impl_6__wrapping_mul as impl_u8__wrapping_mul}

include Core_models.Bundle {impl_6__saturating_mul as impl_u8__saturating_mul}

include Core_models.Bundle {impl_6__overflowing_mul as impl_u8__overflowing_mul}

include Core_models.Bundle {impl_6__checked_mul as impl_u8__checked_mul}

include Core_models.Bundle {impl_6__unchecked_mul as impl_u8__unchecked_mul}

include Core_models.Bundle {impl_6__rem_euclid as impl_u8__rem_euclid}

include Core_models.Bundle {impl_6__pow as impl_u8__pow}

include Core_models.Bundle {impl_6__overflowing_pow as impl_u8__overflowing_pow}

include Core_models.Bundle {impl_6__count_ones as impl_u8__count_ones}

include Core_models.Bundle {impl_6__rotate_right as impl_u8__rotate_right}

include Core_models.Bundle {impl_6__rotate_left as impl_u8__rotate_left}

include Core_models.Bundle {impl_6__leading_zeros as impl_u8__leading_zeros}

include Core_models.Bundle {impl_6__ilog2 as impl_u8__ilog2}

include Core_models.Bundle {impl_6__from_str_radix as impl_u8__from_str_radix}

include Core_models.Bundle {impl_6__from_be_bytes as impl_u8__from_be_bytes}

include Core_models.Bundle {impl_6__from_le_bytes as impl_u8__from_le_bytes}

include Core_models.Bundle {impl_6__to_be_bytes as impl_u8__to_be_bytes}

include Core_models.Bundle {impl_6__to_le_bytes as impl_u8__to_le_bytes}

include Core_models.Bundle {impl_6__checked_div as impl_u8__checked_div}

include Core_models.Bundle {impl_6__unchecked_div as impl_u8__unchecked_div}

include Core_models.Bundle {impl_6__checked_rem as impl_u8__checked_rem}

include Core_models.Bundle {impl_6__unchecked_rem as impl_u8__unchecked_rem}

include Core_models.Bundle {impl_6__is_power_of_two as impl_u8__is_power_of_two}

include Core_models.Bundle {impl_6__div_ceil as impl_u8__div_ceil}

include Core_models.Bundle {impl_6__is_multiple_of as impl_u8__is_multiple_of}

include Core_models.Bundle {impl_6__wrapping_neg as impl_u8__wrapping_neg}

include Core_models.Bundle {impl_7__MIN as impl_u16__MIN}

include Core_models.Bundle {impl_7__MAX as impl_u16__MAX}

include Core_models.Bundle {impl_7__BITS as impl_u16__BITS}

include Core_models.Bundle {impl_7__wrapping_add as impl_u16__wrapping_add}

include Core_models.Bundle {impl_7__saturating_add as impl_u16__saturating_add}

include Core_models.Bundle {impl_7__overflowing_add as impl_u16__overflowing_add}

include Core_models.Bundle {impl_7__checked_add as impl_u16__checked_add}

include Core_models.Bundle {impl_7__unchecked_add as impl_u16__unchecked_add}

include Core_models.Bundle {impl_7__wrapping_sub as impl_u16__wrapping_sub}

include Core_models.Bundle {impl_7__saturating_sub as impl_u16__saturating_sub}

include Core_models.Bundle {impl_7__overflowing_sub as impl_u16__overflowing_sub}

include Core_models.Bundle {impl_7__checked_sub as impl_u16__checked_sub}

include Core_models.Bundle {impl_7__unchecked_sub as impl_u16__unchecked_sub}

include Core_models.Bundle {impl_7__wrapping_mul as impl_u16__wrapping_mul}

include Core_models.Bundle {impl_7__saturating_mul as impl_u16__saturating_mul}

include Core_models.Bundle {impl_7__overflowing_mul as impl_u16__overflowing_mul}

include Core_models.Bundle {impl_7__checked_mul as impl_u16__checked_mul}

include Core_models.Bundle {impl_7__unchecked_mul as impl_u16__unchecked_mul}

include Core_models.Bundle {impl_7__rem_euclid as impl_u16__rem_euclid}

include Core_models.Bundle {impl_7__pow as impl_u16__pow}

include Core_models.Bundle {impl_7__overflowing_pow as impl_u16__overflowing_pow}

include Core_models.Bundle {impl_7__count_ones as impl_u16__count_ones}

include Core_models.Bundle {impl_7__rotate_right as impl_u16__rotate_right}

include Core_models.Bundle {impl_7__rotate_left as impl_u16__rotate_left}

include Core_models.Bundle {impl_7__leading_zeros as impl_u16__leading_zeros}

include Core_models.Bundle {impl_7__ilog2 as impl_u16__ilog2}

include Core_models.Bundle {impl_7__from_str_radix as impl_u16__from_str_radix}

include Core_models.Bundle {impl_7__from_be_bytes as impl_u16__from_be_bytes}

include Core_models.Bundle {impl_7__from_le_bytes as impl_u16__from_le_bytes}

include Core_models.Bundle {impl_7__to_be_bytes as impl_u16__to_be_bytes}

include Core_models.Bundle {impl_7__to_le_bytes as impl_u16__to_le_bytes}

include Core_models.Bundle {impl_7__checked_div as impl_u16__checked_div}

include Core_models.Bundle {impl_7__unchecked_div as impl_u16__unchecked_div}

include Core_models.Bundle {impl_7__checked_rem as impl_u16__checked_rem}

include Core_models.Bundle {impl_7__unchecked_rem as impl_u16__unchecked_rem}

include Core_models.Bundle {impl_7__is_power_of_two as impl_u16__is_power_of_two}

include Core_models.Bundle {impl_7__div_ceil as impl_u16__div_ceil}

include Core_models.Bundle {impl_7__is_multiple_of as impl_u16__is_multiple_of}

include Core_models.Bundle {impl_7__wrapping_neg as impl_u16__wrapping_neg}

include Core_models.Bundle {impl_8__MIN as impl_u32__MIN}

include Core_models.Bundle {impl_8__MAX as impl_u32__MAX}

include Core_models.Bundle {impl_8__BITS as impl_u32__BITS}

include Core_models.Bundle {impl_8__wrapping_add as impl_u32__wrapping_add}

include Core_models.Bundle {impl_8__saturating_add as impl_u32__saturating_add}

include Core_models.Bundle {impl_8__overflowing_add as impl_u32__overflowing_add}

include Core_models.Bundle {impl_8__checked_add as impl_u32__checked_add}

include Core_models.Bundle {impl_8__unchecked_add as impl_u32__unchecked_add}

include Core_models.Bundle {impl_8__wrapping_sub as impl_u32__wrapping_sub}

include Core_models.Bundle {impl_8__saturating_sub as impl_u32__saturating_sub}

include Core_models.Bundle {impl_8__overflowing_sub as impl_u32__overflowing_sub}

include Core_models.Bundle {impl_8__checked_sub as impl_u32__checked_sub}

include Core_models.Bundle {impl_8__unchecked_sub as impl_u32__unchecked_sub}

include Core_models.Bundle {impl_8__wrapping_mul as impl_u32__wrapping_mul}

include Core_models.Bundle {impl_8__saturating_mul as impl_u32__saturating_mul}

include Core_models.Bundle {impl_8__overflowing_mul as impl_u32__overflowing_mul}

include Core_models.Bundle {impl_8__checked_mul as impl_u32__checked_mul}

include Core_models.Bundle {impl_8__unchecked_mul as impl_u32__unchecked_mul}

include Core_models.Bundle {impl_8__rem_euclid as impl_u32__rem_euclid}

include Core_models.Bundle {impl_8__pow as impl_u32__pow}

include Core_models.Bundle {impl_8__overflowing_pow as impl_u32__overflowing_pow}

include Core_models.Bundle {impl_8__count_ones as impl_u32__count_ones}

include Core_models.Bundle {impl_8__rotate_right as impl_u32__rotate_right}

include Core_models.Bundle {impl_8__rotate_left as impl_u32__rotate_left}

include Core_models.Bundle {impl_8__leading_zeros as impl_u32__leading_zeros}

include Core_models.Bundle {impl_8__ilog2 as impl_u32__ilog2}

include Core_models.Bundle {impl_8__from_str_radix as impl_u32__from_str_radix}

include Core_models.Bundle {impl_8__from_be_bytes as impl_u32__from_be_bytes}

include Core_models.Bundle {impl_8__from_le_bytes as impl_u32__from_le_bytes}

include Core_models.Bundle {impl_8__to_be_bytes as impl_u32__to_be_bytes}

include Core_models.Bundle {impl_8__to_le_bytes as impl_u32__to_le_bytes}

include Core_models.Bundle {impl_8__checked_div as impl_u32__checked_div}

include Core_models.Bundle {impl_8__unchecked_div as impl_u32__unchecked_div}

include Core_models.Bundle {impl_8__checked_rem as impl_u32__checked_rem}

include Core_models.Bundle {impl_8__unchecked_rem as impl_u32__unchecked_rem}

include Core_models.Bundle {impl_8__is_power_of_two as impl_u32__is_power_of_two}

include Core_models.Bundle {impl_8__div_ceil as impl_u32__div_ceil}

include Core_models.Bundle {impl_8__is_multiple_of as impl_u32__is_multiple_of}

include Core_models.Bundle {impl_8__wrapping_neg as impl_u32__wrapping_neg}

include Core_models.Bundle {impl_9__MIN as impl_u64__MIN}

include Core_models.Bundle {impl_9__MAX as impl_u64__MAX}

include Core_models.Bundle {impl_9__BITS as impl_u64__BITS}

include Core_models.Bundle {impl_9__wrapping_add as impl_u64__wrapping_add}

include Core_models.Bundle {impl_9__saturating_add as impl_u64__saturating_add}

include Core_models.Bundle {impl_9__overflowing_add as impl_u64__overflowing_add}

include Core_models.Bundle {impl_9__checked_add as impl_u64__checked_add}

include Core_models.Bundle {impl_9__unchecked_add as impl_u64__unchecked_add}

include Core_models.Bundle {impl_9__wrapping_sub as impl_u64__wrapping_sub}

include Core_models.Bundle {impl_9__saturating_sub as impl_u64__saturating_sub}

include Core_models.Bundle {impl_9__overflowing_sub as impl_u64__overflowing_sub}

include Core_models.Bundle {impl_9__checked_sub as impl_u64__checked_sub}

include Core_models.Bundle {impl_9__unchecked_sub as impl_u64__unchecked_sub}

include Core_models.Bundle {impl_9__wrapping_mul as impl_u64__wrapping_mul}

include Core_models.Bundle {impl_9__saturating_mul as impl_u64__saturating_mul}

include Core_models.Bundle {impl_9__overflowing_mul as impl_u64__overflowing_mul}

include Core_models.Bundle {impl_9__checked_mul as impl_u64__checked_mul}

include Core_models.Bundle {impl_9__unchecked_mul as impl_u64__unchecked_mul}

include Core_models.Bundle {impl_9__rem_euclid as impl_u64__rem_euclid}

include Core_models.Bundle {impl_9__pow as impl_u64__pow}

include Core_models.Bundle {impl_9__overflowing_pow as impl_u64__overflowing_pow}

include Core_models.Bundle {impl_9__count_ones as impl_u64__count_ones}

include Core_models.Bundle {impl_9__rotate_right as impl_u64__rotate_right}

include Core_models.Bundle {impl_9__rotate_left as impl_u64__rotate_left}

include Core_models.Bundle {impl_9__leading_zeros as impl_u64__leading_zeros}

include Core_models.Bundle {impl_9__ilog2 as impl_u64__ilog2}

include Core_models.Bundle {impl_9__from_str_radix as impl_u64__from_str_radix}

include Core_models.Bundle {impl_9__from_be_bytes as impl_u64__from_be_bytes}

include Core_models.Bundle {impl_9__from_le_bytes as impl_u64__from_le_bytes}

include Core_models.Bundle {impl_9__to_be_bytes as impl_u64__to_be_bytes}

include Core_models.Bundle {impl_9__to_le_bytes as impl_u64__to_le_bytes}

include Core_models.Bundle {impl_9__checked_div as impl_u64__checked_div}

include Core_models.Bundle {impl_9__unchecked_div as impl_u64__unchecked_div}

include Core_models.Bundle {impl_9__checked_rem as impl_u64__checked_rem}

include Core_models.Bundle {impl_9__unchecked_rem as impl_u64__unchecked_rem}

include Core_models.Bundle {impl_9__is_power_of_two as impl_u64__is_power_of_two}

include Core_models.Bundle {impl_9__div_ceil as impl_u64__div_ceil}

include Core_models.Bundle {impl_9__is_multiple_of as impl_u64__is_multiple_of}

include Core_models.Bundle {impl_9__wrapping_neg as impl_u64__wrapping_neg}

include Core_models.Bundle {impl_10__MIN as impl_u128__MIN}

include Core_models.Bundle {impl_10__MAX as impl_u128__MAX}

include Core_models.Bundle {impl_10__BITS as impl_u128__BITS}

include Core_models.Bundle {impl_10__wrapping_add as impl_u128__wrapping_add}

include Core_models.Bundle {impl_10__saturating_add as impl_u128__saturating_add}

include Core_models.Bundle {impl_10__overflowing_add as impl_u128__overflowing_add}

include Core_models.Bundle {impl_10__checked_add as impl_u128__checked_add}

include Core_models.Bundle {impl_10__unchecked_add as impl_u128__unchecked_add}

include Core_models.Bundle {impl_10__wrapping_sub as impl_u128__wrapping_sub}

include Core_models.Bundle {impl_10__saturating_sub as impl_u128__saturating_sub}

include Core_models.Bundle {impl_10__overflowing_sub as impl_u128__overflowing_sub}

include Core_models.Bundle {impl_10__checked_sub as impl_u128__checked_sub}

include Core_models.Bundle {impl_10__unchecked_sub as impl_u128__unchecked_sub}

include Core_models.Bundle {impl_10__wrapping_mul as impl_u128__wrapping_mul}

include Core_models.Bundle {impl_10__saturating_mul as impl_u128__saturating_mul}

include Core_models.Bundle {impl_10__overflowing_mul as impl_u128__overflowing_mul}

include Core_models.Bundle {impl_10__checked_mul as impl_u128__checked_mul}

include Core_models.Bundle {impl_10__unchecked_mul as impl_u128__unchecked_mul}

include Core_models.Bundle {impl_10__rem_euclid as impl_u128__rem_euclid}

include Core_models.Bundle {impl_10__pow as impl_u128__pow}

include Core_models.Bundle {impl_10__overflowing_pow as impl_u128__overflowing_pow}

include Core_models.Bundle {impl_10__count_ones as impl_u128__count_ones}

include Core_models.Bundle {impl_10__rotate_right as impl_u128__rotate_right}

include Core_models.Bundle {impl_10__rotate_left as impl_u128__rotate_left}

include Core_models.Bundle {impl_10__leading_zeros as impl_u128__leading_zeros}

include Core_models.Bundle {impl_10__ilog2 as impl_u128__ilog2}

include Core_models.Bundle {impl_10__from_str_radix as impl_u128__from_str_radix}

include Core_models.Bundle {impl_10__from_be_bytes as impl_u128__from_be_bytes}

include Core_models.Bundle {impl_10__from_le_bytes as impl_u128__from_le_bytes}

include Core_models.Bundle {impl_10__to_be_bytes as impl_u128__to_be_bytes}

include Core_models.Bundle {impl_10__to_le_bytes as impl_u128__to_le_bytes}

include Core_models.Bundle {impl_10__checked_div as impl_u128__checked_div}

include Core_models.Bundle {impl_10__unchecked_div as impl_u128__unchecked_div}

include Core_models.Bundle {impl_10__checked_rem as impl_u128__checked_rem}

include Core_models.Bundle {impl_10__unchecked_rem as impl_u128__unchecked_rem}

include Core_models.Bundle {impl_10__is_power_of_two as impl_u128__is_power_of_two}

include Core_models.Bundle {impl_10__div_ceil as impl_u128__div_ceil}

include Core_models.Bundle {impl_10__is_multiple_of as impl_u128__is_multiple_of}

include Core_models.Bundle {impl_10__wrapping_neg as impl_u128__wrapping_neg}

include Core_models.Bundle {impl_11__MIN as impl_usize__MIN}

include Core_models.Bundle {impl_11__MAX as impl_usize__MAX}

include Core_models.Bundle {impl_11__BITS as impl_usize__BITS}

include Core_models.Bundle {impl_11__wrapping_add as impl_usize__wrapping_add}

include Core_models.Bundle {impl_11__saturating_add as impl_usize__saturating_add}

include Core_models.Bundle {impl_11__overflowing_add as impl_usize__overflowing_add}

include Core_models.Bundle {impl_11__checked_add as impl_usize__checked_add}

include Core_models.Bundle {impl_11__unchecked_add as impl_usize__unchecked_add}

include Core_models.Bundle {impl_11__wrapping_sub as impl_usize__wrapping_sub}

include Core_models.Bundle {impl_11__saturating_sub as impl_usize__saturating_sub}

include Core_models.Bundle {impl_11__overflowing_sub as impl_usize__overflowing_sub}

include Core_models.Bundle {impl_11__checked_sub as impl_usize__checked_sub}

include Core_models.Bundle {impl_11__unchecked_sub as impl_usize__unchecked_sub}

include Core_models.Bundle {impl_11__wrapping_mul as impl_usize__wrapping_mul}

include Core_models.Bundle {impl_11__saturating_mul as impl_usize__saturating_mul}

include Core_models.Bundle {impl_11__overflowing_mul as impl_usize__overflowing_mul}

include Core_models.Bundle {impl_11__checked_mul as impl_usize__checked_mul}

include Core_models.Bundle {impl_11__unchecked_mul as impl_usize__unchecked_mul}

include Core_models.Bundle {impl_11__rem_euclid as impl_usize__rem_euclid}

include Core_models.Bundle {impl_11__pow as impl_usize__pow}

include Core_models.Bundle {impl_11__overflowing_pow as impl_usize__overflowing_pow}

include Core_models.Bundle {impl_11__count_ones as impl_usize__count_ones}

include Core_models.Bundle {impl_11__rotate_right as impl_usize__rotate_right}

include Core_models.Bundle {impl_11__rotate_left as impl_usize__rotate_left}

include Core_models.Bundle {impl_11__leading_zeros as impl_usize__leading_zeros}

include Core_models.Bundle {impl_11__ilog2 as impl_usize__ilog2}

include Core_models.Bundle {impl_11__from_str_radix as impl_usize__from_str_radix}

include Core_models.Bundle {impl_11__from_be_bytes as impl_usize__from_be_bytes}

include Core_models.Bundle {impl_11__from_le_bytes as impl_usize__from_le_bytes}

include Core_models.Bundle {impl_11__to_be_bytes as impl_usize__to_be_bytes}

include Core_models.Bundle {impl_11__to_le_bytes as impl_usize__to_le_bytes}

include Core_models.Bundle {impl_11__checked_div as impl_usize__checked_div}

include Core_models.Bundle {impl_11__unchecked_div as impl_usize__unchecked_div}

include Core_models.Bundle {impl_11__checked_rem as impl_usize__checked_rem}

include Core_models.Bundle {impl_11__unchecked_rem as impl_usize__unchecked_rem}

include Core_models.Bundle {impl_11__is_power_of_two as impl_usize__is_power_of_two}

include Core_models.Bundle {impl_11__div_ceil as impl_usize__div_ceil}

include Core_models.Bundle {impl_11__is_multiple_of as impl_usize__is_multiple_of}

include Core_models.Bundle {impl_11__wrapping_neg as impl_usize__wrapping_neg}

include Core_models.Bundle {impl_12__MIN as impl_i8__MIN}

include Core_models.Bundle {impl_12__MAX as impl_i8__MAX}

include Core_models.Bundle {impl_12__BITS as impl_i8__BITS}

include Core_models.Bundle {impl_12__wrapping_add as impl_i8__wrapping_add}

include Core_models.Bundle {impl_12__saturating_add as impl_i8__saturating_add}

include Core_models.Bundle {impl_12__overflowing_add as impl_i8__overflowing_add}

include Core_models.Bundle {impl_12__checked_add as impl_i8__checked_add}

include Core_models.Bundle {impl_12__unchecked_add as impl_i8__unchecked_add}

include Core_models.Bundle {impl_12__wrapping_sub as impl_i8__wrapping_sub}

include Core_models.Bundle {impl_12__saturating_sub as impl_i8__saturating_sub}

include Core_models.Bundle {impl_12__overflowing_sub as impl_i8__overflowing_sub}

include Core_models.Bundle {impl_12__checked_sub as impl_i8__checked_sub}

include Core_models.Bundle {impl_12__unchecked_sub as impl_i8__unchecked_sub}

include Core_models.Bundle {impl_12__checked_add_unsigned as impl_i8__checked_add_unsigned}

include Core_models.Bundle {impl_12__checked_sub_unsigned as impl_i8__checked_sub_unsigned}

include Core_models.Bundle {impl_12__wrapping_mul as impl_i8__wrapping_mul}

include Core_models.Bundle {impl_12__saturating_mul as impl_i8__saturating_mul}

include Core_models.Bundle {impl_12__overflowing_mul as impl_i8__overflowing_mul}

include Core_models.Bundle {impl_12__checked_mul as impl_i8__checked_mul}

include Core_models.Bundle {impl_12__unchecked_mul as impl_i8__unchecked_mul}

include Core_models.Bundle {impl_12__rem_euclid as impl_i8__rem_euclid}

include Core_models.Bundle {impl_12__pow as impl_i8__pow}

include Core_models.Bundle {impl_12__overflowing_pow as impl_i8__overflowing_pow}

include Core_models.Bundle {impl_12__count_ones as impl_i8__count_ones}

include Core_models.Bundle {impl_12__abs as impl_i8__abs}

include Core_models.Bundle {impl_12__rotate_right as impl_i8__rotate_right}

include Core_models.Bundle {impl_12__rotate_left as impl_i8__rotate_left}

include Core_models.Bundle {impl_12__leading_zeros as impl_i8__leading_zeros}

include Core_models.Bundle {impl_12__ilog2 as impl_i8__ilog2}

include Core_models.Bundle {impl_12__from_str_radix as impl_i8__from_str_radix}

include Core_models.Bundle {impl_12__from_be_bytes as impl_i8__from_be_bytes}

include Core_models.Bundle {impl_12__from_le_bytes as impl_i8__from_le_bytes}

include Core_models.Bundle {impl_12__to_be_bytes as impl_i8__to_be_bytes}

include Core_models.Bundle {impl_12__to_le_bytes as impl_i8__to_le_bytes}

include Core_models.Bundle {impl_12__checked_div as impl_i8__checked_div}

include Core_models.Bundle {impl_12__unchecked_div as impl_i8__unchecked_div}

include Core_models.Bundle {impl_12__checked_rem as impl_i8__checked_rem}

include Core_models.Bundle {impl_12__unchecked_rem as impl_i8__unchecked_rem}

include Core_models.Bundle {impl_12__signum as impl_i8__signum}

include Core_models.Bundle {impl_12__div_ceil as impl_i8__div_ceil}

include Core_models.Bundle {impl_12__wrapping_neg as impl_i8__wrapping_neg}

include Core_models.Bundle {impl_13__MIN as impl_i16__MIN}

include Core_models.Bundle {impl_13__MAX as impl_i16__MAX}

include Core_models.Bundle {impl_13__BITS as impl_i16__BITS}

include Core_models.Bundle {impl_13__wrapping_add as impl_i16__wrapping_add}

include Core_models.Bundle {impl_13__saturating_add as impl_i16__saturating_add}

include Core_models.Bundle {impl_13__overflowing_add as impl_i16__overflowing_add}

include Core_models.Bundle {impl_13__checked_add as impl_i16__checked_add}

include Core_models.Bundle {impl_13__unchecked_add as impl_i16__unchecked_add}

include Core_models.Bundle {impl_13__wrapping_sub as impl_i16__wrapping_sub}

include Core_models.Bundle {impl_13__saturating_sub as impl_i16__saturating_sub}

include Core_models.Bundle {impl_13__overflowing_sub as impl_i16__overflowing_sub}

include Core_models.Bundle {impl_13__checked_sub as impl_i16__checked_sub}

include Core_models.Bundle {impl_13__unchecked_sub as impl_i16__unchecked_sub}

include Core_models.Bundle {impl_13__checked_add_unsigned as impl_i16__checked_add_unsigned}

include Core_models.Bundle {impl_13__checked_sub_unsigned as impl_i16__checked_sub_unsigned}

include Core_models.Bundle {impl_13__wrapping_mul as impl_i16__wrapping_mul}

include Core_models.Bundle {impl_13__saturating_mul as impl_i16__saturating_mul}

include Core_models.Bundle {impl_13__overflowing_mul as impl_i16__overflowing_mul}

include Core_models.Bundle {impl_13__checked_mul as impl_i16__checked_mul}

include Core_models.Bundle {impl_13__unchecked_mul as impl_i16__unchecked_mul}

include Core_models.Bundle {impl_13__rem_euclid as impl_i16__rem_euclid}

include Core_models.Bundle {impl_13__pow as impl_i16__pow}

include Core_models.Bundle {impl_13__overflowing_pow as impl_i16__overflowing_pow}

include Core_models.Bundle {impl_13__count_ones as impl_i16__count_ones}

include Core_models.Bundle {impl_13__abs as impl_i16__abs}

include Core_models.Bundle {impl_13__rotate_right as impl_i16__rotate_right}

include Core_models.Bundle {impl_13__rotate_left as impl_i16__rotate_left}

include Core_models.Bundle {impl_13__leading_zeros as impl_i16__leading_zeros}

include Core_models.Bundle {impl_13__ilog2 as impl_i16__ilog2}

include Core_models.Bundle {impl_13__from_str_radix as impl_i16__from_str_radix}

include Core_models.Bundle {impl_13__from_be_bytes as impl_i16__from_be_bytes}

include Core_models.Bundle {impl_13__from_le_bytes as impl_i16__from_le_bytes}

include Core_models.Bundle {impl_13__to_be_bytes as impl_i16__to_be_bytes}

include Core_models.Bundle {impl_13__to_le_bytes as impl_i16__to_le_bytes}

include Core_models.Bundle {impl_13__checked_div as impl_i16__checked_div}

include Core_models.Bundle {impl_13__unchecked_div as impl_i16__unchecked_div}

include Core_models.Bundle {impl_13__checked_rem as impl_i16__checked_rem}

include Core_models.Bundle {impl_13__unchecked_rem as impl_i16__unchecked_rem}

include Core_models.Bundle {impl_13__signum as impl_i16__signum}

include Core_models.Bundle {impl_13__div_ceil as impl_i16__div_ceil}

include Core_models.Bundle {impl_13__wrapping_neg as impl_i16__wrapping_neg}

include Core_models.Bundle {impl_14__MIN as impl_i32__MIN}

include Core_models.Bundle {impl_14__MAX as impl_i32__MAX}

include Core_models.Bundle {impl_14__BITS as impl_i32__BITS}

include Core_models.Bundle {impl_14__wrapping_add as impl_i32__wrapping_add}

include Core_models.Bundle {impl_14__saturating_add as impl_i32__saturating_add}

include Core_models.Bundle {impl_14__overflowing_add as impl_i32__overflowing_add}

include Core_models.Bundle {impl_14__checked_add as impl_i32__checked_add}

include Core_models.Bundle {impl_14__unchecked_add as impl_i32__unchecked_add}

include Core_models.Bundle {impl_14__wrapping_sub as impl_i32__wrapping_sub}

include Core_models.Bundle {impl_14__saturating_sub as impl_i32__saturating_sub}

include Core_models.Bundle {impl_14__overflowing_sub as impl_i32__overflowing_sub}

include Core_models.Bundle {impl_14__checked_sub as impl_i32__checked_sub}

include Core_models.Bundle {impl_14__unchecked_sub as impl_i32__unchecked_sub}

include Core_models.Bundle {impl_14__checked_add_unsigned as impl_i32__checked_add_unsigned}

include Core_models.Bundle {impl_14__checked_sub_unsigned as impl_i32__checked_sub_unsigned}

include Core_models.Bundle {impl_14__wrapping_mul as impl_i32__wrapping_mul}

include Core_models.Bundle {impl_14__saturating_mul as impl_i32__saturating_mul}

include Core_models.Bundle {impl_14__overflowing_mul as impl_i32__overflowing_mul}

include Core_models.Bundle {impl_14__checked_mul as impl_i32__checked_mul}

include Core_models.Bundle {impl_14__unchecked_mul as impl_i32__unchecked_mul}

include Core_models.Bundle {impl_14__rem_euclid as impl_i32__rem_euclid}

include Core_models.Bundle {impl_14__pow as impl_i32__pow}

include Core_models.Bundle {impl_14__overflowing_pow as impl_i32__overflowing_pow}

include Core_models.Bundle {impl_14__count_ones as impl_i32__count_ones}

include Core_models.Bundle {impl_14__abs as impl_i32__abs}

include Core_models.Bundle {impl_14__rotate_right as impl_i32__rotate_right}

include Core_models.Bundle {impl_14__rotate_left as impl_i32__rotate_left}

include Core_models.Bundle {impl_14__leading_zeros as impl_i32__leading_zeros}

include Core_models.Bundle {impl_14__ilog2 as impl_i32__ilog2}

include Core_models.Bundle {impl_14__from_str_radix as impl_i32__from_str_radix}

include Core_models.Bundle {impl_14__from_be_bytes as impl_i32__from_be_bytes}

include Core_models.Bundle {impl_14__from_le_bytes as impl_i32__from_le_bytes}

include Core_models.Bundle {impl_14__to_be_bytes as impl_i32__to_be_bytes}

include Core_models.Bundle {impl_14__to_le_bytes as impl_i32__to_le_bytes}

include Core_models.Bundle {impl_14__checked_div as impl_i32__checked_div}

include Core_models.Bundle {impl_14__unchecked_div as impl_i32__unchecked_div}

include Core_models.Bundle {impl_14__checked_rem as impl_i32__checked_rem}

include Core_models.Bundle {impl_14__unchecked_rem as impl_i32__unchecked_rem}

include Core_models.Bundle {impl_14__signum as impl_i32__signum}

include Core_models.Bundle {impl_14__div_ceil as impl_i32__div_ceil}

include Core_models.Bundle {impl_14__wrapping_neg as impl_i32__wrapping_neg}

include Core_models.Bundle {impl_15__MIN as impl_i64__MIN}

include Core_models.Bundle {impl_15__MAX as impl_i64__MAX}

include Core_models.Bundle {impl_15__BITS as impl_i64__BITS}

include Core_models.Bundle {impl_15__wrapping_add as impl_i64__wrapping_add}

include Core_models.Bundle {impl_15__saturating_add as impl_i64__saturating_add}

include Core_models.Bundle {impl_15__overflowing_add as impl_i64__overflowing_add}

include Core_models.Bundle {impl_15__checked_add as impl_i64__checked_add}

include Core_models.Bundle {impl_15__unchecked_add as impl_i64__unchecked_add}

include Core_models.Bundle {impl_15__wrapping_sub as impl_i64__wrapping_sub}

include Core_models.Bundle {impl_15__saturating_sub as impl_i64__saturating_sub}

include Core_models.Bundle {impl_15__overflowing_sub as impl_i64__overflowing_sub}

include Core_models.Bundle {impl_15__checked_sub as impl_i64__checked_sub}

include Core_models.Bundle {impl_15__unchecked_sub as impl_i64__unchecked_sub}

include Core_models.Bundle {impl_15__checked_add_unsigned as impl_i64__checked_add_unsigned}

include Core_models.Bundle {impl_15__checked_sub_unsigned as impl_i64__checked_sub_unsigned}

include Core_models.Bundle {impl_15__wrapping_mul as impl_i64__wrapping_mul}

include Core_models.Bundle {impl_15__saturating_mul as impl_i64__saturating_mul}

include Core_models.Bundle {impl_15__overflowing_mul as impl_i64__overflowing_mul}

include Core_models.Bundle {impl_15__checked_mul as impl_i64__checked_mul}

include Core_models.Bundle {impl_15__unchecked_mul as impl_i64__unchecked_mul}

include Core_models.Bundle {impl_15__rem_euclid as impl_i64__rem_euclid}

include Core_models.Bundle {impl_15__pow as impl_i64__pow}

include Core_models.Bundle {impl_15__overflowing_pow as impl_i64__overflowing_pow}

include Core_models.Bundle {impl_15__count_ones as impl_i64__count_ones}

include Core_models.Bundle {impl_15__abs as impl_i64__abs}

include Core_models.Bundle {impl_15__rotate_right as impl_i64__rotate_right}

include Core_models.Bundle {impl_15__rotate_left as impl_i64__rotate_left}

include Core_models.Bundle {impl_15__leading_zeros as impl_i64__leading_zeros}

include Core_models.Bundle {impl_15__ilog2 as impl_i64__ilog2}

include Core_models.Bundle {impl_15__from_str_radix as impl_i64__from_str_radix}

include Core_models.Bundle {impl_15__from_be_bytes as impl_i64__from_be_bytes}

include Core_models.Bundle {impl_15__from_le_bytes as impl_i64__from_le_bytes}

include Core_models.Bundle {impl_15__to_be_bytes as impl_i64__to_be_bytes}

include Core_models.Bundle {impl_15__to_le_bytes as impl_i64__to_le_bytes}

include Core_models.Bundle {impl_15__checked_div as impl_i64__checked_div}

include Core_models.Bundle {impl_15__unchecked_div as impl_i64__unchecked_div}

include Core_models.Bundle {impl_15__checked_rem as impl_i64__checked_rem}

include Core_models.Bundle {impl_15__unchecked_rem as impl_i64__unchecked_rem}

include Core_models.Bundle {impl_15__signum as impl_i64__signum}

include Core_models.Bundle {impl_15__div_ceil as impl_i64__div_ceil}

include Core_models.Bundle {impl_15__wrapping_neg as impl_i64__wrapping_neg}

include Core_models.Bundle {impl_16__MIN as impl_i128__MIN}

include Core_models.Bundle {impl_16__MAX as impl_i128__MAX}

include Core_models.Bundle {impl_16__BITS as impl_i128__BITS}

include Core_models.Bundle {impl_16__wrapping_add as impl_i128__wrapping_add}

include Core_models.Bundle {impl_16__saturating_add as impl_i128__saturating_add}

include Core_models.Bundle {impl_16__overflowing_add as impl_i128__overflowing_add}

include Core_models.Bundle {impl_16__checked_add as impl_i128__checked_add}

include Core_models.Bundle {impl_16__unchecked_add as impl_i128__unchecked_add}

include Core_models.Bundle {impl_16__wrapping_sub as impl_i128__wrapping_sub}

include Core_models.Bundle {impl_16__saturating_sub as impl_i128__saturating_sub}

include Core_models.Bundle {impl_16__overflowing_sub as impl_i128__overflowing_sub}

include Core_models.Bundle {impl_16__checked_sub as impl_i128__checked_sub}

include Core_models.Bundle {impl_16__unchecked_sub as impl_i128__unchecked_sub}

include Core_models.Bundle {impl_16__checked_add_unsigned as impl_i128__checked_add_unsigned}

include Core_models.Bundle {impl_16__checked_sub_unsigned as impl_i128__checked_sub_unsigned}

include Core_models.Bundle {impl_16__wrapping_mul as impl_i128__wrapping_mul}

include Core_models.Bundle {impl_16__saturating_mul as impl_i128__saturating_mul}

include Core_models.Bundle {impl_16__overflowing_mul as impl_i128__overflowing_mul}

include Core_models.Bundle {impl_16__checked_mul as impl_i128__checked_mul}

include Core_models.Bundle {impl_16__unchecked_mul as impl_i128__unchecked_mul}

include Core_models.Bundle {impl_16__rem_euclid as impl_i128__rem_euclid}

include Core_models.Bundle {impl_16__pow as impl_i128__pow}

include Core_models.Bundle {impl_16__overflowing_pow as impl_i128__overflowing_pow}

include Core_models.Bundle {impl_16__count_ones as impl_i128__count_ones}

include Core_models.Bundle {impl_16__abs as impl_i128__abs}

include Core_models.Bundle {impl_16__rotate_right as impl_i128__rotate_right}

include Core_models.Bundle {impl_16__rotate_left as impl_i128__rotate_left}

include Core_models.Bundle {impl_16__leading_zeros as impl_i128__leading_zeros}

include Core_models.Bundle {impl_16__ilog2 as impl_i128__ilog2}

include Core_models.Bundle {impl_16__from_str_radix as impl_i128__from_str_radix}

include Core_models.Bundle {impl_16__from_be_bytes as impl_i128__from_be_bytes}

include Core_models.Bundle {impl_16__from_le_bytes as impl_i128__from_le_bytes}

include Core_models.Bundle {impl_16__to_be_bytes as impl_i128__to_be_bytes}

include Core_models.Bundle {impl_16__to_le_bytes as impl_i128__to_le_bytes}

include Core_models.Bundle {impl_16__checked_div as impl_i128__checked_div}

include Core_models.Bundle {impl_16__unchecked_div as impl_i128__unchecked_div}

include Core_models.Bundle {impl_16__checked_rem as impl_i128__checked_rem}

include Core_models.Bundle {impl_16__unchecked_rem as impl_i128__unchecked_rem}

include Core_models.Bundle {impl_16__signum as impl_i128__signum}

include Core_models.Bundle {impl_16__div_ceil as impl_i128__div_ceil}

include Core_models.Bundle {impl_16__wrapping_neg as impl_i128__wrapping_neg}

include Core_models.Bundle {impl_17__MIN as impl_isize__MIN}

include Core_models.Bundle {impl_17__MAX as impl_isize__MAX}

include Core_models.Bundle {impl_17__BITS as impl_isize__BITS}

include Core_models.Bundle {impl_17__wrapping_add as impl_isize__wrapping_add}

include Core_models.Bundle {impl_17__saturating_add as impl_isize__saturating_add}

include Core_models.Bundle {impl_17__overflowing_add as impl_isize__overflowing_add}

include Core_models.Bundle {impl_17__checked_add as impl_isize__checked_add}

include Core_models.Bundle {impl_17__unchecked_add as impl_isize__unchecked_add}

include Core_models.Bundle {impl_17__wrapping_sub as impl_isize__wrapping_sub}

include Core_models.Bundle {impl_17__saturating_sub as impl_isize__saturating_sub}

include Core_models.Bundle {impl_17__overflowing_sub as impl_isize__overflowing_sub}

include Core_models.Bundle {impl_17__checked_sub as impl_isize__checked_sub}

include Core_models.Bundle {impl_17__unchecked_sub as impl_isize__unchecked_sub}

include Core_models.Bundle {impl_17__checked_add_unsigned as impl_isize__checked_add_unsigned}

include Core_models.Bundle {impl_17__checked_sub_unsigned as impl_isize__checked_sub_unsigned}

include Core_models.Bundle {impl_17__wrapping_mul as impl_isize__wrapping_mul}

include Core_models.Bundle {impl_17__saturating_mul as impl_isize__saturating_mul}

include Core_models.Bundle {impl_17__overflowing_mul as impl_isize__overflowing_mul}

include Core_models.Bundle {impl_17__checked_mul as impl_isize__checked_mul}

include Core_models.Bundle {impl_17__unchecked_mul as impl_isize__unchecked_mul}

include Core_models.Bundle {impl_17__rem_euclid as impl_isize__rem_euclid}

include Core_models.Bundle {impl_17__pow as impl_isize__pow}

include Core_models.Bundle {impl_17__overflowing_pow as impl_isize__overflowing_pow}

include Core_models.Bundle {impl_17__count_ones as impl_isize__count_ones}

include Core_models.Bundle {impl_17__abs as impl_isize__abs}

include Core_models.Bundle {impl_17__rotate_right as impl_isize__rotate_right}

include Core_models.Bundle {impl_17__rotate_left as impl_isize__rotate_left}

include Core_models.Bundle {impl_17__leading_zeros as impl_isize__leading_zeros}

include Core_models.Bundle {impl_17__ilog2 as impl_isize__ilog2}

include Core_models.Bundle {impl_17__from_str_radix as impl_isize__from_str_radix}

include Core_models.Bundle {impl_17__from_be_bytes as impl_isize__from_be_bytes}

include Core_models.Bundle {impl_17__from_le_bytes as impl_isize__from_le_bytes}

include Core_models.Bundle {impl_17__to_be_bytes as impl_isize__to_be_bytes}

include Core_models.Bundle {impl_17__to_le_bytes as impl_isize__to_le_bytes}

include Core_models.Bundle {impl_17__checked_div as impl_isize__checked_div}

include Core_models.Bundle {impl_17__unchecked_div as impl_isize__unchecked_div}

include Core_models.Bundle {impl_17__checked_rem as impl_isize__checked_rem}

include Core_models.Bundle {impl_17__unchecked_rem as impl_isize__unchecked_rem}

include Core_models.Bundle {impl_17__signum as impl_isize__signum}

include Core_models.Bundle {impl_17__div_ceil as impl_isize__div_ceil}

include Core_models.Bundle {impl_17__wrapping_neg as impl_isize__wrapping_neg}

include Core_models.Bundle {impl_18__from__num as impl_18}

include Core_models.Bundle {impl_19__from__num as impl_19}

include Core_models.Bundle {impl_20__from__num as impl_20}

include Core_models.Bundle {impl_21__from__num as impl_21}

include Core_models.Bundle {impl_22__from__num as impl_22}

include Core_models.Bundle {impl_23__from__num as impl_23}

include Core_models.Bundle {impl_24__from__num as impl_24}

include Core_models.Bundle {impl_25__from__num as impl_25}

include Core_models.Bundle {impl_26__from__num as impl_26}

include Core_models.Bundle {impl_27__from__num as impl_27}

include Core_models.Bundle {impl_28__from__num as impl_28}

include Core_models.Bundle {impl_29__from__num as impl_29}

include Core_models.Bundle {impl_30__from__num as impl_30}

include Core_models.Bundle {t_NonZero as t_NonZero}

include Core_models.Bundle {NonZero as NonZero}

include Core_models.Bundle {impl_31__BITS as impl_NonZero_of_u8__BITS}

include Core_models.Bundle {impl_31__MIN as impl_NonZero_of_u8__MIN}

include Core_models.Bundle {impl_31__MAX as impl_NonZero_of_u8__MAX}

include Core_models.Bundle {impl_31__new as impl_NonZero_of_u8__new}

include Core_models.Bundle {impl_31__new_unchecked as impl_NonZero_of_u8__new_unchecked}

include Core_models.Bundle {impl_31__get as impl_NonZero_of_u8__get}

include Core_models.Bundle {impl_31__from_str_radix as impl_NonZero_of_u8__from_str_radix}

include Core_models.Bundle {impl_31__leading_zeros as impl_NonZero_of_u8__leading_zeros}

include Core_models.Bundle {impl_31__trailing_zeros as impl_NonZero_of_u8__trailing_zeros}

include Core_models.Bundle {impl_31__lowest_one as impl_NonZero_of_u8__lowest_one}

include Core_models.Bundle {impl_31__count_ones as impl_NonZero_of_u8__count_ones}

include Core_models.Bundle {impl_31__isolate_highest_one as impl_NonZero_of_u8__isolate_highest_one}

include Core_models.Bundle {impl_31__isolate_lowest_one as impl_NonZero_of_u8__isolate_lowest_one}

include Core_models.Bundle {impl_31__rotate_left as impl_NonZero_of_u8__rotate_left}

include Core_models.Bundle {impl_31__rotate_right as impl_NonZero_of_u8__rotate_right}

include Core_models.Bundle {impl_31__swap_bytes as impl_NonZero_of_u8__swap_bytes}

include Core_models.Bundle {impl_31__to_be as impl_NonZero_of_u8__to_be}

include Core_models.Bundle {impl_31__to_le as impl_NonZero_of_u8__to_le}

include Core_models.Bundle {impl_31__from_be as impl_NonZero_of_u8__from_be}

include Core_models.Bundle {impl_31__from_le as impl_NonZero_of_u8__from_le}

include Core_models.Bundle {impl_31__checked_mul as impl_NonZero_of_u8__checked_mul}

include Core_models.Bundle {impl_31__saturating_mul as impl_NonZero_of_u8__saturating_mul}

include Core_models.Bundle {impl_31__checked_pow as impl_NonZero_of_u8__checked_pow}

include Core_models.Bundle {impl_31__saturating_pow as impl_NonZero_of_u8__saturating_pow}

include Core_models.Bundle {impl_31__highest_one as impl_NonZero_of_u8__highest_one}

include Core_models.Bundle {impl_31__ilog2 as impl_NonZero_of_u8__ilog2}

include Core_models.Bundle {impl_31__bit_width as impl_NonZero_of_u8__bit_width}

include Core_models.Bundle {impl_31__checked_add as impl_NonZero_of_u8__checked_add}

include Core_models.Bundle {impl_31__saturating_add as impl_NonZero_of_u8__saturating_add}

include Core_models.Bundle {impl_31__unchecked_add as impl_NonZero_of_u8__unchecked_add}

include Core_models.Bundle {impl_31__unchecked_mul as impl_NonZero_of_u8__unchecked_mul}

include Core_models.Bundle {impl_31__checked_next_power_of_two as impl_NonZero_of_u8__checked_next_power_of_two}

include Core_models.Bundle {impl_31__midpoint as impl_NonZero_of_u8__midpoint}

include Core_models.Bundle {impl_31__is_power_of_two as impl_NonZero_of_u8__is_power_of_two}

include Core_models.Bundle {impl_31__cast_signed as impl_NonZero_of_u8__cast_signed}

include Core_models.Bundle {impl_31__div_ceil as impl_NonZero_of_u8__div_ceil}

include Core_models.Bundle {impl_32__BITS as impl_NonZero_of_u16__BITS}

include Core_models.Bundle {impl_32__MIN as impl_NonZero_of_u16__MIN}

include Core_models.Bundle {impl_32__MAX as impl_NonZero_of_u16__MAX}

include Core_models.Bundle {impl_32__new as impl_NonZero_of_u16__new}

include Core_models.Bundle {impl_32__new_unchecked as impl_NonZero_of_u16__new_unchecked}

include Core_models.Bundle {impl_32__get as impl_NonZero_of_u16__get}

include Core_models.Bundle {impl_32__from_str_radix as impl_NonZero_of_u16__from_str_radix}

include Core_models.Bundle {impl_32__leading_zeros as impl_NonZero_of_u16__leading_zeros}

include Core_models.Bundle {impl_32__trailing_zeros as impl_NonZero_of_u16__trailing_zeros}

include Core_models.Bundle {impl_32__lowest_one as impl_NonZero_of_u16__lowest_one}

include Core_models.Bundle {impl_32__count_ones as impl_NonZero_of_u16__count_ones}

include Core_models.Bundle {impl_32__isolate_highest_one as impl_NonZero_of_u16__isolate_highest_one}

include Core_models.Bundle {impl_32__isolate_lowest_one as impl_NonZero_of_u16__isolate_lowest_one}

include Core_models.Bundle {impl_32__rotate_left as impl_NonZero_of_u16__rotate_left}

include Core_models.Bundle {impl_32__rotate_right as impl_NonZero_of_u16__rotate_right}

include Core_models.Bundle {impl_32__swap_bytes as impl_NonZero_of_u16__swap_bytes}

include Core_models.Bundle {impl_32__to_be as impl_NonZero_of_u16__to_be}

include Core_models.Bundle {impl_32__to_le as impl_NonZero_of_u16__to_le}

include Core_models.Bundle {impl_32__from_be as impl_NonZero_of_u16__from_be}

include Core_models.Bundle {impl_32__from_le as impl_NonZero_of_u16__from_le}

include Core_models.Bundle {impl_32__checked_mul as impl_NonZero_of_u16__checked_mul}

include Core_models.Bundle {impl_32__saturating_mul as impl_NonZero_of_u16__saturating_mul}

include Core_models.Bundle {impl_32__checked_pow as impl_NonZero_of_u16__checked_pow}

include Core_models.Bundle {impl_32__saturating_pow as impl_NonZero_of_u16__saturating_pow}

include Core_models.Bundle {impl_32__highest_one as impl_NonZero_of_u16__highest_one}

include Core_models.Bundle {impl_32__ilog2 as impl_NonZero_of_u16__ilog2}

include Core_models.Bundle {impl_32__bit_width as impl_NonZero_of_u16__bit_width}

include Core_models.Bundle {impl_32__checked_add as impl_NonZero_of_u16__checked_add}

include Core_models.Bundle {impl_32__saturating_add as impl_NonZero_of_u16__saturating_add}

include Core_models.Bundle {impl_32__unchecked_add as impl_NonZero_of_u16__unchecked_add}

include Core_models.Bundle {impl_32__unchecked_mul as impl_NonZero_of_u16__unchecked_mul}

include Core_models.Bundle {impl_32__checked_next_power_of_two as impl_NonZero_of_u16__checked_next_power_of_two}

include Core_models.Bundle {impl_32__midpoint as impl_NonZero_of_u16__midpoint}

include Core_models.Bundle {impl_32__is_power_of_two as impl_NonZero_of_u16__is_power_of_two}

include Core_models.Bundle {impl_32__cast_signed as impl_NonZero_of_u16__cast_signed}

include Core_models.Bundle {impl_32__div_ceil as impl_NonZero_of_u16__div_ceil}

include Core_models.Bundle {impl_33__BITS as impl_NonZero_of_u32__BITS}

include Core_models.Bundle {impl_33__MIN as impl_NonZero_of_u32__MIN}

include Core_models.Bundle {impl_33__MAX as impl_NonZero_of_u32__MAX}

include Core_models.Bundle {impl_33__new as impl_NonZero_of_u32__new}

include Core_models.Bundle {impl_33__new_unchecked as impl_NonZero_of_u32__new_unchecked}

include Core_models.Bundle {impl_33__get as impl_NonZero_of_u32__get}

include Core_models.Bundle {impl_33__from_str_radix as impl_NonZero_of_u32__from_str_radix}

include Core_models.Bundle {impl_33__leading_zeros as impl_NonZero_of_u32__leading_zeros}

include Core_models.Bundle {impl_33__trailing_zeros as impl_NonZero_of_u32__trailing_zeros}

include Core_models.Bundle {impl_33__lowest_one as impl_NonZero_of_u32__lowest_one}

include Core_models.Bundle {impl_33__count_ones as impl_NonZero_of_u32__count_ones}

include Core_models.Bundle {impl_33__isolate_highest_one as impl_NonZero_of_u32__isolate_highest_one}

include Core_models.Bundle {impl_33__isolate_lowest_one as impl_NonZero_of_u32__isolate_lowest_one}

include Core_models.Bundle {impl_33__rotate_left as impl_NonZero_of_u32__rotate_left}

include Core_models.Bundle {impl_33__rotate_right as impl_NonZero_of_u32__rotate_right}

include Core_models.Bundle {impl_33__swap_bytes as impl_NonZero_of_u32__swap_bytes}

include Core_models.Bundle {impl_33__to_be as impl_NonZero_of_u32__to_be}

include Core_models.Bundle {impl_33__to_le as impl_NonZero_of_u32__to_le}

include Core_models.Bundle {impl_33__from_be as impl_NonZero_of_u32__from_be}

include Core_models.Bundle {impl_33__from_le as impl_NonZero_of_u32__from_le}

include Core_models.Bundle {impl_33__checked_mul as impl_NonZero_of_u32__checked_mul}

include Core_models.Bundle {impl_33__saturating_mul as impl_NonZero_of_u32__saturating_mul}

include Core_models.Bundle {impl_33__checked_pow as impl_NonZero_of_u32__checked_pow}

include Core_models.Bundle {impl_33__saturating_pow as impl_NonZero_of_u32__saturating_pow}

include Core_models.Bundle {impl_33__highest_one as impl_NonZero_of_u32__highest_one}

include Core_models.Bundle {impl_33__ilog2 as impl_NonZero_of_u32__ilog2}

include Core_models.Bundle {impl_33__bit_width as impl_NonZero_of_u32__bit_width}

include Core_models.Bundle {impl_33__checked_add as impl_NonZero_of_u32__checked_add}

include Core_models.Bundle {impl_33__saturating_add as impl_NonZero_of_u32__saturating_add}

include Core_models.Bundle {impl_33__unchecked_add as impl_NonZero_of_u32__unchecked_add}

include Core_models.Bundle {impl_33__unchecked_mul as impl_NonZero_of_u32__unchecked_mul}

include Core_models.Bundle {impl_33__checked_next_power_of_two as impl_NonZero_of_u32__checked_next_power_of_two}

include Core_models.Bundle {impl_33__midpoint as impl_NonZero_of_u32__midpoint}

include Core_models.Bundle {impl_33__is_power_of_two as impl_NonZero_of_u32__is_power_of_two}

include Core_models.Bundle {impl_33__cast_signed as impl_NonZero_of_u32__cast_signed}

include Core_models.Bundle {impl_33__div_ceil as impl_NonZero_of_u32__div_ceil}

include Core_models.Bundle {impl_34__BITS as impl_NonZero_of_u64__BITS}

include Core_models.Bundle {impl_34__MIN as impl_NonZero_of_u64__MIN}

include Core_models.Bundle {impl_34__MAX as impl_NonZero_of_u64__MAX}

include Core_models.Bundle {impl_34__new as impl_NonZero_of_u64__new}

include Core_models.Bundle {impl_34__new_unchecked as impl_NonZero_of_u64__new_unchecked}

include Core_models.Bundle {impl_34__get as impl_NonZero_of_u64__get}

include Core_models.Bundle {impl_34__from_str_radix as impl_NonZero_of_u64__from_str_radix}

include Core_models.Bundle {impl_34__leading_zeros as impl_NonZero_of_u64__leading_zeros}

include Core_models.Bundle {impl_34__trailing_zeros as impl_NonZero_of_u64__trailing_zeros}

include Core_models.Bundle {impl_34__lowest_one as impl_NonZero_of_u64__lowest_one}

include Core_models.Bundle {impl_34__count_ones as impl_NonZero_of_u64__count_ones}

include Core_models.Bundle {impl_34__isolate_highest_one as impl_NonZero_of_u64__isolate_highest_one}

include Core_models.Bundle {impl_34__isolate_lowest_one as impl_NonZero_of_u64__isolate_lowest_one}

include Core_models.Bundle {impl_34__rotate_left as impl_NonZero_of_u64__rotate_left}

include Core_models.Bundle {impl_34__rotate_right as impl_NonZero_of_u64__rotate_right}

include Core_models.Bundle {impl_34__swap_bytes as impl_NonZero_of_u64__swap_bytes}

include Core_models.Bundle {impl_34__to_be as impl_NonZero_of_u64__to_be}

include Core_models.Bundle {impl_34__to_le as impl_NonZero_of_u64__to_le}

include Core_models.Bundle {impl_34__from_be as impl_NonZero_of_u64__from_be}

include Core_models.Bundle {impl_34__from_le as impl_NonZero_of_u64__from_le}

include Core_models.Bundle {impl_34__checked_mul as impl_NonZero_of_u64__checked_mul}

include Core_models.Bundle {impl_34__saturating_mul as impl_NonZero_of_u64__saturating_mul}

include Core_models.Bundle {impl_34__checked_pow as impl_NonZero_of_u64__checked_pow}

include Core_models.Bundle {impl_34__saturating_pow as impl_NonZero_of_u64__saturating_pow}

include Core_models.Bundle {impl_34__highest_one as impl_NonZero_of_u64__highest_one}

include Core_models.Bundle {impl_34__ilog2 as impl_NonZero_of_u64__ilog2}

include Core_models.Bundle {impl_34__bit_width as impl_NonZero_of_u64__bit_width}

include Core_models.Bundle {impl_34__checked_add as impl_NonZero_of_u64__checked_add}

include Core_models.Bundle {impl_34__saturating_add as impl_NonZero_of_u64__saturating_add}

include Core_models.Bundle {impl_34__unchecked_add as impl_NonZero_of_u64__unchecked_add}

include Core_models.Bundle {impl_34__unchecked_mul as impl_NonZero_of_u64__unchecked_mul}

include Core_models.Bundle {impl_34__checked_next_power_of_two as impl_NonZero_of_u64__checked_next_power_of_two}

include Core_models.Bundle {impl_34__midpoint as impl_NonZero_of_u64__midpoint}

include Core_models.Bundle {impl_34__is_power_of_two as impl_NonZero_of_u64__is_power_of_two}

include Core_models.Bundle {impl_34__cast_signed as impl_NonZero_of_u64__cast_signed}

include Core_models.Bundle {impl_34__div_ceil as impl_NonZero_of_u64__div_ceil}

include Core_models.Bundle {impl_35__BITS as impl_NonZero_of_u128__BITS}

include Core_models.Bundle {impl_35__MIN as impl_NonZero_of_u128__MIN}

include Core_models.Bundle {impl_35__MAX as impl_NonZero_of_u128__MAX}

include Core_models.Bundle {impl_35__new as impl_NonZero_of_u128__new}

include Core_models.Bundle {impl_35__new_unchecked as impl_NonZero_of_u128__new_unchecked}

include Core_models.Bundle {impl_35__get as impl_NonZero_of_u128__get}

include Core_models.Bundle {impl_35__from_str_radix as impl_NonZero_of_u128__from_str_radix}

include Core_models.Bundle {impl_35__leading_zeros as impl_NonZero_of_u128__leading_zeros}

include Core_models.Bundle {impl_35__trailing_zeros as impl_NonZero_of_u128__trailing_zeros}

include Core_models.Bundle {impl_35__lowest_one as impl_NonZero_of_u128__lowest_one}

include Core_models.Bundle {impl_35__count_ones as impl_NonZero_of_u128__count_ones}

include Core_models.Bundle {impl_35__isolate_highest_one as impl_NonZero_of_u128__isolate_highest_one}

include Core_models.Bundle {impl_35__isolate_lowest_one as impl_NonZero_of_u128__isolate_lowest_one}

include Core_models.Bundle {impl_35__rotate_left as impl_NonZero_of_u128__rotate_left}

include Core_models.Bundle {impl_35__rotate_right as impl_NonZero_of_u128__rotate_right}

include Core_models.Bundle {impl_35__swap_bytes as impl_NonZero_of_u128__swap_bytes}

include Core_models.Bundle {impl_35__to_be as impl_NonZero_of_u128__to_be}

include Core_models.Bundle {impl_35__to_le as impl_NonZero_of_u128__to_le}

include Core_models.Bundle {impl_35__from_be as impl_NonZero_of_u128__from_be}

include Core_models.Bundle {impl_35__from_le as impl_NonZero_of_u128__from_le}

include Core_models.Bundle {impl_35__checked_mul as impl_NonZero_of_u128__checked_mul}

include Core_models.Bundle {impl_35__saturating_mul as impl_NonZero_of_u128__saturating_mul}

include Core_models.Bundle {impl_35__checked_pow as impl_NonZero_of_u128__checked_pow}

include Core_models.Bundle {impl_35__saturating_pow as impl_NonZero_of_u128__saturating_pow}

include Core_models.Bundle {impl_35__highest_one as impl_NonZero_of_u128__highest_one}

include Core_models.Bundle {impl_35__ilog2 as impl_NonZero_of_u128__ilog2}

include Core_models.Bundle {impl_35__bit_width as impl_NonZero_of_u128__bit_width}

include Core_models.Bundle {impl_35__checked_add as impl_NonZero_of_u128__checked_add}

include Core_models.Bundle {impl_35__saturating_add as impl_NonZero_of_u128__saturating_add}

include Core_models.Bundle {impl_35__unchecked_add as impl_NonZero_of_u128__unchecked_add}

include Core_models.Bundle {impl_35__unchecked_mul as impl_NonZero_of_u128__unchecked_mul}

include Core_models.Bundle {impl_35__checked_next_power_of_two as impl_NonZero_of_u128__checked_next_power_of_two}

include Core_models.Bundle {impl_35__midpoint as impl_NonZero_of_u128__midpoint}

include Core_models.Bundle {impl_35__is_power_of_two as impl_NonZero_of_u128__is_power_of_two}

include Core_models.Bundle {impl_35__cast_signed as impl_NonZero_of_u128__cast_signed}

include Core_models.Bundle {impl_35__div_ceil as impl_NonZero_of_u128__div_ceil}

include Core_models.Bundle {impl_36__BITS as impl_NonZero_of_usize__BITS}

include Core_models.Bundle {impl_36__MIN as impl_NonZero_of_usize__MIN}

include Core_models.Bundle {impl_36__MAX as impl_NonZero_of_usize__MAX}

include Core_models.Bundle {impl_36__new as impl_NonZero_of_usize__new}

include Core_models.Bundle {impl_36__new_unchecked as impl_NonZero_of_usize__new_unchecked}

include Core_models.Bundle {impl_36__get as impl_NonZero_of_usize__get}

include Core_models.Bundle {impl_36__from_str_radix as impl_NonZero_of_usize__from_str_radix}

include Core_models.Bundle {impl_36__leading_zeros as impl_NonZero_of_usize__leading_zeros}

include Core_models.Bundle {impl_36__trailing_zeros as impl_NonZero_of_usize__trailing_zeros}

include Core_models.Bundle {impl_36__lowest_one as impl_NonZero_of_usize__lowest_one}

include Core_models.Bundle {impl_36__count_ones as impl_NonZero_of_usize__count_ones}

include Core_models.Bundle {impl_36__isolate_highest_one as impl_NonZero_of_usize__isolate_highest_one}

include Core_models.Bundle {impl_36__isolate_lowest_one as impl_NonZero_of_usize__isolate_lowest_one}

include Core_models.Bundle {impl_36__rotate_left as impl_NonZero_of_usize__rotate_left}

include Core_models.Bundle {impl_36__rotate_right as impl_NonZero_of_usize__rotate_right}

include Core_models.Bundle {impl_36__swap_bytes as impl_NonZero_of_usize__swap_bytes}

include Core_models.Bundle {impl_36__to_be as impl_NonZero_of_usize__to_be}

include Core_models.Bundle {impl_36__to_le as impl_NonZero_of_usize__to_le}

include Core_models.Bundle {impl_36__from_be as impl_NonZero_of_usize__from_be}

include Core_models.Bundle {impl_36__from_le as impl_NonZero_of_usize__from_le}

include Core_models.Bundle {impl_36__checked_mul as impl_NonZero_of_usize__checked_mul}

include Core_models.Bundle {impl_36__saturating_mul as impl_NonZero_of_usize__saturating_mul}

include Core_models.Bundle {impl_36__checked_pow as impl_NonZero_of_usize__checked_pow}

include Core_models.Bundle {impl_36__saturating_pow as impl_NonZero_of_usize__saturating_pow}

include Core_models.Bundle {impl_36__highest_one as impl_NonZero_of_usize__highest_one}

include Core_models.Bundle {impl_36__ilog2 as impl_NonZero_of_usize__ilog2}

include Core_models.Bundle {impl_36__bit_width as impl_NonZero_of_usize__bit_width}

include Core_models.Bundle {impl_36__checked_add as impl_NonZero_of_usize__checked_add}

include Core_models.Bundle {impl_36__saturating_add as impl_NonZero_of_usize__saturating_add}

include Core_models.Bundle {impl_36__unchecked_add as impl_NonZero_of_usize__unchecked_add}

include Core_models.Bundle {impl_36__unchecked_mul as impl_NonZero_of_usize__unchecked_mul}

include Core_models.Bundle {impl_36__checked_next_power_of_two as impl_NonZero_of_usize__checked_next_power_of_two}

include Core_models.Bundle {impl_36__midpoint as impl_NonZero_of_usize__midpoint}

include Core_models.Bundle {impl_36__is_power_of_two as impl_NonZero_of_usize__is_power_of_two}

include Core_models.Bundle {impl_36__cast_signed as impl_NonZero_of_usize__cast_signed}

include Core_models.Bundle {impl_36__div_ceil as impl_NonZero_of_usize__div_ceil}

include Core_models.Bundle {impl_37__BITS as impl_NonZero_of_i8__BITS}

include Core_models.Bundle {impl_37__MIN as impl_NonZero_of_i8__MIN}

include Core_models.Bundle {impl_37__MAX as impl_NonZero_of_i8__MAX}

include Core_models.Bundle {impl_37__new as impl_NonZero_of_i8__new}

include Core_models.Bundle {impl_37__new_unchecked as impl_NonZero_of_i8__new_unchecked}

include Core_models.Bundle {impl_37__get as impl_NonZero_of_i8__get}

include Core_models.Bundle {impl_37__from_str_radix as impl_NonZero_of_i8__from_str_radix}

include Core_models.Bundle {impl_37__leading_zeros as impl_NonZero_of_i8__leading_zeros}

include Core_models.Bundle {impl_37__trailing_zeros as impl_NonZero_of_i8__trailing_zeros}

include Core_models.Bundle {impl_37__lowest_one as impl_NonZero_of_i8__lowest_one}

include Core_models.Bundle {impl_37__count_ones as impl_NonZero_of_i8__count_ones}

include Core_models.Bundle {impl_37__isolate_highest_one as impl_NonZero_of_i8__isolate_highest_one}

include Core_models.Bundle {impl_37__isolate_lowest_one as impl_NonZero_of_i8__isolate_lowest_one}

include Core_models.Bundle {impl_37__rotate_left as impl_NonZero_of_i8__rotate_left}

include Core_models.Bundle {impl_37__rotate_right as impl_NonZero_of_i8__rotate_right}

include Core_models.Bundle {impl_37__swap_bytes as impl_NonZero_of_i8__swap_bytes}

include Core_models.Bundle {impl_37__to_be as impl_NonZero_of_i8__to_be}

include Core_models.Bundle {impl_37__to_le as impl_NonZero_of_i8__to_le}

include Core_models.Bundle {impl_37__from_be as impl_NonZero_of_i8__from_be}

include Core_models.Bundle {impl_37__from_le as impl_NonZero_of_i8__from_le}

include Core_models.Bundle {impl_37__checked_mul as impl_NonZero_of_i8__checked_mul}

include Core_models.Bundle {impl_37__saturating_mul as impl_NonZero_of_i8__saturating_mul}

include Core_models.Bundle {impl_37__checked_pow as impl_NonZero_of_i8__checked_pow}

include Core_models.Bundle {impl_37__saturating_pow as impl_NonZero_of_i8__saturating_pow}

include Core_models.Bundle {impl_37__highest_one as impl_NonZero_of_i8__highest_one}

include Core_models.Bundle {impl_37__unchecked_mul as impl_NonZero_of_i8__unchecked_mul}

include Core_models.Bundle {impl_37__abs as impl_NonZero_of_i8__abs}

include Core_models.Bundle {impl_37__checked_abs as impl_NonZero_of_i8__checked_abs}

include Core_models.Bundle {impl_37__overflowing_abs as impl_NonZero_of_i8__overflowing_abs}

include Core_models.Bundle {impl_37__saturating_abs as impl_NonZero_of_i8__saturating_abs}

include Core_models.Bundle {impl_37__wrapping_abs as impl_NonZero_of_i8__wrapping_abs}

include Core_models.Bundle {impl_37__unsigned_abs as impl_NonZero_of_i8__unsigned_abs}

include Core_models.Bundle {impl_37__is_positive as impl_NonZero_of_i8__is_positive}

include Core_models.Bundle {impl_37__is_negative as impl_NonZero_of_i8__is_negative}

include Core_models.Bundle {impl_37__checked_neg as impl_NonZero_of_i8__checked_neg}

include Core_models.Bundle {impl_37__overflowing_neg as impl_NonZero_of_i8__overflowing_neg}

include Core_models.Bundle {impl_37__saturating_neg as impl_NonZero_of_i8__saturating_neg}

include Core_models.Bundle {impl_37__wrapping_neg as impl_NonZero_of_i8__wrapping_neg}

include Core_models.Bundle {impl_37__cast_unsigned as impl_NonZero_of_i8__cast_unsigned}

include Core_models.Bundle {impl_38__BITS as impl_NonZero_of_i16__BITS}

include Core_models.Bundle {impl_38__MIN as impl_NonZero_of_i16__MIN}

include Core_models.Bundle {impl_38__MAX as impl_NonZero_of_i16__MAX}

include Core_models.Bundle {impl_38__new as impl_NonZero_of_i16__new}

include Core_models.Bundle {impl_38__new_unchecked as impl_NonZero_of_i16__new_unchecked}

include Core_models.Bundle {impl_38__get as impl_NonZero_of_i16__get}

include Core_models.Bundle {impl_38__from_str_radix as impl_NonZero_of_i16__from_str_radix}

include Core_models.Bundle {impl_38__leading_zeros as impl_NonZero_of_i16__leading_zeros}

include Core_models.Bundle {impl_38__trailing_zeros as impl_NonZero_of_i16__trailing_zeros}

include Core_models.Bundle {impl_38__lowest_one as impl_NonZero_of_i16__lowest_one}

include Core_models.Bundle {impl_38__count_ones as impl_NonZero_of_i16__count_ones}

include Core_models.Bundle {impl_38__isolate_highest_one as impl_NonZero_of_i16__isolate_highest_one}

include Core_models.Bundle {impl_38__isolate_lowest_one as impl_NonZero_of_i16__isolate_lowest_one}

include Core_models.Bundle {impl_38__rotate_left as impl_NonZero_of_i16__rotate_left}

include Core_models.Bundle {impl_38__rotate_right as impl_NonZero_of_i16__rotate_right}

include Core_models.Bundle {impl_38__swap_bytes as impl_NonZero_of_i16__swap_bytes}

include Core_models.Bundle {impl_38__to_be as impl_NonZero_of_i16__to_be}

include Core_models.Bundle {impl_38__to_le as impl_NonZero_of_i16__to_le}

include Core_models.Bundle {impl_38__from_be as impl_NonZero_of_i16__from_be}

include Core_models.Bundle {impl_38__from_le as impl_NonZero_of_i16__from_le}

include Core_models.Bundle {impl_38__checked_mul as impl_NonZero_of_i16__checked_mul}

include Core_models.Bundle {impl_38__saturating_mul as impl_NonZero_of_i16__saturating_mul}

include Core_models.Bundle {impl_38__checked_pow as impl_NonZero_of_i16__checked_pow}

include Core_models.Bundle {impl_38__saturating_pow as impl_NonZero_of_i16__saturating_pow}

include Core_models.Bundle {impl_38__highest_one as impl_NonZero_of_i16__highest_one}

include Core_models.Bundle {impl_38__unchecked_mul as impl_NonZero_of_i16__unchecked_mul}

include Core_models.Bundle {impl_38__abs as impl_NonZero_of_i16__abs}

include Core_models.Bundle {impl_38__checked_abs as impl_NonZero_of_i16__checked_abs}

include Core_models.Bundle {impl_38__overflowing_abs as impl_NonZero_of_i16__overflowing_abs}

include Core_models.Bundle {impl_38__saturating_abs as impl_NonZero_of_i16__saturating_abs}

include Core_models.Bundle {impl_38__wrapping_abs as impl_NonZero_of_i16__wrapping_abs}

include Core_models.Bundle {impl_38__unsigned_abs as impl_NonZero_of_i16__unsigned_abs}

include Core_models.Bundle {impl_38__is_positive as impl_NonZero_of_i16__is_positive}

include Core_models.Bundle {impl_38__is_negative as impl_NonZero_of_i16__is_negative}

include Core_models.Bundle {impl_38__checked_neg as impl_NonZero_of_i16__checked_neg}

include Core_models.Bundle {impl_38__overflowing_neg as impl_NonZero_of_i16__overflowing_neg}

include Core_models.Bundle {impl_38__saturating_neg as impl_NonZero_of_i16__saturating_neg}

include Core_models.Bundle {impl_38__wrapping_neg as impl_NonZero_of_i16__wrapping_neg}

include Core_models.Bundle {impl_38__cast_unsigned as impl_NonZero_of_i16__cast_unsigned}

include Core_models.Bundle {impl_39__BITS as impl_NonZero_of_i32__BITS}

include Core_models.Bundle {impl_39__MIN as impl_NonZero_of_i32__MIN}

include Core_models.Bundle {impl_39__MAX as impl_NonZero_of_i32__MAX}

include Core_models.Bundle {impl_39__new as impl_NonZero_of_i32__new}

include Core_models.Bundle {impl_39__new_unchecked as impl_NonZero_of_i32__new_unchecked}

include Core_models.Bundle {impl_39__get as impl_NonZero_of_i32__get}

include Core_models.Bundle {impl_39__from_str_radix as impl_NonZero_of_i32__from_str_radix}

include Core_models.Bundle {impl_39__leading_zeros as impl_NonZero_of_i32__leading_zeros}

include Core_models.Bundle {impl_39__trailing_zeros as impl_NonZero_of_i32__trailing_zeros}

include Core_models.Bundle {impl_39__lowest_one as impl_NonZero_of_i32__lowest_one}

include Core_models.Bundle {impl_39__count_ones as impl_NonZero_of_i32__count_ones}

include Core_models.Bundle {impl_39__isolate_highest_one as impl_NonZero_of_i32__isolate_highest_one}

include Core_models.Bundle {impl_39__isolate_lowest_one as impl_NonZero_of_i32__isolate_lowest_one}

include Core_models.Bundle {impl_39__rotate_left as impl_NonZero_of_i32__rotate_left}

include Core_models.Bundle {impl_39__rotate_right as impl_NonZero_of_i32__rotate_right}

include Core_models.Bundle {impl_39__swap_bytes as impl_NonZero_of_i32__swap_bytes}

include Core_models.Bundle {impl_39__to_be as impl_NonZero_of_i32__to_be}

include Core_models.Bundle {impl_39__to_le as impl_NonZero_of_i32__to_le}

include Core_models.Bundle {impl_39__from_be as impl_NonZero_of_i32__from_be}

include Core_models.Bundle {impl_39__from_le as impl_NonZero_of_i32__from_le}

include Core_models.Bundle {impl_39__checked_mul as impl_NonZero_of_i32__checked_mul}

include Core_models.Bundle {impl_39__saturating_mul as impl_NonZero_of_i32__saturating_mul}

include Core_models.Bundle {impl_39__checked_pow as impl_NonZero_of_i32__checked_pow}

include Core_models.Bundle {impl_39__saturating_pow as impl_NonZero_of_i32__saturating_pow}

include Core_models.Bundle {impl_39__highest_one as impl_NonZero_of_i32__highest_one}

include Core_models.Bundle {impl_39__unchecked_mul as impl_NonZero_of_i32__unchecked_mul}

include Core_models.Bundle {impl_39__abs as impl_NonZero_of_i32__abs}

include Core_models.Bundle {impl_39__checked_abs as impl_NonZero_of_i32__checked_abs}

include Core_models.Bundle {impl_39__overflowing_abs as impl_NonZero_of_i32__overflowing_abs}

include Core_models.Bundle {impl_39__saturating_abs as impl_NonZero_of_i32__saturating_abs}

include Core_models.Bundle {impl_39__wrapping_abs as impl_NonZero_of_i32__wrapping_abs}

include Core_models.Bundle {impl_39__unsigned_abs as impl_NonZero_of_i32__unsigned_abs}

include Core_models.Bundle {impl_39__is_positive as impl_NonZero_of_i32__is_positive}

include Core_models.Bundle {impl_39__is_negative as impl_NonZero_of_i32__is_negative}

include Core_models.Bundle {impl_39__checked_neg as impl_NonZero_of_i32__checked_neg}

include Core_models.Bundle {impl_39__overflowing_neg as impl_NonZero_of_i32__overflowing_neg}

include Core_models.Bundle {impl_39__saturating_neg as impl_NonZero_of_i32__saturating_neg}

include Core_models.Bundle {impl_39__wrapping_neg as impl_NonZero_of_i32__wrapping_neg}

include Core_models.Bundle {impl_39__cast_unsigned as impl_NonZero_of_i32__cast_unsigned}

include Core_models.Bundle {impl_40__BITS as impl_NonZero_of_i64__BITS}

include Core_models.Bundle {impl_40__MIN as impl_NonZero_of_i64__MIN}

include Core_models.Bundle {impl_40__MAX as impl_NonZero_of_i64__MAX}

include Core_models.Bundle {impl_40__new as impl_NonZero_of_i64__new}

include Core_models.Bundle {impl_40__new_unchecked as impl_NonZero_of_i64__new_unchecked}

include Core_models.Bundle {impl_40__get as impl_NonZero_of_i64__get}

include Core_models.Bundle {impl_40__from_str_radix as impl_NonZero_of_i64__from_str_radix}

include Core_models.Bundle {impl_40__leading_zeros as impl_NonZero_of_i64__leading_zeros}

include Core_models.Bundle {impl_40__trailing_zeros as impl_NonZero_of_i64__trailing_zeros}

include Core_models.Bundle {impl_40__lowest_one as impl_NonZero_of_i64__lowest_one}

include Core_models.Bundle {impl_40__count_ones as impl_NonZero_of_i64__count_ones}

include Core_models.Bundle {impl_40__isolate_highest_one as impl_NonZero_of_i64__isolate_highest_one}

include Core_models.Bundle {impl_40__isolate_lowest_one as impl_NonZero_of_i64__isolate_lowest_one}

include Core_models.Bundle {impl_40__rotate_left as impl_NonZero_of_i64__rotate_left}

include Core_models.Bundle {impl_40__rotate_right as impl_NonZero_of_i64__rotate_right}

include Core_models.Bundle {impl_40__swap_bytes as impl_NonZero_of_i64__swap_bytes}

include Core_models.Bundle {impl_40__to_be as impl_NonZero_of_i64__to_be}

include Core_models.Bundle {impl_40__to_le as impl_NonZero_of_i64__to_le}

include Core_models.Bundle {impl_40__from_be as impl_NonZero_of_i64__from_be}

include Core_models.Bundle {impl_40__from_le as impl_NonZero_of_i64__from_le}

include Core_models.Bundle {impl_40__checked_mul as impl_NonZero_of_i64__checked_mul}

include Core_models.Bundle {impl_40__saturating_mul as impl_NonZero_of_i64__saturating_mul}

include Core_models.Bundle {impl_40__checked_pow as impl_NonZero_of_i64__checked_pow}

include Core_models.Bundle {impl_40__saturating_pow as impl_NonZero_of_i64__saturating_pow}

include Core_models.Bundle {impl_40__highest_one as impl_NonZero_of_i64__highest_one}

include Core_models.Bundle {impl_40__unchecked_mul as impl_NonZero_of_i64__unchecked_mul}

include Core_models.Bundle {impl_40__abs as impl_NonZero_of_i64__abs}

include Core_models.Bundle {impl_40__checked_abs as impl_NonZero_of_i64__checked_abs}

include Core_models.Bundle {impl_40__overflowing_abs as impl_NonZero_of_i64__overflowing_abs}

include Core_models.Bundle {impl_40__saturating_abs as impl_NonZero_of_i64__saturating_abs}

include Core_models.Bundle {impl_40__wrapping_abs as impl_NonZero_of_i64__wrapping_abs}

include Core_models.Bundle {impl_40__unsigned_abs as impl_NonZero_of_i64__unsigned_abs}

include Core_models.Bundle {impl_40__is_positive as impl_NonZero_of_i64__is_positive}

include Core_models.Bundle {impl_40__is_negative as impl_NonZero_of_i64__is_negative}

include Core_models.Bundle {impl_40__checked_neg as impl_NonZero_of_i64__checked_neg}

include Core_models.Bundle {impl_40__overflowing_neg as impl_NonZero_of_i64__overflowing_neg}

include Core_models.Bundle {impl_40__saturating_neg as impl_NonZero_of_i64__saturating_neg}

include Core_models.Bundle {impl_40__wrapping_neg as impl_NonZero_of_i64__wrapping_neg}

include Core_models.Bundle {impl_40__cast_unsigned as impl_NonZero_of_i64__cast_unsigned}

include Core_models.Bundle {impl_41__BITS as impl_NonZero_of_i128__BITS}

include Core_models.Bundle {impl_41__MIN as impl_NonZero_of_i128__MIN}

include Core_models.Bundle {impl_41__MAX as impl_NonZero_of_i128__MAX}

include Core_models.Bundle {impl_41__new as impl_NonZero_of_i128__new}

include Core_models.Bundle {impl_41__new_unchecked as impl_NonZero_of_i128__new_unchecked}

include Core_models.Bundle {impl_41__get as impl_NonZero_of_i128__get}

include Core_models.Bundle {impl_41__from_str_radix as impl_NonZero_of_i128__from_str_radix}

include Core_models.Bundle {impl_41__leading_zeros as impl_NonZero_of_i128__leading_zeros}

include Core_models.Bundle {impl_41__trailing_zeros as impl_NonZero_of_i128__trailing_zeros}

include Core_models.Bundle {impl_41__lowest_one as impl_NonZero_of_i128__lowest_one}

include Core_models.Bundle {impl_41__count_ones as impl_NonZero_of_i128__count_ones}

include Core_models.Bundle {impl_41__isolate_highest_one as impl_NonZero_of_i128__isolate_highest_one}

include Core_models.Bundle {impl_41__isolate_lowest_one as impl_NonZero_of_i128__isolate_lowest_one}

include Core_models.Bundle {impl_41__rotate_left as impl_NonZero_of_i128__rotate_left}

include Core_models.Bundle {impl_41__rotate_right as impl_NonZero_of_i128__rotate_right}

include Core_models.Bundle {impl_41__swap_bytes as impl_NonZero_of_i128__swap_bytes}

include Core_models.Bundle {impl_41__to_be as impl_NonZero_of_i128__to_be}

include Core_models.Bundle {impl_41__to_le as impl_NonZero_of_i128__to_le}

include Core_models.Bundle {impl_41__from_be as impl_NonZero_of_i128__from_be}

include Core_models.Bundle {impl_41__from_le as impl_NonZero_of_i128__from_le}

include Core_models.Bundle {impl_41__checked_mul as impl_NonZero_of_i128__checked_mul}

include Core_models.Bundle {impl_41__saturating_mul as impl_NonZero_of_i128__saturating_mul}

include Core_models.Bundle {impl_41__checked_pow as impl_NonZero_of_i128__checked_pow}

include Core_models.Bundle {impl_41__saturating_pow as impl_NonZero_of_i128__saturating_pow}

include Core_models.Bundle {impl_41__highest_one as impl_NonZero_of_i128__highest_one}

include Core_models.Bundle {impl_41__unchecked_mul as impl_NonZero_of_i128__unchecked_mul}

include Core_models.Bundle {impl_41__abs as impl_NonZero_of_i128__abs}

include Core_models.Bundle {impl_41__checked_abs as impl_NonZero_of_i128__checked_abs}

include Core_models.Bundle {impl_41__overflowing_abs as impl_NonZero_of_i128__overflowing_abs}

include Core_models.Bundle {impl_41__saturating_abs as impl_NonZero_of_i128__saturating_abs}

include Core_models.Bundle {impl_41__wrapping_abs as impl_NonZero_of_i128__wrapping_abs}

include Core_models.Bundle {impl_41__unsigned_abs as impl_NonZero_of_i128__unsigned_abs}

include Core_models.Bundle {impl_41__is_positive as impl_NonZero_of_i128__is_positive}

include Core_models.Bundle {impl_41__is_negative as impl_NonZero_of_i128__is_negative}

include Core_models.Bundle {impl_41__checked_neg as impl_NonZero_of_i128__checked_neg}

include Core_models.Bundle {impl_41__overflowing_neg as impl_NonZero_of_i128__overflowing_neg}

include Core_models.Bundle {impl_41__saturating_neg as impl_NonZero_of_i128__saturating_neg}

include Core_models.Bundle {impl_41__wrapping_neg as impl_NonZero_of_i128__wrapping_neg}

include Core_models.Bundle {impl_41__cast_unsigned as impl_NonZero_of_i128__cast_unsigned}

include Core_models.Bundle {impl_42__BITS as impl_NonZero_of_isize__BITS}

include Core_models.Bundle {impl_42__MIN as impl_NonZero_of_isize__MIN}

include Core_models.Bundle {impl_42__MAX as impl_NonZero_of_isize__MAX}

include Core_models.Bundle {impl_42__new as impl_NonZero_of_isize__new}

include Core_models.Bundle {impl_42__new_unchecked as impl_NonZero_of_isize__new_unchecked}

include Core_models.Bundle {impl_42__get as impl_NonZero_of_isize__get}

include Core_models.Bundle {impl_42__from_str_radix as impl_NonZero_of_isize__from_str_radix}

include Core_models.Bundle {impl_42__leading_zeros as impl_NonZero_of_isize__leading_zeros}

include Core_models.Bundle {impl_42__trailing_zeros as impl_NonZero_of_isize__trailing_zeros}

include Core_models.Bundle {impl_42__lowest_one as impl_NonZero_of_isize__lowest_one}

include Core_models.Bundle {impl_42__count_ones as impl_NonZero_of_isize__count_ones}

include Core_models.Bundle {impl_42__isolate_highest_one as impl_NonZero_of_isize__isolate_highest_one}

include Core_models.Bundle {impl_42__isolate_lowest_one as impl_NonZero_of_isize__isolate_lowest_one}

include Core_models.Bundle {impl_42__rotate_left as impl_NonZero_of_isize__rotate_left}

include Core_models.Bundle {impl_42__rotate_right as impl_NonZero_of_isize__rotate_right}

include Core_models.Bundle {impl_42__swap_bytes as impl_NonZero_of_isize__swap_bytes}

include Core_models.Bundle {impl_42__to_be as impl_NonZero_of_isize__to_be}

include Core_models.Bundle {impl_42__to_le as impl_NonZero_of_isize__to_le}

include Core_models.Bundle {impl_42__from_be as impl_NonZero_of_isize__from_be}

include Core_models.Bundle {impl_42__from_le as impl_NonZero_of_isize__from_le}

include Core_models.Bundle {impl_42__checked_mul as impl_NonZero_of_isize__checked_mul}

include Core_models.Bundle {impl_42__saturating_mul as impl_NonZero_of_isize__saturating_mul}

include Core_models.Bundle {impl_42__checked_pow as impl_NonZero_of_isize__checked_pow}

include Core_models.Bundle {impl_42__saturating_pow as impl_NonZero_of_isize__saturating_pow}

include Core_models.Bundle {impl_42__highest_one as impl_NonZero_of_isize__highest_one}

include Core_models.Bundle {impl_42__unchecked_mul as impl_NonZero_of_isize__unchecked_mul}

include Core_models.Bundle {impl_42__abs as impl_NonZero_of_isize__abs}

include Core_models.Bundle {impl_42__checked_abs as impl_NonZero_of_isize__checked_abs}

include Core_models.Bundle {impl_42__overflowing_abs as impl_NonZero_of_isize__overflowing_abs}

include Core_models.Bundle {impl_42__saturating_abs as impl_NonZero_of_isize__saturating_abs}

include Core_models.Bundle {impl_42__wrapping_abs as impl_NonZero_of_isize__wrapping_abs}

include Core_models.Bundle {impl_42__unsigned_abs as impl_NonZero_of_isize__unsigned_abs}

include Core_models.Bundle {impl_42__is_positive as impl_NonZero_of_isize__is_positive}

include Core_models.Bundle {impl_42__is_negative as impl_NonZero_of_isize__is_negative}

include Core_models.Bundle {impl_42__checked_neg as impl_NonZero_of_isize__checked_neg}

include Core_models.Bundle {impl_42__overflowing_neg as impl_NonZero_of_isize__overflowing_neg}

include Core_models.Bundle {impl_42__saturating_neg as impl_NonZero_of_isize__saturating_neg}

include Core_models.Bundle {impl_42__wrapping_neg as impl_NonZero_of_isize__wrapping_neg}

include Core_models.Bundle {impl_42__cast_unsigned as impl_NonZero_of_isize__cast_unsigned}

include Core_models.Bundle {t_Wrapping as t_Wrapping}

include Core_models.Bundle {Wrapping as Wrapping}

include Core_models.Bundle {t_Saturating as t_Saturating}

include Core_models.Bundle {Saturating as Saturating}

include Core_models.Bundle {impl_43__MIN as impl_Wrapping_of_u8__MIN}

include Core_models.Bundle {impl_43__MAX as impl_Wrapping_of_u8__MAX}

include Core_models.Bundle {impl_43__BITS as impl_Wrapping_of_u8__BITS}

include Core_models.Bundle {impl_43__count_ones as impl_Wrapping_of_u8__count_ones}

include Core_models.Bundle {impl_43__count_zeros as impl_Wrapping_of_u8__count_zeros}

include Core_models.Bundle {impl_43__trailing_zeros as impl_Wrapping_of_u8__trailing_zeros}

include Core_models.Bundle {impl_43__leading_zeros as impl_Wrapping_of_u8__leading_zeros}

include Core_models.Bundle {impl_43__rotate_left as impl_Wrapping_of_u8__rotate_left}

include Core_models.Bundle {impl_43__rotate_right as impl_Wrapping_of_u8__rotate_right}

include Core_models.Bundle {impl_43__swap_bytes as impl_Wrapping_of_u8__swap_bytes}

include Core_models.Bundle {impl_43__to_be as impl_Wrapping_of_u8__to_be}

include Core_models.Bundle {impl_43__to_le as impl_Wrapping_of_u8__to_le}

include Core_models.Bundle {impl_43__from_be as impl_Wrapping_of_u8__from_be}

include Core_models.Bundle {impl_43__from_le as impl_Wrapping_of_u8__from_le}

include Core_models.Bundle {impl_43__pow as impl_Wrapping_of_u8__pow}

include Core_models.Bundle {impl_43__is_power_of_two as impl_Wrapping_of_u8__is_power_of_two}

include Core_models.Bundle {impl_43__next_power_of_two as impl_Wrapping_of_u8__next_power_of_two}

include Core_models.Bundle {impl_44__MIN as impl_Wrapping_of_u16__MIN}

include Core_models.Bundle {impl_44__MAX as impl_Wrapping_of_u16__MAX}

include Core_models.Bundle {impl_44__BITS as impl_Wrapping_of_u16__BITS}

include Core_models.Bundle {impl_44__count_ones as impl_Wrapping_of_u16__count_ones}

include Core_models.Bundle {impl_44__count_zeros as impl_Wrapping_of_u16__count_zeros}

include Core_models.Bundle {impl_44__trailing_zeros as impl_Wrapping_of_u16__trailing_zeros}

include Core_models.Bundle {impl_44__leading_zeros as impl_Wrapping_of_u16__leading_zeros}

include Core_models.Bundle {impl_44__rotate_left as impl_Wrapping_of_u16__rotate_left}

include Core_models.Bundle {impl_44__rotate_right as impl_Wrapping_of_u16__rotate_right}

include Core_models.Bundle {impl_44__swap_bytes as impl_Wrapping_of_u16__swap_bytes}

include Core_models.Bundle {impl_44__to_be as impl_Wrapping_of_u16__to_be}

include Core_models.Bundle {impl_44__to_le as impl_Wrapping_of_u16__to_le}

include Core_models.Bundle {impl_44__from_be as impl_Wrapping_of_u16__from_be}

include Core_models.Bundle {impl_44__from_le as impl_Wrapping_of_u16__from_le}

include Core_models.Bundle {impl_44__pow as impl_Wrapping_of_u16__pow}

include Core_models.Bundle {impl_44__is_power_of_two as impl_Wrapping_of_u16__is_power_of_two}

include Core_models.Bundle {impl_44__next_power_of_two as impl_Wrapping_of_u16__next_power_of_two}

include Core_models.Bundle {impl_45__MIN as impl_Wrapping_of_u32__MIN}

include Core_models.Bundle {impl_45__MAX as impl_Wrapping_of_u32__MAX}

include Core_models.Bundle {impl_45__BITS as impl_Wrapping_of_u32__BITS}

include Core_models.Bundle {impl_45__count_ones as impl_Wrapping_of_u32__count_ones}

include Core_models.Bundle {impl_45__count_zeros as impl_Wrapping_of_u32__count_zeros}

include Core_models.Bundle {impl_45__trailing_zeros as impl_Wrapping_of_u32__trailing_zeros}

include Core_models.Bundle {impl_45__leading_zeros as impl_Wrapping_of_u32__leading_zeros}

include Core_models.Bundle {impl_45__rotate_left as impl_Wrapping_of_u32__rotate_left}

include Core_models.Bundle {impl_45__rotate_right as impl_Wrapping_of_u32__rotate_right}

include Core_models.Bundle {impl_45__swap_bytes as impl_Wrapping_of_u32__swap_bytes}

include Core_models.Bundle {impl_45__to_be as impl_Wrapping_of_u32__to_be}

include Core_models.Bundle {impl_45__to_le as impl_Wrapping_of_u32__to_le}

include Core_models.Bundle {impl_45__from_be as impl_Wrapping_of_u32__from_be}

include Core_models.Bundle {impl_45__from_le as impl_Wrapping_of_u32__from_le}

include Core_models.Bundle {impl_45__pow as impl_Wrapping_of_u32__pow}

include Core_models.Bundle {impl_45__is_power_of_two as impl_Wrapping_of_u32__is_power_of_two}

include Core_models.Bundle {impl_45__next_power_of_two as impl_Wrapping_of_u32__next_power_of_two}

include Core_models.Bundle {impl_46__MIN as impl_Wrapping_of_u64__MIN}

include Core_models.Bundle {impl_46__MAX as impl_Wrapping_of_u64__MAX}

include Core_models.Bundle {impl_46__BITS as impl_Wrapping_of_u64__BITS}

include Core_models.Bundle {impl_46__count_ones as impl_Wrapping_of_u64__count_ones}

include Core_models.Bundle {impl_46__count_zeros as impl_Wrapping_of_u64__count_zeros}

include Core_models.Bundle {impl_46__trailing_zeros as impl_Wrapping_of_u64__trailing_zeros}

include Core_models.Bundle {impl_46__leading_zeros as impl_Wrapping_of_u64__leading_zeros}

include Core_models.Bundle {impl_46__rotate_left as impl_Wrapping_of_u64__rotate_left}

include Core_models.Bundle {impl_46__rotate_right as impl_Wrapping_of_u64__rotate_right}

include Core_models.Bundle {impl_46__swap_bytes as impl_Wrapping_of_u64__swap_bytes}

include Core_models.Bundle {impl_46__to_be as impl_Wrapping_of_u64__to_be}

include Core_models.Bundle {impl_46__to_le as impl_Wrapping_of_u64__to_le}

include Core_models.Bundle {impl_46__from_be as impl_Wrapping_of_u64__from_be}

include Core_models.Bundle {impl_46__from_le as impl_Wrapping_of_u64__from_le}

include Core_models.Bundle {impl_46__pow as impl_Wrapping_of_u64__pow}

include Core_models.Bundle {impl_46__is_power_of_two as impl_Wrapping_of_u64__is_power_of_two}

include Core_models.Bundle {impl_46__next_power_of_two as impl_Wrapping_of_u64__next_power_of_two}

include Core_models.Bundle {impl_47__MIN as impl_Wrapping_of_u128__MIN}

include Core_models.Bundle {impl_47__MAX as impl_Wrapping_of_u128__MAX}

include Core_models.Bundle {impl_47__BITS as impl_Wrapping_of_u128__BITS}

include Core_models.Bundle {impl_47__count_ones as impl_Wrapping_of_u128__count_ones}

include Core_models.Bundle {impl_47__count_zeros as impl_Wrapping_of_u128__count_zeros}

include Core_models.Bundle {impl_47__trailing_zeros as impl_Wrapping_of_u128__trailing_zeros}

include Core_models.Bundle {impl_47__leading_zeros as impl_Wrapping_of_u128__leading_zeros}

include Core_models.Bundle {impl_47__rotate_left as impl_Wrapping_of_u128__rotate_left}

include Core_models.Bundle {impl_47__rotate_right as impl_Wrapping_of_u128__rotate_right}

include Core_models.Bundle {impl_47__swap_bytes as impl_Wrapping_of_u128__swap_bytes}

include Core_models.Bundle {impl_47__to_be as impl_Wrapping_of_u128__to_be}

include Core_models.Bundle {impl_47__to_le as impl_Wrapping_of_u128__to_le}

include Core_models.Bundle {impl_47__from_be as impl_Wrapping_of_u128__from_be}

include Core_models.Bundle {impl_47__from_le as impl_Wrapping_of_u128__from_le}

include Core_models.Bundle {impl_47__pow as impl_Wrapping_of_u128__pow}

include Core_models.Bundle {impl_47__is_power_of_two as impl_Wrapping_of_u128__is_power_of_two}

include Core_models.Bundle {impl_47__next_power_of_two as impl_Wrapping_of_u128__next_power_of_two}

include Core_models.Bundle {impl_48__MIN as impl_Wrapping_of_usize__MIN}

include Core_models.Bundle {impl_48__MAX as impl_Wrapping_of_usize__MAX}

include Core_models.Bundle {impl_48__BITS as impl_Wrapping_of_usize__BITS}

include Core_models.Bundle {impl_48__count_ones as impl_Wrapping_of_usize__count_ones}

include Core_models.Bundle {impl_48__count_zeros as impl_Wrapping_of_usize__count_zeros}

include Core_models.Bundle {impl_48__trailing_zeros as impl_Wrapping_of_usize__trailing_zeros}

include Core_models.Bundle {impl_48__leading_zeros as impl_Wrapping_of_usize__leading_zeros}

include Core_models.Bundle {impl_48__rotate_left as impl_Wrapping_of_usize__rotate_left}

include Core_models.Bundle {impl_48__rotate_right as impl_Wrapping_of_usize__rotate_right}

include Core_models.Bundle {impl_48__swap_bytes as impl_Wrapping_of_usize__swap_bytes}

include Core_models.Bundle {impl_48__to_be as impl_Wrapping_of_usize__to_be}

include Core_models.Bundle {impl_48__to_le as impl_Wrapping_of_usize__to_le}

include Core_models.Bundle {impl_48__from_be as impl_Wrapping_of_usize__from_be}

include Core_models.Bundle {impl_48__from_le as impl_Wrapping_of_usize__from_le}

include Core_models.Bundle {impl_48__pow as impl_Wrapping_of_usize__pow}

include Core_models.Bundle {impl_48__is_power_of_two as impl_Wrapping_of_usize__is_power_of_two}

include Core_models.Bundle {impl_48__next_power_of_two as impl_Wrapping_of_usize__next_power_of_two}

include Core_models.Bundle {impl_49__MIN as impl_Wrapping_of_i8__MIN}

include Core_models.Bundle {impl_49__MAX as impl_Wrapping_of_i8__MAX}

include Core_models.Bundle {impl_49__BITS as impl_Wrapping_of_i8__BITS}

include Core_models.Bundle {impl_49__count_ones as impl_Wrapping_of_i8__count_ones}

include Core_models.Bundle {impl_49__count_zeros as impl_Wrapping_of_i8__count_zeros}

include Core_models.Bundle {impl_49__trailing_zeros as impl_Wrapping_of_i8__trailing_zeros}

include Core_models.Bundle {impl_49__leading_zeros as impl_Wrapping_of_i8__leading_zeros}

include Core_models.Bundle {impl_49__rotate_left as impl_Wrapping_of_i8__rotate_left}

include Core_models.Bundle {impl_49__rotate_right as impl_Wrapping_of_i8__rotate_right}

include Core_models.Bundle {impl_49__swap_bytes as impl_Wrapping_of_i8__swap_bytes}

include Core_models.Bundle {impl_49__to_be as impl_Wrapping_of_i8__to_be}

include Core_models.Bundle {impl_49__to_le as impl_Wrapping_of_i8__to_le}

include Core_models.Bundle {impl_49__from_be as impl_Wrapping_of_i8__from_be}

include Core_models.Bundle {impl_49__from_le as impl_Wrapping_of_i8__from_le}

include Core_models.Bundle {impl_49__pow as impl_Wrapping_of_i8__pow}

include Core_models.Bundle {impl_49__abs as impl_Wrapping_of_i8__abs}

include Core_models.Bundle {impl_49__signum as impl_Wrapping_of_i8__signum}

include Core_models.Bundle {impl_49__is_positive as impl_Wrapping_of_i8__is_positive}

include Core_models.Bundle {impl_49__is_negative as impl_Wrapping_of_i8__is_negative}

include Core_models.Bundle {impl_50__MIN as impl_Wrapping_of_i16__MIN}

include Core_models.Bundle {impl_50__MAX as impl_Wrapping_of_i16__MAX}

include Core_models.Bundle {impl_50__BITS as impl_Wrapping_of_i16__BITS}

include Core_models.Bundle {impl_50__count_ones as impl_Wrapping_of_i16__count_ones}

include Core_models.Bundle {impl_50__count_zeros as impl_Wrapping_of_i16__count_zeros}

include Core_models.Bundle {impl_50__trailing_zeros as impl_Wrapping_of_i16__trailing_zeros}

include Core_models.Bundle {impl_50__leading_zeros as impl_Wrapping_of_i16__leading_zeros}

include Core_models.Bundle {impl_50__rotate_left as impl_Wrapping_of_i16__rotate_left}

include Core_models.Bundle {impl_50__rotate_right as impl_Wrapping_of_i16__rotate_right}

include Core_models.Bundle {impl_50__swap_bytes as impl_Wrapping_of_i16__swap_bytes}

include Core_models.Bundle {impl_50__to_be as impl_Wrapping_of_i16__to_be}

include Core_models.Bundle {impl_50__to_le as impl_Wrapping_of_i16__to_le}

include Core_models.Bundle {impl_50__from_be as impl_Wrapping_of_i16__from_be}

include Core_models.Bundle {impl_50__from_le as impl_Wrapping_of_i16__from_le}

include Core_models.Bundle {impl_50__pow as impl_Wrapping_of_i16__pow}

include Core_models.Bundle {impl_50__abs as impl_Wrapping_of_i16__abs}

include Core_models.Bundle {impl_50__signum as impl_Wrapping_of_i16__signum}

include Core_models.Bundle {impl_50__is_positive as impl_Wrapping_of_i16__is_positive}

include Core_models.Bundle {impl_50__is_negative as impl_Wrapping_of_i16__is_negative}

include Core_models.Bundle {impl_51__MIN as impl_Wrapping_of_i32__MIN}

include Core_models.Bundle {impl_51__MAX as impl_Wrapping_of_i32__MAX}

include Core_models.Bundle {impl_51__BITS as impl_Wrapping_of_i32__BITS}

include Core_models.Bundle {impl_51__count_ones as impl_Wrapping_of_i32__count_ones}

include Core_models.Bundle {impl_51__count_zeros as impl_Wrapping_of_i32__count_zeros}

include Core_models.Bundle {impl_51__trailing_zeros as impl_Wrapping_of_i32__trailing_zeros}

include Core_models.Bundle {impl_51__leading_zeros as impl_Wrapping_of_i32__leading_zeros}

include Core_models.Bundle {impl_51__rotate_left as impl_Wrapping_of_i32__rotate_left}

include Core_models.Bundle {impl_51__rotate_right as impl_Wrapping_of_i32__rotate_right}

include Core_models.Bundle {impl_51__swap_bytes as impl_Wrapping_of_i32__swap_bytes}

include Core_models.Bundle {impl_51__to_be as impl_Wrapping_of_i32__to_be}

include Core_models.Bundle {impl_51__to_le as impl_Wrapping_of_i32__to_le}

include Core_models.Bundle {impl_51__from_be as impl_Wrapping_of_i32__from_be}

include Core_models.Bundle {impl_51__from_le as impl_Wrapping_of_i32__from_le}

include Core_models.Bundle {impl_51__pow as impl_Wrapping_of_i32__pow}

include Core_models.Bundle {impl_51__abs as impl_Wrapping_of_i32__abs}

include Core_models.Bundle {impl_51__signum as impl_Wrapping_of_i32__signum}

include Core_models.Bundle {impl_51__is_positive as impl_Wrapping_of_i32__is_positive}

include Core_models.Bundle {impl_51__is_negative as impl_Wrapping_of_i32__is_negative}

include Core_models.Bundle {impl_52__MIN as impl_Wrapping_of_i64__MIN}

include Core_models.Bundle {impl_52__MAX as impl_Wrapping_of_i64__MAX}

include Core_models.Bundle {impl_52__BITS as impl_Wrapping_of_i64__BITS}

include Core_models.Bundle {impl_52__count_ones as impl_Wrapping_of_i64__count_ones}

include Core_models.Bundle {impl_52__count_zeros as impl_Wrapping_of_i64__count_zeros}

include Core_models.Bundle {impl_52__trailing_zeros as impl_Wrapping_of_i64__trailing_zeros}

include Core_models.Bundle {impl_52__leading_zeros as impl_Wrapping_of_i64__leading_zeros}

include Core_models.Bundle {impl_52__rotate_left as impl_Wrapping_of_i64__rotate_left}

include Core_models.Bundle {impl_52__rotate_right as impl_Wrapping_of_i64__rotate_right}

include Core_models.Bundle {impl_52__swap_bytes as impl_Wrapping_of_i64__swap_bytes}

include Core_models.Bundle {impl_52__to_be as impl_Wrapping_of_i64__to_be}

include Core_models.Bundle {impl_52__to_le as impl_Wrapping_of_i64__to_le}

include Core_models.Bundle {impl_52__from_be as impl_Wrapping_of_i64__from_be}

include Core_models.Bundle {impl_52__from_le as impl_Wrapping_of_i64__from_le}

include Core_models.Bundle {impl_52__pow as impl_Wrapping_of_i64__pow}

include Core_models.Bundle {impl_52__abs as impl_Wrapping_of_i64__abs}

include Core_models.Bundle {impl_52__signum as impl_Wrapping_of_i64__signum}

include Core_models.Bundle {impl_52__is_positive as impl_Wrapping_of_i64__is_positive}

include Core_models.Bundle {impl_52__is_negative as impl_Wrapping_of_i64__is_negative}

include Core_models.Bundle {impl_53__MIN as impl_Wrapping_of_i128__MIN}

include Core_models.Bundle {impl_53__MAX as impl_Wrapping_of_i128__MAX}

include Core_models.Bundle {impl_53__BITS as impl_Wrapping_of_i128__BITS}

include Core_models.Bundle {impl_53__count_ones as impl_Wrapping_of_i128__count_ones}

include Core_models.Bundle {impl_53__count_zeros as impl_Wrapping_of_i128__count_zeros}

include Core_models.Bundle {impl_53__trailing_zeros as impl_Wrapping_of_i128__trailing_zeros}

include Core_models.Bundle {impl_53__leading_zeros as impl_Wrapping_of_i128__leading_zeros}

include Core_models.Bundle {impl_53__rotate_left as impl_Wrapping_of_i128__rotate_left}

include Core_models.Bundle {impl_53__rotate_right as impl_Wrapping_of_i128__rotate_right}

include Core_models.Bundle {impl_53__swap_bytes as impl_Wrapping_of_i128__swap_bytes}

include Core_models.Bundle {impl_53__to_be as impl_Wrapping_of_i128__to_be}

include Core_models.Bundle {impl_53__to_le as impl_Wrapping_of_i128__to_le}

include Core_models.Bundle {impl_53__from_be as impl_Wrapping_of_i128__from_be}

include Core_models.Bundle {impl_53__from_le as impl_Wrapping_of_i128__from_le}

include Core_models.Bundle {impl_53__pow as impl_Wrapping_of_i128__pow}

include Core_models.Bundle {impl_53__abs as impl_Wrapping_of_i128__abs}

include Core_models.Bundle {impl_53__signum as impl_Wrapping_of_i128__signum}

include Core_models.Bundle {impl_53__is_positive as impl_Wrapping_of_i128__is_positive}

include Core_models.Bundle {impl_53__is_negative as impl_Wrapping_of_i128__is_negative}

include Core_models.Bundle {impl_54__MIN as impl_Wrapping_of_isize__MIN}

include Core_models.Bundle {impl_54__MAX as impl_Wrapping_of_isize__MAX}

include Core_models.Bundle {impl_54__BITS as impl_Wrapping_of_isize__BITS}

include Core_models.Bundle {impl_54__count_ones as impl_Wrapping_of_isize__count_ones}

include Core_models.Bundle {impl_54__count_zeros as impl_Wrapping_of_isize__count_zeros}

include Core_models.Bundle {impl_54__trailing_zeros as impl_Wrapping_of_isize__trailing_zeros}

include Core_models.Bundle {impl_54__leading_zeros as impl_Wrapping_of_isize__leading_zeros}

include Core_models.Bundle {impl_54__rotate_left as impl_Wrapping_of_isize__rotate_left}

include Core_models.Bundle {impl_54__rotate_right as impl_Wrapping_of_isize__rotate_right}

include Core_models.Bundle {impl_54__swap_bytes as impl_Wrapping_of_isize__swap_bytes}

include Core_models.Bundle {impl_54__to_be as impl_Wrapping_of_isize__to_be}

include Core_models.Bundle {impl_54__to_le as impl_Wrapping_of_isize__to_le}

include Core_models.Bundle {impl_54__from_be as impl_Wrapping_of_isize__from_be}

include Core_models.Bundle {impl_54__from_le as impl_Wrapping_of_isize__from_le}

include Core_models.Bundle {impl_54__pow as impl_Wrapping_of_isize__pow}

include Core_models.Bundle {impl_54__abs as impl_Wrapping_of_isize__abs}

include Core_models.Bundle {impl_54__signum as impl_Wrapping_of_isize__signum}

include Core_models.Bundle {impl_54__is_positive as impl_Wrapping_of_isize__is_positive}

include Core_models.Bundle {impl_54__is_negative as impl_Wrapping_of_isize__is_negative}

include Core_models.Bundle {impl_55__MIN as impl_Saturating_of_u8__MIN}

include Core_models.Bundle {impl_55__MAX as impl_Saturating_of_u8__MAX}

include Core_models.Bundle {impl_55__BITS as impl_Saturating_of_u8__BITS}

include Core_models.Bundle {impl_55__count_ones as impl_Saturating_of_u8__count_ones}

include Core_models.Bundle {impl_55__count_zeros as impl_Saturating_of_u8__count_zeros}

include Core_models.Bundle {impl_55__trailing_zeros as impl_Saturating_of_u8__trailing_zeros}

include Core_models.Bundle {impl_55__leading_zeros as impl_Saturating_of_u8__leading_zeros}

include Core_models.Bundle {impl_55__rotate_left as impl_Saturating_of_u8__rotate_left}

include Core_models.Bundle {impl_55__rotate_right as impl_Saturating_of_u8__rotate_right}

include Core_models.Bundle {impl_55__swap_bytes as impl_Saturating_of_u8__swap_bytes}

include Core_models.Bundle {impl_55__to_be as impl_Saturating_of_u8__to_be}

include Core_models.Bundle {impl_55__to_le as impl_Saturating_of_u8__to_le}

include Core_models.Bundle {impl_55__from_be as impl_Saturating_of_u8__from_be}

include Core_models.Bundle {impl_55__from_le as impl_Saturating_of_u8__from_le}

include Core_models.Bundle {impl_55__pow as impl_Saturating_of_u8__pow}

include Core_models.Bundle {impl_55__is_power_of_two as impl_Saturating_of_u8__is_power_of_two}

include Core_models.Bundle {impl_56__MIN as impl_Saturating_of_u16__MIN}

include Core_models.Bundle {impl_56__MAX as impl_Saturating_of_u16__MAX}

include Core_models.Bundle {impl_56__BITS as impl_Saturating_of_u16__BITS}

include Core_models.Bundle {impl_56__count_ones as impl_Saturating_of_u16__count_ones}

include Core_models.Bundle {impl_56__count_zeros as impl_Saturating_of_u16__count_zeros}

include Core_models.Bundle {impl_56__trailing_zeros as impl_Saturating_of_u16__trailing_zeros}

include Core_models.Bundle {impl_56__leading_zeros as impl_Saturating_of_u16__leading_zeros}

include Core_models.Bundle {impl_56__rotate_left as impl_Saturating_of_u16__rotate_left}

include Core_models.Bundle {impl_56__rotate_right as impl_Saturating_of_u16__rotate_right}

include Core_models.Bundle {impl_56__swap_bytes as impl_Saturating_of_u16__swap_bytes}

include Core_models.Bundle {impl_56__to_be as impl_Saturating_of_u16__to_be}

include Core_models.Bundle {impl_56__to_le as impl_Saturating_of_u16__to_le}

include Core_models.Bundle {impl_56__from_be as impl_Saturating_of_u16__from_be}

include Core_models.Bundle {impl_56__from_le as impl_Saturating_of_u16__from_le}

include Core_models.Bundle {impl_56__pow as impl_Saturating_of_u16__pow}

include Core_models.Bundle {impl_56__is_power_of_two as impl_Saturating_of_u16__is_power_of_two}

include Core_models.Bundle {impl_57__MIN as impl_Saturating_of_u32__MIN}

include Core_models.Bundle {impl_57__MAX as impl_Saturating_of_u32__MAX}

include Core_models.Bundle {impl_57__BITS as impl_Saturating_of_u32__BITS}

include Core_models.Bundle {impl_57__count_ones as impl_Saturating_of_u32__count_ones}

include Core_models.Bundle {impl_57__count_zeros as impl_Saturating_of_u32__count_zeros}

include Core_models.Bundle {impl_57__trailing_zeros as impl_Saturating_of_u32__trailing_zeros}

include Core_models.Bundle {impl_57__leading_zeros as impl_Saturating_of_u32__leading_zeros}

include Core_models.Bundle {impl_57__rotate_left as impl_Saturating_of_u32__rotate_left}

include Core_models.Bundle {impl_57__rotate_right as impl_Saturating_of_u32__rotate_right}

include Core_models.Bundle {impl_57__swap_bytes as impl_Saturating_of_u32__swap_bytes}

include Core_models.Bundle {impl_57__to_be as impl_Saturating_of_u32__to_be}

include Core_models.Bundle {impl_57__to_le as impl_Saturating_of_u32__to_le}

include Core_models.Bundle {impl_57__from_be as impl_Saturating_of_u32__from_be}

include Core_models.Bundle {impl_57__from_le as impl_Saturating_of_u32__from_le}

include Core_models.Bundle {impl_57__pow as impl_Saturating_of_u32__pow}

include Core_models.Bundle {impl_57__is_power_of_two as impl_Saturating_of_u32__is_power_of_two}

include Core_models.Bundle {impl_58__MIN as impl_Saturating_of_u64__MIN}

include Core_models.Bundle {impl_58__MAX as impl_Saturating_of_u64__MAX}

include Core_models.Bundle {impl_58__BITS as impl_Saturating_of_u64__BITS}

include Core_models.Bundle {impl_58__count_ones as impl_Saturating_of_u64__count_ones}

include Core_models.Bundle {impl_58__count_zeros as impl_Saturating_of_u64__count_zeros}

include Core_models.Bundle {impl_58__trailing_zeros as impl_Saturating_of_u64__trailing_zeros}

include Core_models.Bundle {impl_58__leading_zeros as impl_Saturating_of_u64__leading_zeros}

include Core_models.Bundle {impl_58__rotate_left as impl_Saturating_of_u64__rotate_left}

include Core_models.Bundle {impl_58__rotate_right as impl_Saturating_of_u64__rotate_right}

include Core_models.Bundle {impl_58__swap_bytes as impl_Saturating_of_u64__swap_bytes}

include Core_models.Bundle {impl_58__to_be as impl_Saturating_of_u64__to_be}

include Core_models.Bundle {impl_58__to_le as impl_Saturating_of_u64__to_le}

include Core_models.Bundle {impl_58__from_be as impl_Saturating_of_u64__from_be}

include Core_models.Bundle {impl_58__from_le as impl_Saturating_of_u64__from_le}

include Core_models.Bundle {impl_58__pow as impl_Saturating_of_u64__pow}

include Core_models.Bundle {impl_58__is_power_of_two as impl_Saturating_of_u64__is_power_of_two}

include Core_models.Bundle {impl_59__MIN as impl_Saturating_of_u128__MIN}

include Core_models.Bundle {impl_59__MAX as impl_Saturating_of_u128__MAX}

include Core_models.Bundle {impl_59__BITS as impl_Saturating_of_u128__BITS}

include Core_models.Bundle {impl_59__count_ones as impl_Saturating_of_u128__count_ones}

include Core_models.Bundle {impl_59__count_zeros as impl_Saturating_of_u128__count_zeros}

include Core_models.Bundle {impl_59__trailing_zeros as impl_Saturating_of_u128__trailing_zeros}

include Core_models.Bundle {impl_59__leading_zeros as impl_Saturating_of_u128__leading_zeros}

include Core_models.Bundle {impl_59__rotate_left as impl_Saturating_of_u128__rotate_left}

include Core_models.Bundle {impl_59__rotate_right as impl_Saturating_of_u128__rotate_right}

include Core_models.Bundle {impl_59__swap_bytes as impl_Saturating_of_u128__swap_bytes}

include Core_models.Bundle {impl_59__to_be as impl_Saturating_of_u128__to_be}

include Core_models.Bundle {impl_59__to_le as impl_Saturating_of_u128__to_le}

include Core_models.Bundle {impl_59__from_be as impl_Saturating_of_u128__from_be}

include Core_models.Bundle {impl_59__from_le as impl_Saturating_of_u128__from_le}

include Core_models.Bundle {impl_59__pow as impl_Saturating_of_u128__pow}

include Core_models.Bundle {impl_59__is_power_of_two as impl_Saturating_of_u128__is_power_of_two}

include Core_models.Bundle {impl_60__MIN as impl_Saturating_of_usize__MIN}

include Core_models.Bundle {impl_60__MAX as impl_Saturating_of_usize__MAX}

include Core_models.Bundle {impl_60__BITS as impl_Saturating_of_usize__BITS}

include Core_models.Bundle {impl_60__count_ones as impl_Saturating_of_usize__count_ones}

include Core_models.Bundle {impl_60__count_zeros as impl_Saturating_of_usize__count_zeros}

include Core_models.Bundle {impl_60__trailing_zeros as impl_Saturating_of_usize__trailing_zeros}

include Core_models.Bundle {impl_60__leading_zeros as impl_Saturating_of_usize__leading_zeros}

include Core_models.Bundle {impl_60__rotate_left as impl_Saturating_of_usize__rotate_left}

include Core_models.Bundle {impl_60__rotate_right as impl_Saturating_of_usize__rotate_right}

include Core_models.Bundle {impl_60__swap_bytes as impl_Saturating_of_usize__swap_bytes}

include Core_models.Bundle {impl_60__to_be as impl_Saturating_of_usize__to_be}

include Core_models.Bundle {impl_60__to_le as impl_Saturating_of_usize__to_le}

include Core_models.Bundle {impl_60__from_be as impl_Saturating_of_usize__from_be}

include Core_models.Bundle {impl_60__from_le as impl_Saturating_of_usize__from_le}

include Core_models.Bundle {impl_60__pow as impl_Saturating_of_usize__pow}

include Core_models.Bundle {impl_60__is_power_of_two as impl_Saturating_of_usize__is_power_of_two}

include Core_models.Bundle {impl_61__MIN as impl_Saturating_of_i8__MIN}

include Core_models.Bundle {impl_61__MAX as impl_Saturating_of_i8__MAX}

include Core_models.Bundle {impl_61__BITS as impl_Saturating_of_i8__BITS}

include Core_models.Bundle {impl_61__count_ones as impl_Saturating_of_i8__count_ones}

include Core_models.Bundle {impl_61__count_zeros as impl_Saturating_of_i8__count_zeros}

include Core_models.Bundle {impl_61__trailing_zeros as impl_Saturating_of_i8__trailing_zeros}

include Core_models.Bundle {impl_61__leading_zeros as impl_Saturating_of_i8__leading_zeros}

include Core_models.Bundle {impl_61__rotate_left as impl_Saturating_of_i8__rotate_left}

include Core_models.Bundle {impl_61__rotate_right as impl_Saturating_of_i8__rotate_right}

include Core_models.Bundle {impl_61__swap_bytes as impl_Saturating_of_i8__swap_bytes}

include Core_models.Bundle {impl_61__to_be as impl_Saturating_of_i8__to_be}

include Core_models.Bundle {impl_61__to_le as impl_Saturating_of_i8__to_le}

include Core_models.Bundle {impl_61__from_be as impl_Saturating_of_i8__from_be}

include Core_models.Bundle {impl_61__from_le as impl_Saturating_of_i8__from_le}

include Core_models.Bundle {impl_61__pow as impl_Saturating_of_i8__pow}

include Core_models.Bundle {impl_61__abs as impl_Saturating_of_i8__abs}

include Core_models.Bundle {impl_61__signum as impl_Saturating_of_i8__signum}

include Core_models.Bundle {impl_61__is_positive as impl_Saturating_of_i8__is_positive}

include Core_models.Bundle {impl_61__is_negative as impl_Saturating_of_i8__is_negative}

include Core_models.Bundle {impl_62__MIN as impl_Saturating_of_i16__MIN}

include Core_models.Bundle {impl_62__MAX as impl_Saturating_of_i16__MAX}

include Core_models.Bundle {impl_62__BITS as impl_Saturating_of_i16__BITS}

include Core_models.Bundle {impl_62__count_ones as impl_Saturating_of_i16__count_ones}

include Core_models.Bundle {impl_62__count_zeros as impl_Saturating_of_i16__count_zeros}

include Core_models.Bundle {impl_62__trailing_zeros as impl_Saturating_of_i16__trailing_zeros}

include Core_models.Bundle {impl_62__leading_zeros as impl_Saturating_of_i16__leading_zeros}

include Core_models.Bundle {impl_62__rotate_left as impl_Saturating_of_i16__rotate_left}

include Core_models.Bundle {impl_62__rotate_right as impl_Saturating_of_i16__rotate_right}

include Core_models.Bundle {impl_62__swap_bytes as impl_Saturating_of_i16__swap_bytes}

include Core_models.Bundle {impl_62__to_be as impl_Saturating_of_i16__to_be}

include Core_models.Bundle {impl_62__to_le as impl_Saturating_of_i16__to_le}

include Core_models.Bundle {impl_62__from_be as impl_Saturating_of_i16__from_be}

include Core_models.Bundle {impl_62__from_le as impl_Saturating_of_i16__from_le}

include Core_models.Bundle {impl_62__pow as impl_Saturating_of_i16__pow}

include Core_models.Bundle {impl_62__abs as impl_Saturating_of_i16__abs}

include Core_models.Bundle {impl_62__signum as impl_Saturating_of_i16__signum}

include Core_models.Bundle {impl_62__is_positive as impl_Saturating_of_i16__is_positive}

include Core_models.Bundle {impl_62__is_negative as impl_Saturating_of_i16__is_negative}

include Core_models.Bundle {impl_63__MIN as impl_Saturating_of_i32__MIN}

include Core_models.Bundle {impl_63__MAX as impl_Saturating_of_i32__MAX}

include Core_models.Bundle {impl_63__BITS as impl_Saturating_of_i32__BITS}

include Core_models.Bundle {impl_63__count_ones as impl_Saturating_of_i32__count_ones}

include Core_models.Bundle {impl_63__count_zeros as impl_Saturating_of_i32__count_zeros}

include Core_models.Bundle {impl_63__trailing_zeros as impl_Saturating_of_i32__trailing_zeros}

include Core_models.Bundle {impl_63__leading_zeros as impl_Saturating_of_i32__leading_zeros}

include Core_models.Bundle {impl_63__rotate_left as impl_Saturating_of_i32__rotate_left}

include Core_models.Bundle {impl_63__rotate_right as impl_Saturating_of_i32__rotate_right}

include Core_models.Bundle {impl_63__swap_bytes as impl_Saturating_of_i32__swap_bytes}

include Core_models.Bundle {impl_63__to_be as impl_Saturating_of_i32__to_be}

include Core_models.Bundle {impl_63__to_le as impl_Saturating_of_i32__to_le}

include Core_models.Bundle {impl_63__from_be as impl_Saturating_of_i32__from_be}

include Core_models.Bundle {impl_63__from_le as impl_Saturating_of_i32__from_le}

include Core_models.Bundle {impl_63__pow as impl_Saturating_of_i32__pow}

include Core_models.Bundle {impl_63__abs as impl_Saturating_of_i32__abs}

include Core_models.Bundle {impl_63__signum as impl_Saturating_of_i32__signum}

include Core_models.Bundle {impl_63__is_positive as impl_Saturating_of_i32__is_positive}

include Core_models.Bundle {impl_63__is_negative as impl_Saturating_of_i32__is_negative}

include Core_models.Bundle {impl_64__MIN as impl_Saturating_of_i64__MIN}

include Core_models.Bundle {impl_64__MAX as impl_Saturating_of_i64__MAX}

include Core_models.Bundle {impl_64__BITS as impl_Saturating_of_i64__BITS}

include Core_models.Bundle {impl_64__count_ones as impl_Saturating_of_i64__count_ones}

include Core_models.Bundle {impl_64__count_zeros as impl_Saturating_of_i64__count_zeros}

include Core_models.Bundle {impl_64__trailing_zeros as impl_Saturating_of_i64__trailing_zeros}

include Core_models.Bundle {impl_64__leading_zeros as impl_Saturating_of_i64__leading_zeros}

include Core_models.Bundle {impl_64__rotate_left as impl_Saturating_of_i64__rotate_left}

include Core_models.Bundle {impl_64__rotate_right as impl_Saturating_of_i64__rotate_right}

include Core_models.Bundle {impl_64__swap_bytes as impl_Saturating_of_i64__swap_bytes}

include Core_models.Bundle {impl_64__to_be as impl_Saturating_of_i64__to_be}

include Core_models.Bundle {impl_64__to_le as impl_Saturating_of_i64__to_le}

include Core_models.Bundle {impl_64__from_be as impl_Saturating_of_i64__from_be}

include Core_models.Bundle {impl_64__from_le as impl_Saturating_of_i64__from_le}

include Core_models.Bundle {impl_64__pow as impl_Saturating_of_i64__pow}

include Core_models.Bundle {impl_64__abs as impl_Saturating_of_i64__abs}

include Core_models.Bundle {impl_64__signum as impl_Saturating_of_i64__signum}

include Core_models.Bundle {impl_64__is_positive as impl_Saturating_of_i64__is_positive}

include Core_models.Bundle {impl_64__is_negative as impl_Saturating_of_i64__is_negative}

include Core_models.Bundle {impl_65__MIN as impl_Saturating_of_i128__MIN}

include Core_models.Bundle {impl_65__MAX as impl_Saturating_of_i128__MAX}

include Core_models.Bundle {impl_65__BITS as impl_Saturating_of_i128__BITS}

include Core_models.Bundle {impl_65__count_ones as impl_Saturating_of_i128__count_ones}

include Core_models.Bundle {impl_65__count_zeros as impl_Saturating_of_i128__count_zeros}

include Core_models.Bundle {impl_65__trailing_zeros as impl_Saturating_of_i128__trailing_zeros}

include Core_models.Bundle {impl_65__leading_zeros as impl_Saturating_of_i128__leading_zeros}

include Core_models.Bundle {impl_65__rotate_left as impl_Saturating_of_i128__rotate_left}

include Core_models.Bundle {impl_65__rotate_right as impl_Saturating_of_i128__rotate_right}

include Core_models.Bundle {impl_65__swap_bytes as impl_Saturating_of_i128__swap_bytes}

include Core_models.Bundle {impl_65__to_be as impl_Saturating_of_i128__to_be}

include Core_models.Bundle {impl_65__to_le as impl_Saturating_of_i128__to_le}

include Core_models.Bundle {impl_65__from_be as impl_Saturating_of_i128__from_be}

include Core_models.Bundle {impl_65__from_le as impl_Saturating_of_i128__from_le}

include Core_models.Bundle {impl_65__pow as impl_Saturating_of_i128__pow}

include Core_models.Bundle {impl_65__abs as impl_Saturating_of_i128__abs}

include Core_models.Bundle {impl_65__signum as impl_Saturating_of_i128__signum}

include Core_models.Bundle {impl_65__is_positive as impl_Saturating_of_i128__is_positive}

include Core_models.Bundle {impl_65__is_negative as impl_Saturating_of_i128__is_negative}

include Core_models.Bundle {impl_66__MIN as impl_Saturating_of_isize__MIN}

include Core_models.Bundle {impl_66__MAX as impl_Saturating_of_isize__MAX}

include Core_models.Bundle {impl_66__BITS as impl_Saturating_of_isize__BITS}

include Core_models.Bundle {impl_66__count_ones as impl_Saturating_of_isize__count_ones}

include Core_models.Bundle {impl_66__count_zeros as impl_Saturating_of_isize__count_zeros}

include Core_models.Bundle {impl_66__trailing_zeros as impl_Saturating_of_isize__trailing_zeros}

include Core_models.Bundle {impl_66__leading_zeros as impl_Saturating_of_isize__leading_zeros}

include Core_models.Bundle {impl_66__rotate_left as impl_Saturating_of_isize__rotate_left}

include Core_models.Bundle {impl_66__rotate_right as impl_Saturating_of_isize__rotate_right}

include Core_models.Bundle {impl_66__swap_bytes as impl_Saturating_of_isize__swap_bytes}

include Core_models.Bundle {impl_66__to_be as impl_Saturating_of_isize__to_be}

include Core_models.Bundle {impl_66__to_le as impl_Saturating_of_isize__to_le}

include Core_models.Bundle {impl_66__from_be as impl_Saturating_of_isize__from_be}

include Core_models.Bundle {impl_66__from_le as impl_Saturating_of_isize__from_le}

include Core_models.Bundle {impl_66__pow as impl_Saturating_of_isize__pow}

include Core_models.Bundle {impl_66__abs as impl_Saturating_of_isize__abs}

include Core_models.Bundle {impl_66__signum as impl_Saturating_of_isize__signum}

include Core_models.Bundle {impl_66__is_positive as impl_Saturating_of_isize__is_positive}

include Core_models.Bundle {impl_66__is_negative as impl_Saturating_of_isize__is_negative}
