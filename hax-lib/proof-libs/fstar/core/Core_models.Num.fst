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

include Core_models.Bundle {impl_6__min_value as impl_u8__min_value}

include Core_models.Bundle {impl_6__max_value as impl_u8__max_value}

include Core_models.Bundle {impl_6__cast_signed as impl_u8__cast_signed}

include Core_models.Bundle {impl_6__count_zeros as impl_u8__count_zeros}

include Core_models.Bundle {impl_6__checked_ilog2 as impl_u8__checked_ilog2}

include Core_models.Bundle {impl_6__overflowing_neg as impl_u8__overflowing_neg}

include Core_models.Bundle {impl_6__checked_neg as impl_u8__checked_neg}

include Core_models.Bundle {impl_6__strict_neg as impl_u8__strict_neg}

include Core_models.Bundle {impl_6__wrapping_pow as impl_u8__wrapping_pow}

include Core_models.Bundle {impl_6__saturating_pow as impl_u8__saturating_pow}

include Core_models.Bundle {impl_6__strict_pow as impl_u8__strict_pow}

include Core_models.Bundle {impl_6__strict_add as impl_u8__strict_add}

include Core_models.Bundle {impl_6__strict_sub as impl_u8__strict_sub}

include Core_models.Bundle {impl_6__strict_mul as impl_u8__strict_mul}

include Core_models.Bundle {impl_6__wrapping_div as impl_u8__wrapping_div}

include Core_models.Bundle {impl_6__wrapping_rem as impl_u8__wrapping_rem}

include Core_models.Bundle {impl_6__wrapping_div_euclid as impl_u8__wrapping_div_euclid}

include Core_models.Bundle {impl_6__wrapping_rem_euclid as impl_u8__wrapping_rem_euclid}

include Core_models.Bundle {impl_6__saturating_div as impl_u8__saturating_div}

include Core_models.Bundle {impl_6__strict_div as impl_u8__strict_div}

include Core_models.Bundle {impl_6__strict_rem as impl_u8__strict_rem}

include Core_models.Bundle {impl_6__strict_div_euclid as impl_u8__strict_div_euclid}

include Core_models.Bundle {impl_6__strict_rem_euclid as impl_u8__strict_rem_euclid}

include Core_models.Bundle {impl_6__div_euclid as impl_u8__div_euclid}

include Core_models.Bundle {impl_6__div_floor as impl_u8__div_floor}

include Core_models.Bundle {impl_6__overflowing_div as impl_u8__overflowing_div}

include Core_models.Bundle {impl_6__overflowing_rem as impl_u8__overflowing_rem}

include Core_models.Bundle {impl_6__overflowing_div_euclid as impl_u8__overflowing_div_euclid}

include Core_models.Bundle {impl_6__overflowing_rem_euclid as impl_u8__overflowing_rem_euclid}

include Core_models.Bundle {impl_6__checked_div_euclid as impl_u8__checked_div_euclid}

include Core_models.Bundle {impl_6__checked_rem_euclid as impl_u8__checked_rem_euclid}

include Core_models.Bundle {impl_6__div_exact as impl_u8__div_exact}

include Core_models.Bundle {impl_6__checked_div_exact as impl_u8__checked_div_exact}

include Core_models.Bundle {impl_6__unchecked_div_exact as impl_u8__unchecked_div_exact}

include Core_models.Bundle {impl_6__abs_diff as impl_u8__abs_diff}

include Core_models.Bundle {impl_6__midpoint as impl_u8__midpoint}

include Core_models.Bundle {impl_6__next_multiple_of as impl_u8__next_multiple_of}

include Core_models.Bundle {impl_6__checked_next_multiple_of as impl_u8__checked_next_multiple_of}

include Core_models.Bundle {impl_6__checked_signed_diff as impl_u8__checked_signed_diff}

include Core_models.Bundle {impl_6__wrapping_add_signed as impl_u8__wrapping_add_signed}

include Core_models.Bundle {impl_6__wrapping_sub_signed as impl_u8__wrapping_sub_signed}

include Core_models.Bundle {impl_6__overflowing_add_signed as impl_u8__overflowing_add_signed}

include Core_models.Bundle {impl_6__overflowing_sub_signed as impl_u8__overflowing_sub_signed}

include Core_models.Bundle {impl_6__checked_add_signed as impl_u8__checked_add_signed}

include Core_models.Bundle {impl_6__checked_sub_signed as impl_u8__checked_sub_signed}

include Core_models.Bundle {impl_6__saturating_add_signed as impl_u8__saturating_add_signed}

include Core_models.Bundle {impl_6__saturating_sub_signed as impl_u8__saturating_sub_signed}

include Core_models.Bundle {impl_6__strict_add_signed as impl_u8__strict_add_signed}

include Core_models.Bundle {impl_6__strict_sub_signed as impl_u8__strict_sub_signed}

include Core_models.Bundle {impl_6__trailing_zeros as impl_u8__trailing_zeros}

include Core_models.Bundle {impl_6__trailing_ones as impl_u8__trailing_ones}

include Core_models.Bundle {impl_6__leading_ones as impl_u8__leading_ones}

include Core_models.Bundle {impl_6__bit_width as impl_u8__bit_width}

include Core_models.Bundle {impl_6__highest_one as impl_u8__highest_one}

include Core_models.Bundle {impl_6__lowest_one as impl_u8__lowest_one}

include Core_models.Bundle {impl_6__isolate_lowest_one as impl_u8__isolate_lowest_one}

include Core_models.Bundle {impl_6__isolate_highest_one as impl_u8__isolate_highest_one}

include Core_models.Bundle {impl_6__swap_bytes as impl_u8__swap_bytes}

include Core_models.Bundle {impl_6__to_be as impl_u8__to_be}

include Core_models.Bundle {impl_6__to_le as impl_u8__to_le}

include Core_models.Bundle {impl_6__from_be as impl_u8__from_be}

include Core_models.Bundle {impl_6__from_le as impl_u8__from_le}

include Core_models.Bundle {impl_6__to_ne_bytes as impl_u8__to_ne_bytes}

include Core_models.Bundle {impl_6__from_ne_bytes as impl_u8__from_ne_bytes}

include Core_models.Bundle {impl_6__wrapping_shl as impl_u8__wrapping_shl}

include Core_models.Bundle {impl_6__wrapping_shr as impl_u8__wrapping_shr}

include Core_models.Bundle {impl_6__overflowing_shl as impl_u8__overflowing_shl}

include Core_models.Bundle {impl_6__overflowing_shr as impl_u8__overflowing_shr}

include Core_models.Bundle {impl_6__checked_shl as impl_u8__checked_shl}

include Core_models.Bundle {impl_6__checked_shr as impl_u8__checked_shr}

include Core_models.Bundle {impl_6__strict_shl as impl_u8__strict_shl}

include Core_models.Bundle {impl_6__strict_shr as impl_u8__strict_shr}

include Core_models.Bundle {impl_6__unbounded_shl as impl_u8__unbounded_shl}

include Core_models.Bundle {impl_6__unbounded_shr as impl_u8__unbounded_shr}

include Core_models.Bundle {impl_6__unchecked_shl as impl_u8__unchecked_shl}

include Core_models.Bundle {impl_6__unchecked_shr as impl_u8__unchecked_shr}

include Core_models.Bundle {impl_6__shl_exact as impl_u8__shl_exact}

include Core_models.Bundle {impl_6__shr_exact as impl_u8__shr_exact}

include Core_models.Bundle {impl_6__unchecked_shl_exact as impl_u8__unchecked_shl_exact}

include Core_models.Bundle {impl_6__unchecked_shr_exact as impl_u8__unchecked_shr_exact}

include Core_models.Bundle {impl_6__funnel_shl as impl_u8__funnel_shl}

include Core_models.Bundle {impl_6__funnel_shr as impl_u8__funnel_shr}

include Core_models.Bundle {impl_6__unchecked_disjoint_bitor as impl_u8__unchecked_disjoint_bitor}

include Core_models.Bundle {impl_6__checked_next_power_of_two as impl_u8__checked_next_power_of_two}

include Core_models.Bundle {impl_6__wrapping_next_power_of_two as impl_u8__wrapping_next_power_of_two}

include Core_models.Bundle {impl_6__next_power_of_two as impl_u8__next_power_of_two}

include Core_models.Bundle {impl_6__reverse_bits as impl_u8__reverse_bits}

include Core_models.Bundle {impl_6__widening_mul as impl_u8__widening_mul}

include Core_models.Bundle {impl_6__carrying_mul_add as impl_u8__carrying_mul_add}

include Core_models.Bundle {impl_6__carrying_mul as impl_u8__carrying_mul}

include Core_models.Bundle {impl_6__carrying_add as impl_u8__carrying_add}

include Core_models.Bundle {impl_6__borrowing_sub as impl_u8__borrowing_sub}

include Core_models.Bundle {impl_6__is_ascii as impl_u8__is_ascii}

include Core_models.Bundle {impl_6__is_ascii_uppercase as impl_u8__is_ascii_uppercase}

include Core_models.Bundle {impl_6__is_ascii_lowercase as impl_u8__is_ascii_lowercase}

include Core_models.Bundle {impl_6__is_ascii_alphabetic as impl_u8__is_ascii_alphabetic}

include Core_models.Bundle {impl_6__is_ascii_digit as impl_u8__is_ascii_digit}

include Core_models.Bundle {impl_6__is_ascii_octdigit as impl_u8__is_ascii_octdigit}

include Core_models.Bundle {impl_6__is_ascii_hexdigit as impl_u8__is_ascii_hexdigit}

include Core_models.Bundle {impl_6__is_ascii_alphanumeric as impl_u8__is_ascii_alphanumeric}

include Core_models.Bundle {impl_6__is_ascii_punctuation as impl_u8__is_ascii_punctuation}

include Core_models.Bundle {impl_6__is_ascii_graphic as impl_u8__is_ascii_graphic}

include Core_models.Bundle {impl_6__is_ascii_whitespace as impl_u8__is_ascii_whitespace}

include Core_models.Bundle {impl_6__is_ascii_control as impl_u8__is_ascii_control}

include Core_models.Bundle {impl_6__to_ascii_uppercase as impl_u8__to_ascii_uppercase}

include Core_models.Bundle {impl_6__to_ascii_lowercase as impl_u8__to_ascii_lowercase}

include Core_models.Bundle {impl_6__eq_ignore_ascii_case as impl_u8__eq_ignore_ascii_case}

include Core_models.Bundle {impl_6__make_ascii_uppercase as impl_u8__make_ascii_uppercase}

include Core_models.Bundle {impl_6__make_ascii_lowercase as impl_u8__make_ascii_lowercase}

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

include Core_models.Bundle {impl_7__min_value as impl_u16__min_value}

include Core_models.Bundle {impl_7__max_value as impl_u16__max_value}

include Core_models.Bundle {impl_7__cast_signed as impl_u16__cast_signed}

include Core_models.Bundle {impl_7__count_zeros as impl_u16__count_zeros}

include Core_models.Bundle {impl_7__checked_ilog2 as impl_u16__checked_ilog2}

include Core_models.Bundle {impl_7__overflowing_neg as impl_u16__overflowing_neg}

include Core_models.Bundle {impl_7__checked_neg as impl_u16__checked_neg}

include Core_models.Bundle {impl_7__strict_neg as impl_u16__strict_neg}

include Core_models.Bundle {impl_7__wrapping_pow as impl_u16__wrapping_pow}

include Core_models.Bundle {impl_7__saturating_pow as impl_u16__saturating_pow}

include Core_models.Bundle {impl_7__strict_pow as impl_u16__strict_pow}

include Core_models.Bundle {impl_7__strict_add as impl_u16__strict_add}

include Core_models.Bundle {impl_7__strict_sub as impl_u16__strict_sub}

include Core_models.Bundle {impl_7__strict_mul as impl_u16__strict_mul}

include Core_models.Bundle {impl_7__wrapping_div as impl_u16__wrapping_div}

include Core_models.Bundle {impl_7__wrapping_rem as impl_u16__wrapping_rem}

include Core_models.Bundle {impl_7__wrapping_div_euclid as impl_u16__wrapping_div_euclid}

include Core_models.Bundle {impl_7__wrapping_rem_euclid as impl_u16__wrapping_rem_euclid}

include Core_models.Bundle {impl_7__saturating_div as impl_u16__saturating_div}

include Core_models.Bundle {impl_7__strict_div as impl_u16__strict_div}

include Core_models.Bundle {impl_7__strict_rem as impl_u16__strict_rem}

include Core_models.Bundle {impl_7__strict_div_euclid as impl_u16__strict_div_euclid}

include Core_models.Bundle {impl_7__strict_rem_euclid as impl_u16__strict_rem_euclid}

include Core_models.Bundle {impl_7__div_euclid as impl_u16__div_euclid}

include Core_models.Bundle {impl_7__div_floor as impl_u16__div_floor}

include Core_models.Bundle {impl_7__overflowing_div as impl_u16__overflowing_div}

include Core_models.Bundle {impl_7__overflowing_rem as impl_u16__overflowing_rem}

include Core_models.Bundle {impl_7__overflowing_div_euclid as impl_u16__overflowing_div_euclid}

include Core_models.Bundle {impl_7__overflowing_rem_euclid as impl_u16__overflowing_rem_euclid}

include Core_models.Bundle {impl_7__checked_div_euclid as impl_u16__checked_div_euclid}

include Core_models.Bundle {impl_7__checked_rem_euclid as impl_u16__checked_rem_euclid}

include Core_models.Bundle {impl_7__div_exact as impl_u16__div_exact}

include Core_models.Bundle {impl_7__checked_div_exact as impl_u16__checked_div_exact}

include Core_models.Bundle {impl_7__unchecked_div_exact as impl_u16__unchecked_div_exact}

include Core_models.Bundle {impl_7__abs_diff as impl_u16__abs_diff}

include Core_models.Bundle {impl_7__midpoint as impl_u16__midpoint}

include Core_models.Bundle {impl_7__next_multiple_of as impl_u16__next_multiple_of}

include Core_models.Bundle {impl_7__checked_next_multiple_of as impl_u16__checked_next_multiple_of}

include Core_models.Bundle {impl_7__checked_signed_diff as impl_u16__checked_signed_diff}

include Core_models.Bundle {impl_7__wrapping_add_signed as impl_u16__wrapping_add_signed}

include Core_models.Bundle {impl_7__wrapping_sub_signed as impl_u16__wrapping_sub_signed}

include Core_models.Bundle {impl_7__overflowing_add_signed as impl_u16__overflowing_add_signed}

include Core_models.Bundle {impl_7__overflowing_sub_signed as impl_u16__overflowing_sub_signed}

include Core_models.Bundle {impl_7__checked_add_signed as impl_u16__checked_add_signed}

include Core_models.Bundle {impl_7__checked_sub_signed as impl_u16__checked_sub_signed}

include Core_models.Bundle {impl_7__saturating_add_signed as impl_u16__saturating_add_signed}

include Core_models.Bundle {impl_7__saturating_sub_signed as impl_u16__saturating_sub_signed}

include Core_models.Bundle {impl_7__strict_add_signed as impl_u16__strict_add_signed}

include Core_models.Bundle {impl_7__strict_sub_signed as impl_u16__strict_sub_signed}

include Core_models.Bundle {impl_7__trailing_zeros as impl_u16__trailing_zeros}

include Core_models.Bundle {impl_7__trailing_ones as impl_u16__trailing_ones}

include Core_models.Bundle {impl_7__leading_ones as impl_u16__leading_ones}

include Core_models.Bundle {impl_7__bit_width as impl_u16__bit_width}

include Core_models.Bundle {impl_7__highest_one as impl_u16__highest_one}

include Core_models.Bundle {impl_7__lowest_one as impl_u16__lowest_one}

include Core_models.Bundle {impl_7__isolate_lowest_one as impl_u16__isolate_lowest_one}

include Core_models.Bundle {impl_7__isolate_highest_one as impl_u16__isolate_highest_one}

include Core_models.Bundle {impl_7__swap_bytes as impl_u16__swap_bytes}

include Core_models.Bundle {impl_7__to_be as impl_u16__to_be}

include Core_models.Bundle {impl_7__to_le as impl_u16__to_le}

include Core_models.Bundle {impl_7__from_be as impl_u16__from_be}

include Core_models.Bundle {impl_7__from_le as impl_u16__from_le}

include Core_models.Bundle {impl_7__to_ne_bytes as impl_u16__to_ne_bytes}

include Core_models.Bundle {impl_7__from_ne_bytes as impl_u16__from_ne_bytes}

include Core_models.Bundle {impl_7__wrapping_shl as impl_u16__wrapping_shl}

include Core_models.Bundle {impl_7__wrapping_shr as impl_u16__wrapping_shr}

include Core_models.Bundle {impl_7__overflowing_shl as impl_u16__overflowing_shl}

include Core_models.Bundle {impl_7__overflowing_shr as impl_u16__overflowing_shr}

include Core_models.Bundle {impl_7__checked_shl as impl_u16__checked_shl}

include Core_models.Bundle {impl_7__checked_shr as impl_u16__checked_shr}

include Core_models.Bundle {impl_7__strict_shl as impl_u16__strict_shl}

include Core_models.Bundle {impl_7__strict_shr as impl_u16__strict_shr}

include Core_models.Bundle {impl_7__unbounded_shl as impl_u16__unbounded_shl}

include Core_models.Bundle {impl_7__unbounded_shr as impl_u16__unbounded_shr}

include Core_models.Bundle {impl_7__unchecked_shl as impl_u16__unchecked_shl}

include Core_models.Bundle {impl_7__unchecked_shr as impl_u16__unchecked_shr}

include Core_models.Bundle {impl_7__shl_exact as impl_u16__shl_exact}

include Core_models.Bundle {impl_7__shr_exact as impl_u16__shr_exact}

include Core_models.Bundle {impl_7__unchecked_shl_exact as impl_u16__unchecked_shl_exact}

include Core_models.Bundle {impl_7__unchecked_shr_exact as impl_u16__unchecked_shr_exact}

include Core_models.Bundle {impl_7__funnel_shl as impl_u16__funnel_shl}

include Core_models.Bundle {impl_7__funnel_shr as impl_u16__funnel_shr}

include Core_models.Bundle {impl_7__unchecked_disjoint_bitor as impl_u16__unchecked_disjoint_bitor}

include Core_models.Bundle {impl_7__checked_next_power_of_two as impl_u16__checked_next_power_of_two}

include Core_models.Bundle {impl_7__wrapping_next_power_of_two as impl_u16__wrapping_next_power_of_two}

include Core_models.Bundle {impl_7__next_power_of_two as impl_u16__next_power_of_two}

include Core_models.Bundle {impl_7__reverse_bits as impl_u16__reverse_bits}

include Core_models.Bundle {impl_7__widening_mul as impl_u16__widening_mul}

include Core_models.Bundle {impl_7__carrying_mul_add as impl_u16__carrying_mul_add}

include Core_models.Bundle {impl_7__carrying_mul as impl_u16__carrying_mul}

include Core_models.Bundle {impl_7__carrying_add as impl_u16__carrying_add}

include Core_models.Bundle {impl_7__borrowing_sub as impl_u16__borrowing_sub}

include Core_models.Bundle {impl_7__is_utf16_surrogate as impl_u16__is_utf16_surrogate}

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

include Core_models.Bundle {impl_8__min_value as impl_u32__min_value}

include Core_models.Bundle {impl_8__max_value as impl_u32__max_value}

include Core_models.Bundle {impl_8__cast_signed as impl_u32__cast_signed}

include Core_models.Bundle {impl_8__count_zeros as impl_u32__count_zeros}

include Core_models.Bundle {impl_8__checked_ilog2 as impl_u32__checked_ilog2}

include Core_models.Bundle {impl_8__overflowing_neg as impl_u32__overflowing_neg}

include Core_models.Bundle {impl_8__checked_neg as impl_u32__checked_neg}

include Core_models.Bundle {impl_8__strict_neg as impl_u32__strict_neg}

include Core_models.Bundle {impl_8__wrapping_pow as impl_u32__wrapping_pow}

include Core_models.Bundle {impl_8__saturating_pow as impl_u32__saturating_pow}

include Core_models.Bundle {impl_8__strict_pow as impl_u32__strict_pow}

include Core_models.Bundle {impl_8__strict_add as impl_u32__strict_add}

include Core_models.Bundle {impl_8__strict_sub as impl_u32__strict_sub}

include Core_models.Bundle {impl_8__strict_mul as impl_u32__strict_mul}

include Core_models.Bundle {impl_8__wrapping_div as impl_u32__wrapping_div}

include Core_models.Bundle {impl_8__wrapping_rem as impl_u32__wrapping_rem}

include Core_models.Bundle {impl_8__wrapping_div_euclid as impl_u32__wrapping_div_euclid}

include Core_models.Bundle {impl_8__wrapping_rem_euclid as impl_u32__wrapping_rem_euclid}

include Core_models.Bundle {impl_8__saturating_div as impl_u32__saturating_div}

include Core_models.Bundle {impl_8__strict_div as impl_u32__strict_div}

include Core_models.Bundle {impl_8__strict_rem as impl_u32__strict_rem}

include Core_models.Bundle {impl_8__strict_div_euclid as impl_u32__strict_div_euclid}

include Core_models.Bundle {impl_8__strict_rem_euclid as impl_u32__strict_rem_euclid}

include Core_models.Bundle {impl_8__div_euclid as impl_u32__div_euclid}

include Core_models.Bundle {impl_8__div_floor as impl_u32__div_floor}

include Core_models.Bundle {impl_8__overflowing_div as impl_u32__overflowing_div}

include Core_models.Bundle {impl_8__overflowing_rem as impl_u32__overflowing_rem}

include Core_models.Bundle {impl_8__overflowing_div_euclid as impl_u32__overflowing_div_euclid}

include Core_models.Bundle {impl_8__overflowing_rem_euclid as impl_u32__overflowing_rem_euclid}

include Core_models.Bundle {impl_8__checked_div_euclid as impl_u32__checked_div_euclid}

include Core_models.Bundle {impl_8__checked_rem_euclid as impl_u32__checked_rem_euclid}

include Core_models.Bundle {impl_8__div_exact as impl_u32__div_exact}

include Core_models.Bundle {impl_8__checked_div_exact as impl_u32__checked_div_exact}

include Core_models.Bundle {impl_8__unchecked_div_exact as impl_u32__unchecked_div_exact}

include Core_models.Bundle {impl_8__abs_diff as impl_u32__abs_diff}

include Core_models.Bundle {impl_8__midpoint as impl_u32__midpoint}

include Core_models.Bundle {impl_8__next_multiple_of as impl_u32__next_multiple_of}

include Core_models.Bundle {impl_8__checked_next_multiple_of as impl_u32__checked_next_multiple_of}

include Core_models.Bundle {impl_8__checked_signed_diff as impl_u32__checked_signed_diff}

include Core_models.Bundle {impl_8__wrapping_add_signed as impl_u32__wrapping_add_signed}

include Core_models.Bundle {impl_8__wrapping_sub_signed as impl_u32__wrapping_sub_signed}

include Core_models.Bundle {impl_8__overflowing_add_signed as impl_u32__overflowing_add_signed}

include Core_models.Bundle {impl_8__overflowing_sub_signed as impl_u32__overflowing_sub_signed}

include Core_models.Bundle {impl_8__checked_add_signed as impl_u32__checked_add_signed}

include Core_models.Bundle {impl_8__checked_sub_signed as impl_u32__checked_sub_signed}

include Core_models.Bundle {impl_8__saturating_add_signed as impl_u32__saturating_add_signed}

include Core_models.Bundle {impl_8__saturating_sub_signed as impl_u32__saturating_sub_signed}

include Core_models.Bundle {impl_8__strict_add_signed as impl_u32__strict_add_signed}

include Core_models.Bundle {impl_8__strict_sub_signed as impl_u32__strict_sub_signed}

include Core_models.Bundle {impl_8__trailing_zeros as impl_u32__trailing_zeros}

include Core_models.Bundle {impl_8__trailing_ones as impl_u32__trailing_ones}

include Core_models.Bundle {impl_8__leading_ones as impl_u32__leading_ones}

include Core_models.Bundle {impl_8__bit_width as impl_u32__bit_width}

include Core_models.Bundle {impl_8__highest_one as impl_u32__highest_one}

include Core_models.Bundle {impl_8__lowest_one as impl_u32__lowest_one}

include Core_models.Bundle {impl_8__isolate_lowest_one as impl_u32__isolate_lowest_one}

include Core_models.Bundle {impl_8__isolate_highest_one as impl_u32__isolate_highest_one}

include Core_models.Bundle {impl_8__swap_bytes as impl_u32__swap_bytes}

include Core_models.Bundle {impl_8__to_be as impl_u32__to_be}

include Core_models.Bundle {impl_8__to_le as impl_u32__to_le}

include Core_models.Bundle {impl_8__from_be as impl_u32__from_be}

include Core_models.Bundle {impl_8__from_le as impl_u32__from_le}

include Core_models.Bundle {impl_8__to_ne_bytes as impl_u32__to_ne_bytes}

include Core_models.Bundle {impl_8__from_ne_bytes as impl_u32__from_ne_bytes}

include Core_models.Bundle {impl_8__wrapping_shl as impl_u32__wrapping_shl}

include Core_models.Bundle {impl_8__wrapping_shr as impl_u32__wrapping_shr}

include Core_models.Bundle {impl_8__overflowing_shl as impl_u32__overflowing_shl}

include Core_models.Bundle {impl_8__overflowing_shr as impl_u32__overflowing_shr}

include Core_models.Bundle {impl_8__checked_shl as impl_u32__checked_shl}

include Core_models.Bundle {impl_8__checked_shr as impl_u32__checked_shr}

include Core_models.Bundle {impl_8__strict_shl as impl_u32__strict_shl}

include Core_models.Bundle {impl_8__strict_shr as impl_u32__strict_shr}

include Core_models.Bundle {impl_8__unbounded_shl as impl_u32__unbounded_shl}

include Core_models.Bundle {impl_8__unbounded_shr as impl_u32__unbounded_shr}

include Core_models.Bundle {impl_8__unchecked_shl as impl_u32__unchecked_shl}

include Core_models.Bundle {impl_8__unchecked_shr as impl_u32__unchecked_shr}

include Core_models.Bundle {impl_8__shl_exact as impl_u32__shl_exact}

include Core_models.Bundle {impl_8__shr_exact as impl_u32__shr_exact}

include Core_models.Bundle {impl_8__unchecked_shl_exact as impl_u32__unchecked_shl_exact}

include Core_models.Bundle {impl_8__unchecked_shr_exact as impl_u32__unchecked_shr_exact}

include Core_models.Bundle {impl_8__funnel_shl as impl_u32__funnel_shl}

include Core_models.Bundle {impl_8__funnel_shr as impl_u32__funnel_shr}

include Core_models.Bundle {impl_8__unchecked_disjoint_bitor as impl_u32__unchecked_disjoint_bitor}

include Core_models.Bundle {impl_8__checked_next_power_of_two as impl_u32__checked_next_power_of_two}

include Core_models.Bundle {impl_8__wrapping_next_power_of_two as impl_u32__wrapping_next_power_of_two}

include Core_models.Bundle {impl_8__next_power_of_two as impl_u32__next_power_of_two}

include Core_models.Bundle {impl_8__reverse_bits as impl_u32__reverse_bits}

include Core_models.Bundle {impl_8__widening_mul as impl_u32__widening_mul}

include Core_models.Bundle {impl_8__carrying_mul_add as impl_u32__carrying_mul_add}

include Core_models.Bundle {impl_8__carrying_mul as impl_u32__carrying_mul}

include Core_models.Bundle {impl_8__carrying_add as impl_u32__carrying_add}

include Core_models.Bundle {impl_8__borrowing_sub as impl_u32__borrowing_sub}

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

include Core_models.Bundle {impl_9__min_value as impl_u64__min_value}

include Core_models.Bundle {impl_9__max_value as impl_u64__max_value}

include Core_models.Bundle {impl_9__cast_signed as impl_u64__cast_signed}

include Core_models.Bundle {impl_9__count_zeros as impl_u64__count_zeros}

include Core_models.Bundle {impl_9__checked_ilog2 as impl_u64__checked_ilog2}

include Core_models.Bundle {impl_9__overflowing_neg as impl_u64__overflowing_neg}

include Core_models.Bundle {impl_9__checked_neg as impl_u64__checked_neg}

include Core_models.Bundle {impl_9__strict_neg as impl_u64__strict_neg}

include Core_models.Bundle {impl_9__wrapping_pow as impl_u64__wrapping_pow}

include Core_models.Bundle {impl_9__saturating_pow as impl_u64__saturating_pow}

include Core_models.Bundle {impl_9__strict_pow as impl_u64__strict_pow}

include Core_models.Bundle {impl_9__strict_add as impl_u64__strict_add}

include Core_models.Bundle {impl_9__strict_sub as impl_u64__strict_sub}

include Core_models.Bundle {impl_9__strict_mul as impl_u64__strict_mul}

include Core_models.Bundle {impl_9__wrapping_div as impl_u64__wrapping_div}

include Core_models.Bundle {impl_9__wrapping_rem as impl_u64__wrapping_rem}

include Core_models.Bundle {impl_9__wrapping_div_euclid as impl_u64__wrapping_div_euclid}

include Core_models.Bundle {impl_9__wrapping_rem_euclid as impl_u64__wrapping_rem_euclid}

include Core_models.Bundle {impl_9__saturating_div as impl_u64__saturating_div}

include Core_models.Bundle {impl_9__strict_div as impl_u64__strict_div}

include Core_models.Bundle {impl_9__strict_rem as impl_u64__strict_rem}

include Core_models.Bundle {impl_9__strict_div_euclid as impl_u64__strict_div_euclid}

include Core_models.Bundle {impl_9__strict_rem_euclid as impl_u64__strict_rem_euclid}

include Core_models.Bundle {impl_9__div_euclid as impl_u64__div_euclid}

include Core_models.Bundle {impl_9__div_floor as impl_u64__div_floor}

include Core_models.Bundle {impl_9__overflowing_div as impl_u64__overflowing_div}

include Core_models.Bundle {impl_9__overflowing_rem as impl_u64__overflowing_rem}

include Core_models.Bundle {impl_9__overflowing_div_euclid as impl_u64__overflowing_div_euclid}

include Core_models.Bundle {impl_9__overflowing_rem_euclid as impl_u64__overflowing_rem_euclid}

include Core_models.Bundle {impl_9__checked_div_euclid as impl_u64__checked_div_euclid}

include Core_models.Bundle {impl_9__checked_rem_euclid as impl_u64__checked_rem_euclid}

include Core_models.Bundle {impl_9__div_exact as impl_u64__div_exact}

include Core_models.Bundle {impl_9__checked_div_exact as impl_u64__checked_div_exact}

include Core_models.Bundle {impl_9__unchecked_div_exact as impl_u64__unchecked_div_exact}

include Core_models.Bundle {impl_9__abs_diff as impl_u64__abs_diff}

include Core_models.Bundle {impl_9__midpoint as impl_u64__midpoint}

include Core_models.Bundle {impl_9__next_multiple_of as impl_u64__next_multiple_of}

include Core_models.Bundle {impl_9__checked_next_multiple_of as impl_u64__checked_next_multiple_of}

include Core_models.Bundle {impl_9__checked_signed_diff as impl_u64__checked_signed_diff}

include Core_models.Bundle {impl_9__wrapping_add_signed as impl_u64__wrapping_add_signed}

include Core_models.Bundle {impl_9__wrapping_sub_signed as impl_u64__wrapping_sub_signed}

include Core_models.Bundle {impl_9__overflowing_add_signed as impl_u64__overflowing_add_signed}

include Core_models.Bundle {impl_9__overflowing_sub_signed as impl_u64__overflowing_sub_signed}

include Core_models.Bundle {impl_9__checked_add_signed as impl_u64__checked_add_signed}

include Core_models.Bundle {impl_9__checked_sub_signed as impl_u64__checked_sub_signed}

include Core_models.Bundle {impl_9__saturating_add_signed as impl_u64__saturating_add_signed}

include Core_models.Bundle {impl_9__saturating_sub_signed as impl_u64__saturating_sub_signed}

include Core_models.Bundle {impl_9__strict_add_signed as impl_u64__strict_add_signed}

include Core_models.Bundle {impl_9__strict_sub_signed as impl_u64__strict_sub_signed}

include Core_models.Bundle {impl_9__trailing_zeros as impl_u64__trailing_zeros}

include Core_models.Bundle {impl_9__trailing_ones as impl_u64__trailing_ones}

include Core_models.Bundle {impl_9__leading_ones as impl_u64__leading_ones}

include Core_models.Bundle {impl_9__bit_width as impl_u64__bit_width}

include Core_models.Bundle {impl_9__highest_one as impl_u64__highest_one}

include Core_models.Bundle {impl_9__lowest_one as impl_u64__lowest_one}

include Core_models.Bundle {impl_9__isolate_lowest_one as impl_u64__isolate_lowest_one}

include Core_models.Bundle {impl_9__isolate_highest_one as impl_u64__isolate_highest_one}

include Core_models.Bundle {impl_9__swap_bytes as impl_u64__swap_bytes}

include Core_models.Bundle {impl_9__to_be as impl_u64__to_be}

include Core_models.Bundle {impl_9__to_le as impl_u64__to_le}

include Core_models.Bundle {impl_9__from_be as impl_u64__from_be}

include Core_models.Bundle {impl_9__from_le as impl_u64__from_le}

include Core_models.Bundle {impl_9__to_ne_bytes as impl_u64__to_ne_bytes}

include Core_models.Bundle {impl_9__from_ne_bytes as impl_u64__from_ne_bytes}

include Core_models.Bundle {impl_9__wrapping_shl as impl_u64__wrapping_shl}

include Core_models.Bundle {impl_9__wrapping_shr as impl_u64__wrapping_shr}

include Core_models.Bundle {impl_9__overflowing_shl as impl_u64__overflowing_shl}

include Core_models.Bundle {impl_9__overflowing_shr as impl_u64__overflowing_shr}

include Core_models.Bundle {impl_9__checked_shl as impl_u64__checked_shl}

include Core_models.Bundle {impl_9__checked_shr as impl_u64__checked_shr}

include Core_models.Bundle {impl_9__strict_shl as impl_u64__strict_shl}

include Core_models.Bundle {impl_9__strict_shr as impl_u64__strict_shr}

include Core_models.Bundle {impl_9__unbounded_shl as impl_u64__unbounded_shl}

include Core_models.Bundle {impl_9__unbounded_shr as impl_u64__unbounded_shr}

include Core_models.Bundle {impl_9__unchecked_shl as impl_u64__unchecked_shl}

include Core_models.Bundle {impl_9__unchecked_shr as impl_u64__unchecked_shr}

include Core_models.Bundle {impl_9__shl_exact as impl_u64__shl_exact}

include Core_models.Bundle {impl_9__shr_exact as impl_u64__shr_exact}

include Core_models.Bundle {impl_9__unchecked_shl_exact as impl_u64__unchecked_shl_exact}

include Core_models.Bundle {impl_9__unchecked_shr_exact as impl_u64__unchecked_shr_exact}

include Core_models.Bundle {impl_9__funnel_shl as impl_u64__funnel_shl}

include Core_models.Bundle {impl_9__funnel_shr as impl_u64__funnel_shr}

include Core_models.Bundle {impl_9__unchecked_disjoint_bitor as impl_u64__unchecked_disjoint_bitor}

include Core_models.Bundle {impl_9__checked_next_power_of_two as impl_u64__checked_next_power_of_two}

include Core_models.Bundle {impl_9__wrapping_next_power_of_two as impl_u64__wrapping_next_power_of_two}

include Core_models.Bundle {impl_9__next_power_of_two as impl_u64__next_power_of_two}

include Core_models.Bundle {impl_9__reverse_bits as impl_u64__reverse_bits}

include Core_models.Bundle {impl_9__widening_mul as impl_u64__widening_mul}

include Core_models.Bundle {impl_9__carrying_mul_add as impl_u64__carrying_mul_add}

include Core_models.Bundle {impl_9__carrying_mul as impl_u64__carrying_mul}

include Core_models.Bundle {impl_9__carrying_add as impl_u64__carrying_add}

include Core_models.Bundle {impl_9__borrowing_sub as impl_u64__borrowing_sub}

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

include Core_models.Bundle {impl_10__min_value as impl_u128__min_value}

include Core_models.Bundle {impl_10__max_value as impl_u128__max_value}

include Core_models.Bundle {impl_10__cast_signed as impl_u128__cast_signed}

include Core_models.Bundle {impl_10__count_zeros as impl_u128__count_zeros}

include Core_models.Bundle {impl_10__checked_ilog2 as impl_u128__checked_ilog2}

include Core_models.Bundle {impl_10__overflowing_neg as impl_u128__overflowing_neg}

include Core_models.Bundle {impl_10__checked_neg as impl_u128__checked_neg}

include Core_models.Bundle {impl_10__strict_neg as impl_u128__strict_neg}

include Core_models.Bundle {impl_10__wrapping_pow as impl_u128__wrapping_pow}

include Core_models.Bundle {impl_10__saturating_pow as impl_u128__saturating_pow}

include Core_models.Bundle {impl_10__strict_pow as impl_u128__strict_pow}

include Core_models.Bundle {impl_10__strict_add as impl_u128__strict_add}

include Core_models.Bundle {impl_10__strict_sub as impl_u128__strict_sub}

include Core_models.Bundle {impl_10__strict_mul as impl_u128__strict_mul}

include Core_models.Bundle {impl_10__wrapping_div as impl_u128__wrapping_div}

include Core_models.Bundle {impl_10__wrapping_rem as impl_u128__wrapping_rem}

include Core_models.Bundle {impl_10__wrapping_div_euclid as impl_u128__wrapping_div_euclid}

include Core_models.Bundle {impl_10__wrapping_rem_euclid as impl_u128__wrapping_rem_euclid}

include Core_models.Bundle {impl_10__saturating_div as impl_u128__saturating_div}

include Core_models.Bundle {impl_10__strict_div as impl_u128__strict_div}

include Core_models.Bundle {impl_10__strict_rem as impl_u128__strict_rem}

include Core_models.Bundle {impl_10__strict_div_euclid as impl_u128__strict_div_euclid}

include Core_models.Bundle {impl_10__strict_rem_euclid as impl_u128__strict_rem_euclid}

include Core_models.Bundle {impl_10__div_euclid as impl_u128__div_euclid}

include Core_models.Bundle {impl_10__div_floor as impl_u128__div_floor}

include Core_models.Bundle {impl_10__overflowing_div as impl_u128__overflowing_div}

include Core_models.Bundle {impl_10__overflowing_rem as impl_u128__overflowing_rem}

include Core_models.Bundle {impl_10__overflowing_div_euclid as impl_u128__overflowing_div_euclid}

include Core_models.Bundle {impl_10__overflowing_rem_euclid as impl_u128__overflowing_rem_euclid}

include Core_models.Bundle {impl_10__checked_div_euclid as impl_u128__checked_div_euclid}

include Core_models.Bundle {impl_10__checked_rem_euclid as impl_u128__checked_rem_euclid}

include Core_models.Bundle {impl_10__div_exact as impl_u128__div_exact}

include Core_models.Bundle {impl_10__checked_div_exact as impl_u128__checked_div_exact}

include Core_models.Bundle {impl_10__unchecked_div_exact as impl_u128__unchecked_div_exact}

include Core_models.Bundle {impl_10__abs_diff as impl_u128__abs_diff}

include Core_models.Bundle {impl_10__midpoint as impl_u128__midpoint}

include Core_models.Bundle {impl_10__next_multiple_of as impl_u128__next_multiple_of}

include Core_models.Bundle {impl_10__checked_next_multiple_of as impl_u128__checked_next_multiple_of}

include Core_models.Bundle {impl_10__checked_signed_diff as impl_u128__checked_signed_diff}

include Core_models.Bundle {impl_10__wrapping_add_signed as impl_u128__wrapping_add_signed}

include Core_models.Bundle {impl_10__wrapping_sub_signed as impl_u128__wrapping_sub_signed}

include Core_models.Bundle {impl_10__overflowing_add_signed as impl_u128__overflowing_add_signed}

include Core_models.Bundle {impl_10__overflowing_sub_signed as impl_u128__overflowing_sub_signed}

include Core_models.Bundle {impl_10__checked_add_signed as impl_u128__checked_add_signed}

include Core_models.Bundle {impl_10__checked_sub_signed as impl_u128__checked_sub_signed}

include Core_models.Bundle {impl_10__saturating_add_signed as impl_u128__saturating_add_signed}

include Core_models.Bundle {impl_10__saturating_sub_signed as impl_u128__saturating_sub_signed}

include Core_models.Bundle {impl_10__strict_add_signed as impl_u128__strict_add_signed}

include Core_models.Bundle {impl_10__strict_sub_signed as impl_u128__strict_sub_signed}

include Core_models.Bundle {impl_10__trailing_zeros as impl_u128__trailing_zeros}

include Core_models.Bundle {impl_10__trailing_ones as impl_u128__trailing_ones}

include Core_models.Bundle {impl_10__leading_ones as impl_u128__leading_ones}

include Core_models.Bundle {impl_10__bit_width as impl_u128__bit_width}

include Core_models.Bundle {impl_10__highest_one as impl_u128__highest_one}

include Core_models.Bundle {impl_10__lowest_one as impl_u128__lowest_one}

include Core_models.Bundle {impl_10__isolate_lowest_one as impl_u128__isolate_lowest_one}

include Core_models.Bundle {impl_10__isolate_highest_one as impl_u128__isolate_highest_one}

include Core_models.Bundle {impl_10__swap_bytes as impl_u128__swap_bytes}

include Core_models.Bundle {impl_10__to_be as impl_u128__to_be}

include Core_models.Bundle {impl_10__to_le as impl_u128__to_le}

include Core_models.Bundle {impl_10__from_be as impl_u128__from_be}

include Core_models.Bundle {impl_10__from_le as impl_u128__from_le}

include Core_models.Bundle {impl_10__to_ne_bytes as impl_u128__to_ne_bytes}

include Core_models.Bundle {impl_10__from_ne_bytes as impl_u128__from_ne_bytes}

include Core_models.Bundle {impl_10__wrapping_shl as impl_u128__wrapping_shl}

include Core_models.Bundle {impl_10__wrapping_shr as impl_u128__wrapping_shr}

include Core_models.Bundle {impl_10__overflowing_shl as impl_u128__overflowing_shl}

include Core_models.Bundle {impl_10__overflowing_shr as impl_u128__overflowing_shr}

include Core_models.Bundle {impl_10__checked_shl as impl_u128__checked_shl}

include Core_models.Bundle {impl_10__checked_shr as impl_u128__checked_shr}

include Core_models.Bundle {impl_10__strict_shl as impl_u128__strict_shl}

include Core_models.Bundle {impl_10__strict_shr as impl_u128__strict_shr}

include Core_models.Bundle {impl_10__unbounded_shl as impl_u128__unbounded_shl}

include Core_models.Bundle {impl_10__unbounded_shr as impl_u128__unbounded_shr}

include Core_models.Bundle {impl_10__unchecked_shl as impl_u128__unchecked_shl}

include Core_models.Bundle {impl_10__unchecked_shr as impl_u128__unchecked_shr}

include Core_models.Bundle {impl_10__shl_exact as impl_u128__shl_exact}

include Core_models.Bundle {impl_10__shr_exact as impl_u128__shr_exact}

include Core_models.Bundle {impl_10__unchecked_shl_exact as impl_u128__unchecked_shl_exact}

include Core_models.Bundle {impl_10__unchecked_shr_exact as impl_u128__unchecked_shr_exact}

include Core_models.Bundle {impl_10__funnel_shl as impl_u128__funnel_shl}

include Core_models.Bundle {impl_10__funnel_shr as impl_u128__funnel_shr}

include Core_models.Bundle {impl_10__unchecked_disjoint_bitor as impl_u128__unchecked_disjoint_bitor}

include Core_models.Bundle {impl_10__checked_next_power_of_two as impl_u128__checked_next_power_of_two}

include Core_models.Bundle {impl_10__wrapping_next_power_of_two as impl_u128__wrapping_next_power_of_two}

include Core_models.Bundle {impl_10__next_power_of_two as impl_u128__next_power_of_two}

include Core_models.Bundle {impl_10__reverse_bits as impl_u128__reverse_bits}

include Core_models.Bundle {impl_10__widening_mul as impl_u128__widening_mul}

include Core_models.Bundle {impl_10__carrying_mul_add as impl_u128__carrying_mul_add}

include Core_models.Bundle {impl_10__carrying_mul as impl_u128__carrying_mul}

include Core_models.Bundle {impl_10__carrying_add as impl_u128__carrying_add}

include Core_models.Bundle {impl_10__borrowing_sub as impl_u128__borrowing_sub}

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

include Core_models.Bundle {impl_11__min_value as impl_usize__min_value}

include Core_models.Bundle {impl_11__max_value as impl_usize__max_value}

include Core_models.Bundle {impl_11__cast_signed as impl_usize__cast_signed}

include Core_models.Bundle {impl_11__count_zeros as impl_usize__count_zeros}

include Core_models.Bundle {impl_11__checked_ilog2 as impl_usize__checked_ilog2}

include Core_models.Bundle {impl_11__overflowing_neg as impl_usize__overflowing_neg}

include Core_models.Bundle {impl_11__checked_neg as impl_usize__checked_neg}

include Core_models.Bundle {impl_11__strict_neg as impl_usize__strict_neg}

include Core_models.Bundle {impl_11__wrapping_pow as impl_usize__wrapping_pow}

include Core_models.Bundle {impl_11__saturating_pow as impl_usize__saturating_pow}

include Core_models.Bundle {impl_11__strict_pow as impl_usize__strict_pow}

include Core_models.Bundle {impl_11__strict_add as impl_usize__strict_add}

include Core_models.Bundle {impl_11__strict_sub as impl_usize__strict_sub}

include Core_models.Bundle {impl_11__strict_mul as impl_usize__strict_mul}

include Core_models.Bundle {impl_11__wrapping_div as impl_usize__wrapping_div}

include Core_models.Bundle {impl_11__wrapping_rem as impl_usize__wrapping_rem}

include Core_models.Bundle {impl_11__wrapping_div_euclid as impl_usize__wrapping_div_euclid}

include Core_models.Bundle {impl_11__wrapping_rem_euclid as impl_usize__wrapping_rem_euclid}

include Core_models.Bundle {impl_11__saturating_div as impl_usize__saturating_div}

include Core_models.Bundle {impl_11__strict_div as impl_usize__strict_div}

include Core_models.Bundle {impl_11__strict_rem as impl_usize__strict_rem}

include Core_models.Bundle {impl_11__strict_div_euclid as impl_usize__strict_div_euclid}

include Core_models.Bundle {impl_11__strict_rem_euclid as impl_usize__strict_rem_euclid}

include Core_models.Bundle {impl_11__div_euclid as impl_usize__div_euclid}

include Core_models.Bundle {impl_11__div_floor as impl_usize__div_floor}

include Core_models.Bundle {impl_11__overflowing_div as impl_usize__overflowing_div}

include Core_models.Bundle {impl_11__overflowing_rem as impl_usize__overflowing_rem}

include Core_models.Bundle {impl_11__overflowing_div_euclid as impl_usize__overflowing_div_euclid}

include Core_models.Bundle {impl_11__overflowing_rem_euclid as impl_usize__overflowing_rem_euclid}

include Core_models.Bundle {impl_11__checked_div_euclid as impl_usize__checked_div_euclid}

include Core_models.Bundle {impl_11__checked_rem_euclid as impl_usize__checked_rem_euclid}

include Core_models.Bundle {impl_11__div_exact as impl_usize__div_exact}

include Core_models.Bundle {impl_11__checked_div_exact as impl_usize__checked_div_exact}

include Core_models.Bundle {impl_11__unchecked_div_exact as impl_usize__unchecked_div_exact}

include Core_models.Bundle {impl_11__abs_diff as impl_usize__abs_diff}

include Core_models.Bundle {impl_11__midpoint as impl_usize__midpoint}

include Core_models.Bundle {impl_11__next_multiple_of as impl_usize__next_multiple_of}

include Core_models.Bundle {impl_11__checked_next_multiple_of as impl_usize__checked_next_multiple_of}

include Core_models.Bundle {impl_11__checked_signed_diff as impl_usize__checked_signed_diff}

include Core_models.Bundle {impl_11__wrapping_add_signed as impl_usize__wrapping_add_signed}

include Core_models.Bundle {impl_11__wrapping_sub_signed as impl_usize__wrapping_sub_signed}

include Core_models.Bundle {impl_11__overflowing_add_signed as impl_usize__overflowing_add_signed}

include Core_models.Bundle {impl_11__overflowing_sub_signed as impl_usize__overflowing_sub_signed}

include Core_models.Bundle {impl_11__checked_add_signed as impl_usize__checked_add_signed}

include Core_models.Bundle {impl_11__checked_sub_signed as impl_usize__checked_sub_signed}

include Core_models.Bundle {impl_11__saturating_add_signed as impl_usize__saturating_add_signed}

include Core_models.Bundle {impl_11__saturating_sub_signed as impl_usize__saturating_sub_signed}

include Core_models.Bundle {impl_11__strict_add_signed as impl_usize__strict_add_signed}

include Core_models.Bundle {impl_11__strict_sub_signed as impl_usize__strict_sub_signed}

include Core_models.Bundle {impl_11__trailing_zeros as impl_usize__trailing_zeros}

include Core_models.Bundle {impl_11__trailing_ones as impl_usize__trailing_ones}

include Core_models.Bundle {impl_11__leading_ones as impl_usize__leading_ones}

include Core_models.Bundle {impl_11__bit_width as impl_usize__bit_width}

include Core_models.Bundle {impl_11__highest_one as impl_usize__highest_one}

include Core_models.Bundle {impl_11__lowest_one as impl_usize__lowest_one}

include Core_models.Bundle {impl_11__isolate_lowest_one as impl_usize__isolate_lowest_one}

include Core_models.Bundle {impl_11__isolate_highest_one as impl_usize__isolate_highest_one}

include Core_models.Bundle {impl_11__swap_bytes as impl_usize__swap_bytes}

include Core_models.Bundle {impl_11__to_be as impl_usize__to_be}

include Core_models.Bundle {impl_11__to_le as impl_usize__to_le}

include Core_models.Bundle {impl_11__from_be as impl_usize__from_be}

include Core_models.Bundle {impl_11__from_le as impl_usize__from_le}

include Core_models.Bundle {impl_11__to_ne_bytes as impl_usize__to_ne_bytes}

include Core_models.Bundle {impl_11__from_ne_bytes as impl_usize__from_ne_bytes}

include Core_models.Bundle {impl_11__wrapping_shl as impl_usize__wrapping_shl}

include Core_models.Bundle {impl_11__wrapping_shr as impl_usize__wrapping_shr}

include Core_models.Bundle {impl_11__overflowing_shl as impl_usize__overflowing_shl}

include Core_models.Bundle {impl_11__overflowing_shr as impl_usize__overflowing_shr}

include Core_models.Bundle {impl_11__checked_shl as impl_usize__checked_shl}

include Core_models.Bundle {impl_11__checked_shr as impl_usize__checked_shr}

include Core_models.Bundle {impl_11__strict_shl as impl_usize__strict_shl}

include Core_models.Bundle {impl_11__strict_shr as impl_usize__strict_shr}

include Core_models.Bundle {impl_11__unbounded_shl as impl_usize__unbounded_shl}

include Core_models.Bundle {impl_11__unbounded_shr as impl_usize__unbounded_shr}

include Core_models.Bundle {impl_11__unchecked_shl as impl_usize__unchecked_shl}

include Core_models.Bundle {impl_11__unchecked_shr as impl_usize__unchecked_shr}

include Core_models.Bundle {impl_11__shl_exact as impl_usize__shl_exact}

include Core_models.Bundle {impl_11__shr_exact as impl_usize__shr_exact}

include Core_models.Bundle {impl_11__unchecked_shl_exact as impl_usize__unchecked_shl_exact}

include Core_models.Bundle {impl_11__unchecked_shr_exact as impl_usize__unchecked_shr_exact}

include Core_models.Bundle {impl_11__funnel_shl as impl_usize__funnel_shl}

include Core_models.Bundle {impl_11__funnel_shr as impl_usize__funnel_shr}

include Core_models.Bundle {impl_11__unchecked_disjoint_bitor as impl_usize__unchecked_disjoint_bitor}

include Core_models.Bundle {impl_11__checked_next_power_of_two as impl_usize__checked_next_power_of_two}

include Core_models.Bundle {impl_11__wrapping_next_power_of_two as impl_usize__wrapping_next_power_of_two}

include Core_models.Bundle {impl_11__next_power_of_two as impl_usize__next_power_of_two}

include Core_models.Bundle {impl_11__reverse_bits as impl_usize__reverse_bits}

include Core_models.Bundle {impl_11__widening_mul as impl_usize__widening_mul}

include Core_models.Bundle {impl_11__carrying_mul_add as impl_usize__carrying_mul_add}

include Core_models.Bundle {impl_11__carrying_mul as impl_usize__carrying_mul}

include Core_models.Bundle {impl_11__carrying_add as impl_usize__carrying_add}

include Core_models.Bundle {impl_11__borrowing_sub as impl_usize__borrowing_sub}

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

include Core_models.Bundle {impl_12__min_value as impl_i8__min_value}

include Core_models.Bundle {impl_12__max_value as impl_i8__max_value}

include Core_models.Bundle {impl_12__cast_unsigned as impl_i8__cast_unsigned}

include Core_models.Bundle {impl_12__is_positive as impl_i8__is_positive}

include Core_models.Bundle {impl_12__is_negative as impl_i8__is_negative}

include Core_models.Bundle {impl_12__count_zeros as impl_i8__count_zeros}

include Core_models.Bundle {impl_12__checked_ilog2 as impl_i8__checked_ilog2}

include Core_models.Bundle {impl_12__overflowing_neg as impl_i8__overflowing_neg}

include Core_models.Bundle {impl_12__checked_neg as impl_i8__checked_neg}

include Core_models.Bundle {impl_12__saturating_neg as impl_i8__saturating_neg}

include Core_models.Bundle {impl_12__strict_neg as impl_i8__strict_neg}

include Core_models.Bundle {impl_12__unchecked_neg as impl_i8__unchecked_neg}

include Core_models.Bundle {impl_12__wrapping_abs as impl_i8__wrapping_abs}

include Core_models.Bundle {impl_12__overflowing_abs as impl_i8__overflowing_abs}

include Core_models.Bundle {impl_12__checked_abs as impl_i8__checked_abs}

include Core_models.Bundle {impl_12__saturating_abs as impl_i8__saturating_abs}

include Core_models.Bundle {impl_12__strict_abs as impl_i8__strict_abs}

include Core_models.Bundle {impl_12__unsigned_abs as impl_i8__unsigned_abs}

include Core_models.Bundle {impl_12__wrapping_pow as impl_i8__wrapping_pow}

include Core_models.Bundle {impl_12__saturating_pow as impl_i8__saturating_pow}

include Core_models.Bundle {impl_12__strict_pow as impl_i8__strict_pow}

include Core_models.Bundle {impl_12__strict_add as impl_i8__strict_add}

include Core_models.Bundle {impl_12__strict_sub as impl_i8__strict_sub}

include Core_models.Bundle {impl_12__strict_mul as impl_i8__strict_mul}

include Core_models.Bundle {impl_12__overflowing_div as impl_i8__overflowing_div}

include Core_models.Bundle {impl_12__overflowing_rem as impl_i8__overflowing_rem}

include Core_models.Bundle {impl_12__wrapping_div as impl_i8__wrapping_div}

include Core_models.Bundle {impl_12__wrapping_rem as impl_i8__wrapping_rem}

include Core_models.Bundle {impl_12__saturating_div as impl_i8__saturating_div}

include Core_models.Bundle {impl_12__strict_div as impl_i8__strict_div}

include Core_models.Bundle {impl_12__strict_rem as impl_i8__strict_rem}

include Core_models.Bundle {impl_12__div_euclid as impl_i8__div_euclid}

include Core_models.Bundle {impl_12__overflowing_div_euclid as impl_i8__overflowing_div_euclid}

include Core_models.Bundle {impl_12__wrapping_div_euclid as impl_i8__wrapping_div_euclid}

include Core_models.Bundle {impl_12__checked_div_euclid as impl_i8__checked_div_euclid}

include Core_models.Bundle {impl_12__strict_div_euclid as impl_i8__strict_div_euclid}

include Core_models.Bundle {impl_12__overflowing_rem_euclid as impl_i8__overflowing_rem_euclid}

include Core_models.Bundle {impl_12__wrapping_rem_euclid as impl_i8__wrapping_rem_euclid}

include Core_models.Bundle {impl_12__checked_rem_euclid as impl_i8__checked_rem_euclid}

include Core_models.Bundle {impl_12__strict_rem_euclid as impl_i8__strict_rem_euclid}

include Core_models.Bundle {impl_12__div_floor as impl_i8__div_floor}

include Core_models.Bundle {impl_12__div_exact as impl_i8__div_exact}

include Core_models.Bundle {impl_12__checked_div_exact as impl_i8__checked_div_exact}

include Core_models.Bundle {impl_12__unchecked_div_exact as impl_i8__unchecked_div_exact}

include Core_models.Bundle {impl_12__abs_diff as impl_i8__abs_diff}

include Core_models.Bundle {impl_12__midpoint as impl_i8__midpoint}

include Core_models.Bundle {impl_12__checked_next_multiple_of as impl_i8__checked_next_multiple_of}

include Core_models.Bundle {impl_12__wrapping_add_unsigned as impl_i8__wrapping_add_unsigned}

include Core_models.Bundle {impl_12__wrapping_sub_unsigned as impl_i8__wrapping_sub_unsigned}

include Core_models.Bundle {impl_12__overflowing_add_unsigned as impl_i8__overflowing_add_unsigned}

include Core_models.Bundle {impl_12__overflowing_sub_unsigned as impl_i8__overflowing_sub_unsigned}

include Core_models.Bundle {impl_12__saturating_add_unsigned as impl_i8__saturating_add_unsigned}

include Core_models.Bundle {impl_12__saturating_sub_unsigned as impl_i8__saturating_sub_unsigned}

include Core_models.Bundle {impl_12__strict_add_unsigned as impl_i8__strict_add_unsigned}

include Core_models.Bundle {impl_12__strict_sub_unsigned as impl_i8__strict_sub_unsigned}

include Core_models.Bundle {impl_12__reverse_bits as impl_i8__reverse_bits}

include Core_models.Bundle {impl_12__next_multiple_of as impl_i8__next_multiple_of}

include Core_models.Bundle {impl_12__widening_mul as impl_i8__widening_mul}

include Core_models.Bundle {impl_12__carrying_mul_add as impl_i8__carrying_mul_add}

include Core_models.Bundle {impl_12__carrying_mul as impl_i8__carrying_mul}

include Core_models.Bundle {impl_12__carrying_add as impl_i8__carrying_add}

include Core_models.Bundle {impl_12__borrowing_sub as impl_i8__borrowing_sub}

include Core_models.Bundle {impl_12__trailing_zeros as impl_i8__trailing_zeros}

include Core_models.Bundle {impl_12__trailing_ones as impl_i8__trailing_ones}

include Core_models.Bundle {impl_12__leading_ones as impl_i8__leading_ones}

include Core_models.Bundle {impl_12__highest_one as impl_i8__highest_one}

include Core_models.Bundle {impl_12__lowest_one as impl_i8__lowest_one}

include Core_models.Bundle {impl_12__isolate_lowest_one as impl_i8__isolate_lowest_one}

include Core_models.Bundle {impl_12__isolate_highest_one as impl_i8__isolate_highest_one}

include Core_models.Bundle {impl_12__swap_bytes as impl_i8__swap_bytes}

include Core_models.Bundle {impl_12__to_be as impl_i8__to_be}

include Core_models.Bundle {impl_12__to_le as impl_i8__to_le}

include Core_models.Bundle {impl_12__from_be as impl_i8__from_be}

include Core_models.Bundle {impl_12__from_le as impl_i8__from_le}

include Core_models.Bundle {impl_12__to_ne_bytes as impl_i8__to_ne_bytes}

include Core_models.Bundle {impl_12__from_ne_bytes as impl_i8__from_ne_bytes}

include Core_models.Bundle {impl_12__wrapping_shl as impl_i8__wrapping_shl}

include Core_models.Bundle {impl_12__wrapping_shr as impl_i8__wrapping_shr}

include Core_models.Bundle {impl_12__overflowing_shl as impl_i8__overflowing_shl}

include Core_models.Bundle {impl_12__overflowing_shr as impl_i8__overflowing_shr}

include Core_models.Bundle {impl_12__checked_shl as impl_i8__checked_shl}

include Core_models.Bundle {impl_12__checked_shr as impl_i8__checked_shr}

include Core_models.Bundle {impl_12__strict_shl as impl_i8__strict_shl}

include Core_models.Bundle {impl_12__strict_shr as impl_i8__strict_shr}

include Core_models.Bundle {impl_12__unbounded_shl as impl_i8__unbounded_shl}

include Core_models.Bundle {impl_12__unbounded_shr as impl_i8__unbounded_shr}

include Core_models.Bundle {impl_12__unchecked_shl as impl_i8__unchecked_shl}

include Core_models.Bundle {impl_12__unchecked_shr as impl_i8__unchecked_shr}

include Core_models.Bundle {impl_12__shl_exact as impl_i8__shl_exact}

include Core_models.Bundle {impl_12__shr_exact as impl_i8__shr_exact}

include Core_models.Bundle {impl_12__unchecked_shl_exact as impl_i8__unchecked_shl_exact}

include Core_models.Bundle {impl_12__unchecked_shr_exact as impl_i8__unchecked_shr_exact}

include Core_models.Bundle {impl_12__clamp_magnitude as impl_i8__clamp_magnitude}

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

include Core_models.Bundle {impl_13__min_value as impl_i16__min_value}

include Core_models.Bundle {impl_13__max_value as impl_i16__max_value}

include Core_models.Bundle {impl_13__cast_unsigned as impl_i16__cast_unsigned}

include Core_models.Bundle {impl_13__is_positive as impl_i16__is_positive}

include Core_models.Bundle {impl_13__is_negative as impl_i16__is_negative}

include Core_models.Bundle {impl_13__count_zeros as impl_i16__count_zeros}

include Core_models.Bundle {impl_13__checked_ilog2 as impl_i16__checked_ilog2}

include Core_models.Bundle {impl_13__overflowing_neg as impl_i16__overflowing_neg}

include Core_models.Bundle {impl_13__checked_neg as impl_i16__checked_neg}

include Core_models.Bundle {impl_13__saturating_neg as impl_i16__saturating_neg}

include Core_models.Bundle {impl_13__strict_neg as impl_i16__strict_neg}

include Core_models.Bundle {impl_13__unchecked_neg as impl_i16__unchecked_neg}

include Core_models.Bundle {impl_13__wrapping_abs as impl_i16__wrapping_abs}

include Core_models.Bundle {impl_13__overflowing_abs as impl_i16__overflowing_abs}

include Core_models.Bundle {impl_13__checked_abs as impl_i16__checked_abs}

include Core_models.Bundle {impl_13__saturating_abs as impl_i16__saturating_abs}

include Core_models.Bundle {impl_13__strict_abs as impl_i16__strict_abs}

include Core_models.Bundle {impl_13__unsigned_abs as impl_i16__unsigned_abs}

include Core_models.Bundle {impl_13__wrapping_pow as impl_i16__wrapping_pow}

include Core_models.Bundle {impl_13__saturating_pow as impl_i16__saturating_pow}

include Core_models.Bundle {impl_13__strict_pow as impl_i16__strict_pow}

include Core_models.Bundle {impl_13__strict_add as impl_i16__strict_add}

include Core_models.Bundle {impl_13__strict_sub as impl_i16__strict_sub}

include Core_models.Bundle {impl_13__strict_mul as impl_i16__strict_mul}

include Core_models.Bundle {impl_13__overflowing_div as impl_i16__overflowing_div}

include Core_models.Bundle {impl_13__overflowing_rem as impl_i16__overflowing_rem}

include Core_models.Bundle {impl_13__wrapping_div as impl_i16__wrapping_div}

include Core_models.Bundle {impl_13__wrapping_rem as impl_i16__wrapping_rem}

include Core_models.Bundle {impl_13__saturating_div as impl_i16__saturating_div}

include Core_models.Bundle {impl_13__strict_div as impl_i16__strict_div}

include Core_models.Bundle {impl_13__strict_rem as impl_i16__strict_rem}

include Core_models.Bundle {impl_13__div_euclid as impl_i16__div_euclid}

include Core_models.Bundle {impl_13__overflowing_div_euclid as impl_i16__overflowing_div_euclid}

include Core_models.Bundle {impl_13__wrapping_div_euclid as impl_i16__wrapping_div_euclid}

include Core_models.Bundle {impl_13__checked_div_euclid as impl_i16__checked_div_euclid}

include Core_models.Bundle {impl_13__strict_div_euclid as impl_i16__strict_div_euclid}

include Core_models.Bundle {impl_13__overflowing_rem_euclid as impl_i16__overflowing_rem_euclid}

include Core_models.Bundle {impl_13__wrapping_rem_euclid as impl_i16__wrapping_rem_euclid}

include Core_models.Bundle {impl_13__checked_rem_euclid as impl_i16__checked_rem_euclid}

include Core_models.Bundle {impl_13__strict_rem_euclid as impl_i16__strict_rem_euclid}

include Core_models.Bundle {impl_13__div_floor as impl_i16__div_floor}

include Core_models.Bundle {impl_13__div_exact as impl_i16__div_exact}

include Core_models.Bundle {impl_13__checked_div_exact as impl_i16__checked_div_exact}

include Core_models.Bundle {impl_13__unchecked_div_exact as impl_i16__unchecked_div_exact}

include Core_models.Bundle {impl_13__abs_diff as impl_i16__abs_diff}

include Core_models.Bundle {impl_13__midpoint as impl_i16__midpoint}

include Core_models.Bundle {impl_13__checked_next_multiple_of as impl_i16__checked_next_multiple_of}

include Core_models.Bundle {impl_13__wrapping_add_unsigned as impl_i16__wrapping_add_unsigned}

include Core_models.Bundle {impl_13__wrapping_sub_unsigned as impl_i16__wrapping_sub_unsigned}

include Core_models.Bundle {impl_13__overflowing_add_unsigned as impl_i16__overflowing_add_unsigned}

include Core_models.Bundle {impl_13__overflowing_sub_unsigned as impl_i16__overflowing_sub_unsigned}

include Core_models.Bundle {impl_13__saturating_add_unsigned as impl_i16__saturating_add_unsigned}

include Core_models.Bundle {impl_13__saturating_sub_unsigned as impl_i16__saturating_sub_unsigned}

include Core_models.Bundle {impl_13__strict_add_unsigned as impl_i16__strict_add_unsigned}

include Core_models.Bundle {impl_13__strict_sub_unsigned as impl_i16__strict_sub_unsigned}

include Core_models.Bundle {impl_13__reverse_bits as impl_i16__reverse_bits}

include Core_models.Bundle {impl_13__next_multiple_of as impl_i16__next_multiple_of}

include Core_models.Bundle {impl_13__widening_mul as impl_i16__widening_mul}

include Core_models.Bundle {impl_13__carrying_mul_add as impl_i16__carrying_mul_add}

include Core_models.Bundle {impl_13__carrying_mul as impl_i16__carrying_mul}

include Core_models.Bundle {impl_13__carrying_add as impl_i16__carrying_add}

include Core_models.Bundle {impl_13__borrowing_sub as impl_i16__borrowing_sub}

include Core_models.Bundle {impl_13__trailing_zeros as impl_i16__trailing_zeros}

include Core_models.Bundle {impl_13__trailing_ones as impl_i16__trailing_ones}

include Core_models.Bundle {impl_13__leading_ones as impl_i16__leading_ones}

include Core_models.Bundle {impl_13__highest_one as impl_i16__highest_one}

include Core_models.Bundle {impl_13__lowest_one as impl_i16__lowest_one}

include Core_models.Bundle {impl_13__isolate_lowest_one as impl_i16__isolate_lowest_one}

include Core_models.Bundle {impl_13__isolate_highest_one as impl_i16__isolate_highest_one}

include Core_models.Bundle {impl_13__swap_bytes as impl_i16__swap_bytes}

include Core_models.Bundle {impl_13__to_be as impl_i16__to_be}

include Core_models.Bundle {impl_13__to_le as impl_i16__to_le}

include Core_models.Bundle {impl_13__from_be as impl_i16__from_be}

include Core_models.Bundle {impl_13__from_le as impl_i16__from_le}

include Core_models.Bundle {impl_13__to_ne_bytes as impl_i16__to_ne_bytes}

include Core_models.Bundle {impl_13__from_ne_bytes as impl_i16__from_ne_bytes}

include Core_models.Bundle {impl_13__wrapping_shl as impl_i16__wrapping_shl}

include Core_models.Bundle {impl_13__wrapping_shr as impl_i16__wrapping_shr}

include Core_models.Bundle {impl_13__overflowing_shl as impl_i16__overflowing_shl}

include Core_models.Bundle {impl_13__overflowing_shr as impl_i16__overflowing_shr}

include Core_models.Bundle {impl_13__checked_shl as impl_i16__checked_shl}

include Core_models.Bundle {impl_13__checked_shr as impl_i16__checked_shr}

include Core_models.Bundle {impl_13__strict_shl as impl_i16__strict_shl}

include Core_models.Bundle {impl_13__strict_shr as impl_i16__strict_shr}

include Core_models.Bundle {impl_13__unbounded_shl as impl_i16__unbounded_shl}

include Core_models.Bundle {impl_13__unbounded_shr as impl_i16__unbounded_shr}

include Core_models.Bundle {impl_13__unchecked_shl as impl_i16__unchecked_shl}

include Core_models.Bundle {impl_13__unchecked_shr as impl_i16__unchecked_shr}

include Core_models.Bundle {impl_13__shl_exact as impl_i16__shl_exact}

include Core_models.Bundle {impl_13__shr_exact as impl_i16__shr_exact}

include Core_models.Bundle {impl_13__unchecked_shl_exact as impl_i16__unchecked_shl_exact}

include Core_models.Bundle {impl_13__unchecked_shr_exact as impl_i16__unchecked_shr_exact}

include Core_models.Bundle {impl_13__clamp_magnitude as impl_i16__clamp_magnitude}

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

include Core_models.Bundle {impl_14__min_value as impl_i32__min_value}

include Core_models.Bundle {impl_14__max_value as impl_i32__max_value}

include Core_models.Bundle {impl_14__cast_unsigned as impl_i32__cast_unsigned}

include Core_models.Bundle {impl_14__is_positive as impl_i32__is_positive}

include Core_models.Bundle {impl_14__is_negative as impl_i32__is_negative}

include Core_models.Bundle {impl_14__count_zeros as impl_i32__count_zeros}

include Core_models.Bundle {impl_14__checked_ilog2 as impl_i32__checked_ilog2}

include Core_models.Bundle {impl_14__overflowing_neg as impl_i32__overflowing_neg}

include Core_models.Bundle {impl_14__checked_neg as impl_i32__checked_neg}

include Core_models.Bundle {impl_14__saturating_neg as impl_i32__saturating_neg}

include Core_models.Bundle {impl_14__strict_neg as impl_i32__strict_neg}

include Core_models.Bundle {impl_14__unchecked_neg as impl_i32__unchecked_neg}

include Core_models.Bundle {impl_14__wrapping_abs as impl_i32__wrapping_abs}

include Core_models.Bundle {impl_14__overflowing_abs as impl_i32__overflowing_abs}

include Core_models.Bundle {impl_14__checked_abs as impl_i32__checked_abs}

include Core_models.Bundle {impl_14__saturating_abs as impl_i32__saturating_abs}

include Core_models.Bundle {impl_14__strict_abs as impl_i32__strict_abs}

include Core_models.Bundle {impl_14__unsigned_abs as impl_i32__unsigned_abs}

include Core_models.Bundle {impl_14__wrapping_pow as impl_i32__wrapping_pow}

include Core_models.Bundle {impl_14__saturating_pow as impl_i32__saturating_pow}

include Core_models.Bundle {impl_14__strict_pow as impl_i32__strict_pow}

include Core_models.Bundle {impl_14__strict_add as impl_i32__strict_add}

include Core_models.Bundle {impl_14__strict_sub as impl_i32__strict_sub}

include Core_models.Bundle {impl_14__strict_mul as impl_i32__strict_mul}

include Core_models.Bundle {impl_14__overflowing_div as impl_i32__overflowing_div}

include Core_models.Bundle {impl_14__overflowing_rem as impl_i32__overflowing_rem}

include Core_models.Bundle {impl_14__wrapping_div as impl_i32__wrapping_div}

include Core_models.Bundle {impl_14__wrapping_rem as impl_i32__wrapping_rem}

include Core_models.Bundle {impl_14__saturating_div as impl_i32__saturating_div}

include Core_models.Bundle {impl_14__strict_div as impl_i32__strict_div}

include Core_models.Bundle {impl_14__strict_rem as impl_i32__strict_rem}

include Core_models.Bundle {impl_14__div_euclid as impl_i32__div_euclid}

include Core_models.Bundle {impl_14__overflowing_div_euclid as impl_i32__overflowing_div_euclid}

include Core_models.Bundle {impl_14__wrapping_div_euclid as impl_i32__wrapping_div_euclid}

include Core_models.Bundle {impl_14__checked_div_euclid as impl_i32__checked_div_euclid}

include Core_models.Bundle {impl_14__strict_div_euclid as impl_i32__strict_div_euclid}

include Core_models.Bundle {impl_14__overflowing_rem_euclid as impl_i32__overflowing_rem_euclid}

include Core_models.Bundle {impl_14__wrapping_rem_euclid as impl_i32__wrapping_rem_euclid}

include Core_models.Bundle {impl_14__checked_rem_euclid as impl_i32__checked_rem_euclid}

include Core_models.Bundle {impl_14__strict_rem_euclid as impl_i32__strict_rem_euclid}

include Core_models.Bundle {impl_14__div_floor as impl_i32__div_floor}

include Core_models.Bundle {impl_14__div_exact as impl_i32__div_exact}

include Core_models.Bundle {impl_14__checked_div_exact as impl_i32__checked_div_exact}

include Core_models.Bundle {impl_14__unchecked_div_exact as impl_i32__unchecked_div_exact}

include Core_models.Bundle {impl_14__abs_diff as impl_i32__abs_diff}

include Core_models.Bundle {impl_14__midpoint as impl_i32__midpoint}

include Core_models.Bundle {impl_14__checked_next_multiple_of as impl_i32__checked_next_multiple_of}

include Core_models.Bundle {impl_14__wrapping_add_unsigned as impl_i32__wrapping_add_unsigned}

include Core_models.Bundle {impl_14__wrapping_sub_unsigned as impl_i32__wrapping_sub_unsigned}

include Core_models.Bundle {impl_14__overflowing_add_unsigned as impl_i32__overflowing_add_unsigned}

include Core_models.Bundle {impl_14__overflowing_sub_unsigned as impl_i32__overflowing_sub_unsigned}

include Core_models.Bundle {impl_14__saturating_add_unsigned as impl_i32__saturating_add_unsigned}

include Core_models.Bundle {impl_14__saturating_sub_unsigned as impl_i32__saturating_sub_unsigned}

include Core_models.Bundle {impl_14__strict_add_unsigned as impl_i32__strict_add_unsigned}

include Core_models.Bundle {impl_14__strict_sub_unsigned as impl_i32__strict_sub_unsigned}

include Core_models.Bundle {impl_14__reverse_bits as impl_i32__reverse_bits}

include Core_models.Bundle {impl_14__next_multiple_of as impl_i32__next_multiple_of}

include Core_models.Bundle {impl_14__widening_mul as impl_i32__widening_mul}

include Core_models.Bundle {impl_14__carrying_mul_add as impl_i32__carrying_mul_add}

include Core_models.Bundle {impl_14__carrying_mul as impl_i32__carrying_mul}

include Core_models.Bundle {impl_14__carrying_add as impl_i32__carrying_add}

include Core_models.Bundle {impl_14__borrowing_sub as impl_i32__borrowing_sub}

include Core_models.Bundle {impl_14__trailing_zeros as impl_i32__trailing_zeros}

include Core_models.Bundle {impl_14__trailing_ones as impl_i32__trailing_ones}

include Core_models.Bundle {impl_14__leading_ones as impl_i32__leading_ones}

include Core_models.Bundle {impl_14__highest_one as impl_i32__highest_one}

include Core_models.Bundle {impl_14__lowest_one as impl_i32__lowest_one}

include Core_models.Bundle {impl_14__isolate_lowest_one as impl_i32__isolate_lowest_one}

include Core_models.Bundle {impl_14__isolate_highest_one as impl_i32__isolate_highest_one}

include Core_models.Bundle {impl_14__swap_bytes as impl_i32__swap_bytes}

include Core_models.Bundle {impl_14__to_be as impl_i32__to_be}

include Core_models.Bundle {impl_14__to_le as impl_i32__to_le}

include Core_models.Bundle {impl_14__from_be as impl_i32__from_be}

include Core_models.Bundle {impl_14__from_le as impl_i32__from_le}

include Core_models.Bundle {impl_14__to_ne_bytes as impl_i32__to_ne_bytes}

include Core_models.Bundle {impl_14__from_ne_bytes as impl_i32__from_ne_bytes}

include Core_models.Bundle {impl_14__wrapping_shl as impl_i32__wrapping_shl}

include Core_models.Bundle {impl_14__wrapping_shr as impl_i32__wrapping_shr}

include Core_models.Bundle {impl_14__overflowing_shl as impl_i32__overflowing_shl}

include Core_models.Bundle {impl_14__overflowing_shr as impl_i32__overflowing_shr}

include Core_models.Bundle {impl_14__checked_shl as impl_i32__checked_shl}

include Core_models.Bundle {impl_14__checked_shr as impl_i32__checked_shr}

include Core_models.Bundle {impl_14__strict_shl as impl_i32__strict_shl}

include Core_models.Bundle {impl_14__strict_shr as impl_i32__strict_shr}

include Core_models.Bundle {impl_14__unbounded_shl as impl_i32__unbounded_shl}

include Core_models.Bundle {impl_14__unbounded_shr as impl_i32__unbounded_shr}

include Core_models.Bundle {impl_14__unchecked_shl as impl_i32__unchecked_shl}

include Core_models.Bundle {impl_14__unchecked_shr as impl_i32__unchecked_shr}

include Core_models.Bundle {impl_14__shl_exact as impl_i32__shl_exact}

include Core_models.Bundle {impl_14__shr_exact as impl_i32__shr_exact}

include Core_models.Bundle {impl_14__unchecked_shl_exact as impl_i32__unchecked_shl_exact}

include Core_models.Bundle {impl_14__unchecked_shr_exact as impl_i32__unchecked_shr_exact}

include Core_models.Bundle {impl_14__clamp_magnitude as impl_i32__clamp_magnitude}

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

include Core_models.Bundle {impl_15__min_value as impl_i64__min_value}

include Core_models.Bundle {impl_15__max_value as impl_i64__max_value}

include Core_models.Bundle {impl_15__cast_unsigned as impl_i64__cast_unsigned}

include Core_models.Bundle {impl_15__is_positive as impl_i64__is_positive}

include Core_models.Bundle {impl_15__is_negative as impl_i64__is_negative}

include Core_models.Bundle {impl_15__count_zeros as impl_i64__count_zeros}

include Core_models.Bundle {impl_15__checked_ilog2 as impl_i64__checked_ilog2}

include Core_models.Bundle {impl_15__overflowing_neg as impl_i64__overflowing_neg}

include Core_models.Bundle {impl_15__checked_neg as impl_i64__checked_neg}

include Core_models.Bundle {impl_15__saturating_neg as impl_i64__saturating_neg}

include Core_models.Bundle {impl_15__strict_neg as impl_i64__strict_neg}

include Core_models.Bundle {impl_15__unchecked_neg as impl_i64__unchecked_neg}

include Core_models.Bundle {impl_15__wrapping_abs as impl_i64__wrapping_abs}

include Core_models.Bundle {impl_15__overflowing_abs as impl_i64__overflowing_abs}

include Core_models.Bundle {impl_15__checked_abs as impl_i64__checked_abs}

include Core_models.Bundle {impl_15__saturating_abs as impl_i64__saturating_abs}

include Core_models.Bundle {impl_15__strict_abs as impl_i64__strict_abs}

include Core_models.Bundle {impl_15__unsigned_abs as impl_i64__unsigned_abs}

include Core_models.Bundle {impl_15__wrapping_pow as impl_i64__wrapping_pow}

include Core_models.Bundle {impl_15__saturating_pow as impl_i64__saturating_pow}

include Core_models.Bundle {impl_15__strict_pow as impl_i64__strict_pow}

include Core_models.Bundle {impl_15__strict_add as impl_i64__strict_add}

include Core_models.Bundle {impl_15__strict_sub as impl_i64__strict_sub}

include Core_models.Bundle {impl_15__strict_mul as impl_i64__strict_mul}

include Core_models.Bundle {impl_15__overflowing_div as impl_i64__overflowing_div}

include Core_models.Bundle {impl_15__overflowing_rem as impl_i64__overflowing_rem}

include Core_models.Bundle {impl_15__wrapping_div as impl_i64__wrapping_div}

include Core_models.Bundle {impl_15__wrapping_rem as impl_i64__wrapping_rem}

include Core_models.Bundle {impl_15__saturating_div as impl_i64__saturating_div}

include Core_models.Bundle {impl_15__strict_div as impl_i64__strict_div}

include Core_models.Bundle {impl_15__strict_rem as impl_i64__strict_rem}

include Core_models.Bundle {impl_15__div_euclid as impl_i64__div_euclid}

include Core_models.Bundle {impl_15__overflowing_div_euclid as impl_i64__overflowing_div_euclid}

include Core_models.Bundle {impl_15__wrapping_div_euclid as impl_i64__wrapping_div_euclid}

include Core_models.Bundle {impl_15__checked_div_euclid as impl_i64__checked_div_euclid}

include Core_models.Bundle {impl_15__strict_div_euclid as impl_i64__strict_div_euclid}

include Core_models.Bundle {impl_15__overflowing_rem_euclid as impl_i64__overflowing_rem_euclid}

include Core_models.Bundle {impl_15__wrapping_rem_euclid as impl_i64__wrapping_rem_euclid}

include Core_models.Bundle {impl_15__checked_rem_euclid as impl_i64__checked_rem_euclid}

include Core_models.Bundle {impl_15__strict_rem_euclid as impl_i64__strict_rem_euclid}

include Core_models.Bundle {impl_15__div_floor as impl_i64__div_floor}

include Core_models.Bundle {impl_15__div_exact as impl_i64__div_exact}

include Core_models.Bundle {impl_15__checked_div_exact as impl_i64__checked_div_exact}

include Core_models.Bundle {impl_15__unchecked_div_exact as impl_i64__unchecked_div_exact}

include Core_models.Bundle {impl_15__abs_diff as impl_i64__abs_diff}

include Core_models.Bundle {impl_15__midpoint as impl_i64__midpoint}

include Core_models.Bundle {impl_15__checked_next_multiple_of as impl_i64__checked_next_multiple_of}

include Core_models.Bundle {impl_15__wrapping_add_unsigned as impl_i64__wrapping_add_unsigned}

include Core_models.Bundle {impl_15__wrapping_sub_unsigned as impl_i64__wrapping_sub_unsigned}

include Core_models.Bundle {impl_15__overflowing_add_unsigned as impl_i64__overflowing_add_unsigned}

include Core_models.Bundle {impl_15__overflowing_sub_unsigned as impl_i64__overflowing_sub_unsigned}

include Core_models.Bundle {impl_15__saturating_add_unsigned as impl_i64__saturating_add_unsigned}

include Core_models.Bundle {impl_15__saturating_sub_unsigned as impl_i64__saturating_sub_unsigned}

include Core_models.Bundle {impl_15__strict_add_unsigned as impl_i64__strict_add_unsigned}

include Core_models.Bundle {impl_15__strict_sub_unsigned as impl_i64__strict_sub_unsigned}

include Core_models.Bundle {impl_15__reverse_bits as impl_i64__reverse_bits}

include Core_models.Bundle {impl_15__next_multiple_of as impl_i64__next_multiple_of}

include Core_models.Bundle {impl_15__widening_mul as impl_i64__widening_mul}

include Core_models.Bundle {impl_15__carrying_mul_add as impl_i64__carrying_mul_add}

include Core_models.Bundle {impl_15__carrying_mul as impl_i64__carrying_mul}

include Core_models.Bundle {impl_15__carrying_add as impl_i64__carrying_add}

include Core_models.Bundle {impl_15__borrowing_sub as impl_i64__borrowing_sub}

include Core_models.Bundle {impl_15__trailing_zeros as impl_i64__trailing_zeros}

include Core_models.Bundle {impl_15__trailing_ones as impl_i64__trailing_ones}

include Core_models.Bundle {impl_15__leading_ones as impl_i64__leading_ones}

include Core_models.Bundle {impl_15__highest_one as impl_i64__highest_one}

include Core_models.Bundle {impl_15__lowest_one as impl_i64__lowest_one}

include Core_models.Bundle {impl_15__isolate_lowest_one as impl_i64__isolate_lowest_one}

include Core_models.Bundle {impl_15__isolate_highest_one as impl_i64__isolate_highest_one}

include Core_models.Bundle {impl_15__swap_bytes as impl_i64__swap_bytes}

include Core_models.Bundle {impl_15__to_be as impl_i64__to_be}

include Core_models.Bundle {impl_15__to_le as impl_i64__to_le}

include Core_models.Bundle {impl_15__from_be as impl_i64__from_be}

include Core_models.Bundle {impl_15__from_le as impl_i64__from_le}

include Core_models.Bundle {impl_15__to_ne_bytes as impl_i64__to_ne_bytes}

include Core_models.Bundle {impl_15__from_ne_bytes as impl_i64__from_ne_bytes}

include Core_models.Bundle {impl_15__wrapping_shl as impl_i64__wrapping_shl}

include Core_models.Bundle {impl_15__wrapping_shr as impl_i64__wrapping_shr}

include Core_models.Bundle {impl_15__overflowing_shl as impl_i64__overflowing_shl}

include Core_models.Bundle {impl_15__overflowing_shr as impl_i64__overflowing_shr}

include Core_models.Bundle {impl_15__checked_shl as impl_i64__checked_shl}

include Core_models.Bundle {impl_15__checked_shr as impl_i64__checked_shr}

include Core_models.Bundle {impl_15__strict_shl as impl_i64__strict_shl}

include Core_models.Bundle {impl_15__strict_shr as impl_i64__strict_shr}

include Core_models.Bundle {impl_15__unbounded_shl as impl_i64__unbounded_shl}

include Core_models.Bundle {impl_15__unbounded_shr as impl_i64__unbounded_shr}

include Core_models.Bundle {impl_15__unchecked_shl as impl_i64__unchecked_shl}

include Core_models.Bundle {impl_15__unchecked_shr as impl_i64__unchecked_shr}

include Core_models.Bundle {impl_15__shl_exact as impl_i64__shl_exact}

include Core_models.Bundle {impl_15__shr_exact as impl_i64__shr_exact}

include Core_models.Bundle {impl_15__unchecked_shl_exact as impl_i64__unchecked_shl_exact}

include Core_models.Bundle {impl_15__unchecked_shr_exact as impl_i64__unchecked_shr_exact}

include Core_models.Bundle {impl_15__clamp_magnitude as impl_i64__clamp_magnitude}

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

include Core_models.Bundle {impl_16__min_value as impl_i128__min_value}

include Core_models.Bundle {impl_16__max_value as impl_i128__max_value}

include Core_models.Bundle {impl_16__cast_unsigned as impl_i128__cast_unsigned}

include Core_models.Bundle {impl_16__is_positive as impl_i128__is_positive}

include Core_models.Bundle {impl_16__is_negative as impl_i128__is_negative}

include Core_models.Bundle {impl_16__count_zeros as impl_i128__count_zeros}

include Core_models.Bundle {impl_16__checked_ilog2 as impl_i128__checked_ilog2}

include Core_models.Bundle {impl_16__overflowing_neg as impl_i128__overflowing_neg}

include Core_models.Bundle {impl_16__checked_neg as impl_i128__checked_neg}

include Core_models.Bundle {impl_16__saturating_neg as impl_i128__saturating_neg}

include Core_models.Bundle {impl_16__strict_neg as impl_i128__strict_neg}

include Core_models.Bundle {impl_16__unchecked_neg as impl_i128__unchecked_neg}

include Core_models.Bundle {impl_16__wrapping_abs as impl_i128__wrapping_abs}

include Core_models.Bundle {impl_16__overflowing_abs as impl_i128__overflowing_abs}

include Core_models.Bundle {impl_16__checked_abs as impl_i128__checked_abs}

include Core_models.Bundle {impl_16__saturating_abs as impl_i128__saturating_abs}

include Core_models.Bundle {impl_16__strict_abs as impl_i128__strict_abs}

include Core_models.Bundle {impl_16__unsigned_abs as impl_i128__unsigned_abs}

include Core_models.Bundle {impl_16__wrapping_pow as impl_i128__wrapping_pow}

include Core_models.Bundle {impl_16__saturating_pow as impl_i128__saturating_pow}

include Core_models.Bundle {impl_16__strict_pow as impl_i128__strict_pow}

include Core_models.Bundle {impl_16__strict_add as impl_i128__strict_add}

include Core_models.Bundle {impl_16__strict_sub as impl_i128__strict_sub}

include Core_models.Bundle {impl_16__strict_mul as impl_i128__strict_mul}

include Core_models.Bundle {impl_16__overflowing_div as impl_i128__overflowing_div}

include Core_models.Bundle {impl_16__overflowing_rem as impl_i128__overflowing_rem}

include Core_models.Bundle {impl_16__wrapping_div as impl_i128__wrapping_div}

include Core_models.Bundle {impl_16__wrapping_rem as impl_i128__wrapping_rem}

include Core_models.Bundle {impl_16__saturating_div as impl_i128__saturating_div}

include Core_models.Bundle {impl_16__strict_div as impl_i128__strict_div}

include Core_models.Bundle {impl_16__strict_rem as impl_i128__strict_rem}

include Core_models.Bundle {impl_16__div_euclid as impl_i128__div_euclid}

include Core_models.Bundle {impl_16__overflowing_div_euclid as impl_i128__overflowing_div_euclid}

include Core_models.Bundle {impl_16__wrapping_div_euclid as impl_i128__wrapping_div_euclid}

include Core_models.Bundle {impl_16__checked_div_euclid as impl_i128__checked_div_euclid}

include Core_models.Bundle {impl_16__strict_div_euclid as impl_i128__strict_div_euclid}

include Core_models.Bundle {impl_16__overflowing_rem_euclid as impl_i128__overflowing_rem_euclid}

include Core_models.Bundle {impl_16__wrapping_rem_euclid as impl_i128__wrapping_rem_euclid}

include Core_models.Bundle {impl_16__checked_rem_euclid as impl_i128__checked_rem_euclid}

include Core_models.Bundle {impl_16__strict_rem_euclid as impl_i128__strict_rem_euclid}

include Core_models.Bundle {impl_16__div_floor as impl_i128__div_floor}

include Core_models.Bundle {impl_16__div_exact as impl_i128__div_exact}

include Core_models.Bundle {impl_16__checked_div_exact as impl_i128__checked_div_exact}

include Core_models.Bundle {impl_16__unchecked_div_exact as impl_i128__unchecked_div_exact}

include Core_models.Bundle {impl_16__abs_diff as impl_i128__abs_diff}

include Core_models.Bundle {impl_16__midpoint as impl_i128__midpoint}

include Core_models.Bundle {impl_16__checked_next_multiple_of as impl_i128__checked_next_multiple_of}

include Core_models.Bundle {impl_16__wrapping_add_unsigned as impl_i128__wrapping_add_unsigned}

include Core_models.Bundle {impl_16__wrapping_sub_unsigned as impl_i128__wrapping_sub_unsigned}

include Core_models.Bundle {impl_16__overflowing_add_unsigned as impl_i128__overflowing_add_unsigned}

include Core_models.Bundle {impl_16__overflowing_sub_unsigned as impl_i128__overflowing_sub_unsigned}

include Core_models.Bundle {impl_16__saturating_add_unsigned as impl_i128__saturating_add_unsigned}

include Core_models.Bundle {impl_16__saturating_sub_unsigned as impl_i128__saturating_sub_unsigned}

include Core_models.Bundle {impl_16__strict_add_unsigned as impl_i128__strict_add_unsigned}

include Core_models.Bundle {impl_16__strict_sub_unsigned as impl_i128__strict_sub_unsigned}

include Core_models.Bundle {impl_16__reverse_bits as impl_i128__reverse_bits}

include Core_models.Bundle {impl_16__next_multiple_of as impl_i128__next_multiple_of}

include Core_models.Bundle {impl_16__widening_mul as impl_i128__widening_mul}

include Core_models.Bundle {impl_16__carrying_mul_add as impl_i128__carrying_mul_add}

include Core_models.Bundle {impl_16__carrying_mul as impl_i128__carrying_mul}

include Core_models.Bundle {impl_16__carrying_add as impl_i128__carrying_add}

include Core_models.Bundle {impl_16__borrowing_sub as impl_i128__borrowing_sub}

include Core_models.Bundle {impl_16__trailing_zeros as impl_i128__trailing_zeros}

include Core_models.Bundle {impl_16__trailing_ones as impl_i128__trailing_ones}

include Core_models.Bundle {impl_16__leading_ones as impl_i128__leading_ones}

include Core_models.Bundle {impl_16__highest_one as impl_i128__highest_one}

include Core_models.Bundle {impl_16__lowest_one as impl_i128__lowest_one}

include Core_models.Bundle {impl_16__isolate_lowest_one as impl_i128__isolate_lowest_one}

include Core_models.Bundle {impl_16__isolate_highest_one as impl_i128__isolate_highest_one}

include Core_models.Bundle {impl_16__swap_bytes as impl_i128__swap_bytes}

include Core_models.Bundle {impl_16__to_be as impl_i128__to_be}

include Core_models.Bundle {impl_16__to_le as impl_i128__to_le}

include Core_models.Bundle {impl_16__from_be as impl_i128__from_be}

include Core_models.Bundle {impl_16__from_le as impl_i128__from_le}

include Core_models.Bundle {impl_16__to_ne_bytes as impl_i128__to_ne_bytes}

include Core_models.Bundle {impl_16__from_ne_bytes as impl_i128__from_ne_bytes}

include Core_models.Bundle {impl_16__wrapping_shl as impl_i128__wrapping_shl}

include Core_models.Bundle {impl_16__wrapping_shr as impl_i128__wrapping_shr}

include Core_models.Bundle {impl_16__overflowing_shl as impl_i128__overflowing_shl}

include Core_models.Bundle {impl_16__overflowing_shr as impl_i128__overflowing_shr}

include Core_models.Bundle {impl_16__checked_shl as impl_i128__checked_shl}

include Core_models.Bundle {impl_16__checked_shr as impl_i128__checked_shr}

include Core_models.Bundle {impl_16__strict_shl as impl_i128__strict_shl}

include Core_models.Bundle {impl_16__strict_shr as impl_i128__strict_shr}

include Core_models.Bundle {impl_16__unbounded_shl as impl_i128__unbounded_shl}

include Core_models.Bundle {impl_16__unbounded_shr as impl_i128__unbounded_shr}

include Core_models.Bundle {impl_16__unchecked_shl as impl_i128__unchecked_shl}

include Core_models.Bundle {impl_16__unchecked_shr as impl_i128__unchecked_shr}

include Core_models.Bundle {impl_16__shl_exact as impl_i128__shl_exact}

include Core_models.Bundle {impl_16__shr_exact as impl_i128__shr_exact}

include Core_models.Bundle {impl_16__unchecked_shl_exact as impl_i128__unchecked_shl_exact}

include Core_models.Bundle {impl_16__unchecked_shr_exact as impl_i128__unchecked_shr_exact}

include Core_models.Bundle {impl_16__clamp_magnitude as impl_i128__clamp_magnitude}

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

include Core_models.Bundle {impl_17__min_value as impl_isize__min_value}

include Core_models.Bundle {impl_17__max_value as impl_isize__max_value}

include Core_models.Bundle {impl_17__cast_unsigned as impl_isize__cast_unsigned}

include Core_models.Bundle {impl_17__is_positive as impl_isize__is_positive}

include Core_models.Bundle {impl_17__is_negative as impl_isize__is_negative}

include Core_models.Bundle {impl_17__count_zeros as impl_isize__count_zeros}

include Core_models.Bundle {impl_17__checked_ilog2 as impl_isize__checked_ilog2}

include Core_models.Bundle {impl_17__overflowing_neg as impl_isize__overflowing_neg}

include Core_models.Bundle {impl_17__checked_neg as impl_isize__checked_neg}

include Core_models.Bundle {impl_17__saturating_neg as impl_isize__saturating_neg}

include Core_models.Bundle {impl_17__strict_neg as impl_isize__strict_neg}

include Core_models.Bundle {impl_17__unchecked_neg as impl_isize__unchecked_neg}

include Core_models.Bundle {impl_17__wrapping_abs as impl_isize__wrapping_abs}

include Core_models.Bundle {impl_17__overflowing_abs as impl_isize__overflowing_abs}

include Core_models.Bundle {impl_17__checked_abs as impl_isize__checked_abs}

include Core_models.Bundle {impl_17__saturating_abs as impl_isize__saturating_abs}

include Core_models.Bundle {impl_17__strict_abs as impl_isize__strict_abs}

include Core_models.Bundle {impl_17__unsigned_abs as impl_isize__unsigned_abs}

include Core_models.Bundle {impl_17__wrapping_pow as impl_isize__wrapping_pow}

include Core_models.Bundle {impl_17__saturating_pow as impl_isize__saturating_pow}

include Core_models.Bundle {impl_17__strict_pow as impl_isize__strict_pow}

include Core_models.Bundle {impl_17__strict_add as impl_isize__strict_add}

include Core_models.Bundle {impl_17__strict_sub as impl_isize__strict_sub}

include Core_models.Bundle {impl_17__strict_mul as impl_isize__strict_mul}

include Core_models.Bundle {impl_17__overflowing_div as impl_isize__overflowing_div}

include Core_models.Bundle {impl_17__overflowing_rem as impl_isize__overflowing_rem}

include Core_models.Bundle {impl_17__wrapping_div as impl_isize__wrapping_div}

include Core_models.Bundle {impl_17__wrapping_rem as impl_isize__wrapping_rem}

include Core_models.Bundle {impl_17__saturating_div as impl_isize__saturating_div}

include Core_models.Bundle {impl_17__strict_div as impl_isize__strict_div}

include Core_models.Bundle {impl_17__strict_rem as impl_isize__strict_rem}

include Core_models.Bundle {impl_17__div_euclid as impl_isize__div_euclid}

include Core_models.Bundle {impl_17__overflowing_div_euclid as impl_isize__overflowing_div_euclid}

include Core_models.Bundle {impl_17__wrapping_div_euclid as impl_isize__wrapping_div_euclid}

include Core_models.Bundle {impl_17__checked_div_euclid as impl_isize__checked_div_euclid}

include Core_models.Bundle {impl_17__strict_div_euclid as impl_isize__strict_div_euclid}

include Core_models.Bundle {impl_17__overflowing_rem_euclid as impl_isize__overflowing_rem_euclid}

include Core_models.Bundle {impl_17__wrapping_rem_euclid as impl_isize__wrapping_rem_euclid}

include Core_models.Bundle {impl_17__checked_rem_euclid as impl_isize__checked_rem_euclid}

include Core_models.Bundle {impl_17__strict_rem_euclid as impl_isize__strict_rem_euclid}

include Core_models.Bundle {impl_17__div_floor as impl_isize__div_floor}

include Core_models.Bundle {impl_17__div_exact as impl_isize__div_exact}

include Core_models.Bundle {impl_17__checked_div_exact as impl_isize__checked_div_exact}

include Core_models.Bundle {impl_17__unchecked_div_exact as impl_isize__unchecked_div_exact}

include Core_models.Bundle {impl_17__abs_diff as impl_isize__abs_diff}

include Core_models.Bundle {impl_17__midpoint as impl_isize__midpoint}

include Core_models.Bundle {impl_17__checked_next_multiple_of as impl_isize__checked_next_multiple_of}

include Core_models.Bundle {impl_17__wrapping_add_unsigned as impl_isize__wrapping_add_unsigned}

include Core_models.Bundle {impl_17__wrapping_sub_unsigned as impl_isize__wrapping_sub_unsigned}

include Core_models.Bundle {impl_17__overflowing_add_unsigned as impl_isize__overflowing_add_unsigned}

include Core_models.Bundle {impl_17__overflowing_sub_unsigned as impl_isize__overflowing_sub_unsigned}

include Core_models.Bundle {impl_17__saturating_add_unsigned as impl_isize__saturating_add_unsigned}

include Core_models.Bundle {impl_17__saturating_sub_unsigned as impl_isize__saturating_sub_unsigned}

include Core_models.Bundle {impl_17__strict_add_unsigned as impl_isize__strict_add_unsigned}

include Core_models.Bundle {impl_17__strict_sub_unsigned as impl_isize__strict_sub_unsigned}

include Core_models.Bundle {impl_17__reverse_bits as impl_isize__reverse_bits}

include Core_models.Bundle {impl_17__next_multiple_of as impl_isize__next_multiple_of}

include Core_models.Bundle {impl_17__widening_mul as impl_isize__widening_mul}

include Core_models.Bundle {impl_17__carrying_mul_add as impl_isize__carrying_mul_add}

include Core_models.Bundle {impl_17__carrying_mul as impl_isize__carrying_mul}

include Core_models.Bundle {impl_17__carrying_add as impl_isize__carrying_add}

include Core_models.Bundle {impl_17__borrowing_sub as impl_isize__borrowing_sub}

include Core_models.Bundle {impl_17__trailing_zeros as impl_isize__trailing_zeros}

include Core_models.Bundle {impl_17__trailing_ones as impl_isize__trailing_ones}

include Core_models.Bundle {impl_17__leading_ones as impl_isize__leading_ones}

include Core_models.Bundle {impl_17__highest_one as impl_isize__highest_one}

include Core_models.Bundle {impl_17__lowest_one as impl_isize__lowest_one}

include Core_models.Bundle {impl_17__isolate_lowest_one as impl_isize__isolate_lowest_one}

include Core_models.Bundle {impl_17__isolate_highest_one as impl_isize__isolate_highest_one}

include Core_models.Bundle {impl_17__swap_bytes as impl_isize__swap_bytes}

include Core_models.Bundle {impl_17__to_be as impl_isize__to_be}

include Core_models.Bundle {impl_17__to_le as impl_isize__to_le}

include Core_models.Bundle {impl_17__from_be as impl_isize__from_be}

include Core_models.Bundle {impl_17__from_le as impl_isize__from_le}

include Core_models.Bundle {impl_17__to_ne_bytes as impl_isize__to_ne_bytes}

include Core_models.Bundle {impl_17__from_ne_bytes as impl_isize__from_ne_bytes}

include Core_models.Bundle {impl_17__wrapping_shl as impl_isize__wrapping_shl}

include Core_models.Bundle {impl_17__wrapping_shr as impl_isize__wrapping_shr}

include Core_models.Bundle {impl_17__overflowing_shl as impl_isize__overflowing_shl}

include Core_models.Bundle {impl_17__overflowing_shr as impl_isize__overflowing_shr}

include Core_models.Bundle {impl_17__checked_shl as impl_isize__checked_shl}

include Core_models.Bundle {impl_17__checked_shr as impl_isize__checked_shr}

include Core_models.Bundle {impl_17__strict_shl as impl_isize__strict_shl}

include Core_models.Bundle {impl_17__strict_shr as impl_isize__strict_shr}

include Core_models.Bundle {impl_17__unbounded_shl as impl_isize__unbounded_shl}

include Core_models.Bundle {impl_17__unbounded_shr as impl_isize__unbounded_shr}

include Core_models.Bundle {impl_17__unchecked_shl as impl_isize__unchecked_shl}

include Core_models.Bundle {impl_17__unchecked_shr as impl_isize__unchecked_shr}

include Core_models.Bundle {impl_17__shl_exact as impl_isize__shl_exact}

include Core_models.Bundle {impl_17__shr_exact as impl_isize__shr_exact}

include Core_models.Bundle {impl_17__unchecked_shl_exact as impl_isize__unchecked_shl_exact}

include Core_models.Bundle {impl_17__unchecked_shr_exact as impl_isize__unchecked_shr_exact}

include Core_models.Bundle {impl_17__clamp_magnitude as impl_isize__clamp_magnitude}

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
