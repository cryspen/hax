//! Equivalence tests for `core::fmt`.
//!
//! `core::fmt` exists to *produce text*, and the model does not (see the module
//! documentation of `core-models/src/core/fmt.rs`). So the observations that can
//! be pinned here are the pure-data ones: the `FormattingOptions` setter/getter
//! pairs and the `NumBufferTrait` buffer sizes. Everything that needs a
//! `Formatter` is out of reach — one can only be obtained from the formatting
//! runtime, which the model leaves opaque.
//!
//! Comparisons go through `match` rather than `==` on `Option`, so that a test
//! observes only the item under test and not `Option`'s `PartialEq`.

use crate::helpers;
use rust_lean_test_macro::rust_lean_test;

// ----- FormattingOptions::new -----------------------------------------------

#[rust_lean_test]
pub fn test_formatting_options_new_width_unset() -> bool {
    match core::fmt::FormattingOptions::new().get_width() {
        Some(_) => false,
        None => true,
    }
}

#[rust_lean_test]
pub fn test_formatting_options_new_precision_unset() -> bool {
    match core::fmt::FormattingOptions::new().get_precision() {
        Some(_) => false,
        None => true,
    }
}

#[rust_lean_test]
pub fn test_formatting_options_new_align_unset() -> bool {
    match core::fmt::FormattingOptions::new().get_align() {
        Some(_) => false,
        None => true,
    }
}

#[rust_lean_test]
pub fn test_formatting_options_new_sign_unset() -> bool {
    match core::fmt::FormattingOptions::new().get_sign() {
        Some(_) => false,
        None => true,
    }
}

#[rust_lean_test]
pub fn test_formatting_options_new_debug_as_hex_unset() -> bool {
    match core::fmt::FormattingOptions::new().get_debug_as_hex() {
        Some(_) => false,
        None => true,
    }
}

// The `#[derive(Default)]` of real `core` would have used `'\0'` here; `new`
// deliberately uses a space.
#[rust_lean_test]
pub fn test_formatting_options_new_fill_is_space() -> bool {
    core::fmt::FormattingOptions::new().get_fill() == ' '
}

#[rust_lean_test]
pub fn test_formatting_options_new_flags_are_off() -> bool {
    let options = core::fmt::FormattingOptions::new();
    options.get_alternate() == false && options.get_sign_aware_zero_pad() == false
}

// ----- FormattingOptions::width ---------------------------------------------

#[rust_lean_test]
pub fn test_formatting_options_width_zero() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.width(Some(0));
    match options.get_width() {
        Some(width) => width == 0,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_formatting_options_width_max() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.width(Some(u16::MAX));
    match options.get_width() {
        Some(width) => width == u16::MAX,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_formatting_options_width_cleared() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.width(Some(7));
    options.width(helpers::none_u16());
    match options.get_width() {
        Some(_) => false,
        None => true,
    }
}

// ----- FormattingOptions::precision -----------------------------------------

#[rust_lean_test]
pub fn test_formatting_options_precision_zero() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.precision(Some(0));
    match options.get_precision() {
        Some(precision) => precision == 0,
        None => false,
    }
}

#[rust_lean_test]
pub fn test_formatting_options_precision_cleared() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.precision(Some(3));
    options.precision(helpers::none_u16());
    match options.get_precision() {
        Some(_) => false,
        None => true,
    }
}

// Setting the precision leaves the width alone, and the other way round: real
// `core` keeps the two in separate fields with separate flag bits.
#[rust_lean_test]
pub fn test_formatting_options_width_and_precision_are_independent() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.width(Some(4));
    options.precision(Some(9));
    match (options.get_width(), options.get_precision()) {
        (Some(width), Some(precision)) => width == 4 && precision == 9,
        _ => false,
    }
}

// ----- FormattingOptions::fill ----------------------------------------------

#[rust_lean_test]
pub fn test_formatting_options_fill() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.fill('x');
    options.get_fill() == 'x'
}

// The fill is stored next to the flags in real `core`; setting a flag must not
// disturb it.
#[rust_lean_test]
pub fn test_formatting_options_fill_survives_flags() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.fill('0');
    options.alternate(true);
    options.sign_aware_zero_pad(true);
    options.get_fill() == '0' && options.get_alternate() && options.get_sign_aware_zero_pad()
}

// ----- FormattingOptions::align ---------------------------------------------

#[rust_lean_test]
pub fn test_formatting_options_align_left() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.align(Some(core::fmt::Alignment::Left));
    match options.get_align() {
        Some(core::fmt::Alignment::Left) => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_formatting_options_align_right() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.align(Some(core::fmt::Alignment::Right));
    match options.get_align() {
        Some(core::fmt::Alignment::Right) => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_formatting_options_align_center() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.align(Some(core::fmt::Alignment::Center));
    match options.get_align() {
        Some(core::fmt::Alignment::Center) => true,
        _ => false,
    }
}

// ----- FormattingOptions::sign ----------------------------------------------

#[rust_lean_test]
pub fn test_formatting_options_sign_plus() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.sign(Some(core::fmt::Sign::Plus));
    match options.get_sign() {
        Some(core::fmt::Sign::Plus) => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_formatting_options_sign_minus() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.sign(Some(core::fmt::Sign::Minus));
    match options.get_sign() {
        Some(core::fmt::Sign::Minus) => true,
        _ => false,
    }
}

// `Plus` and `Minus` are two separate flag bits; the setter must clear the one
// it does not set.
#[rust_lean_test]
pub fn test_formatting_options_sign_replaced() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.sign(Some(core::fmt::Sign::Plus));
    options.sign(Some(core::fmt::Sign::Minus));
    match options.get_sign() {
        Some(core::fmt::Sign::Minus) => true,
        _ => false,
    }
}

// ----- FormattingOptions::debug_as_hex --------------------------------------

#[rust_lean_test]
pub fn test_formatting_options_debug_as_hex_lower() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.debug_as_hex(Some(core::fmt::DebugAsHex::Lower));
    match options.get_debug_as_hex() {
        Some(core::fmt::DebugAsHex::Lower) => true,
        _ => false,
    }
}

#[rust_lean_test]
pub fn test_formatting_options_debug_as_hex_upper() -> bool {
    let mut options = core::fmt::FormattingOptions::new();
    options.debug_as_hex(Some(core::fmt::DebugAsHex::Upper));
    match options.get_debug_as_hex() {
        Some(core::fmt::DebugAsHex::Upper) => true,
        _ => false,
    }
}

// ----- NumBufferTrait::BUF_SIZE ---------------------------------------------

#[rust_lean_test]
pub fn test_num_buffer_size_u8() -> bool {
    <u8 as core::fmt::NumBufferTrait>::BUF_SIZE == 3
}

// One more than the unsigned buffer of the same width: the sign takes a byte.
#[rust_lean_test]
pub fn test_num_buffer_size_i8() -> bool {
    <i8 as core::fmt::NumBufferTrait>::BUF_SIZE == 4
}

#[rust_lean_test]
pub fn test_num_buffer_size_u32() -> bool {
    <u32 as core::fmt::NumBufferTrait>::BUF_SIZE == 10
}

#[rust_lean_test]
pub fn test_num_buffer_size_u128() -> bool {
    <u128 as core::fmt::NumBufferTrait>::BUF_SIZE == 39
}

#[rust_lean_test]
pub fn test_num_buffer_size_usize() -> bool {
    <usize as core::fmt::NumBufferTrait>::BUF_SIZE == 20
}

#[rust_lean_test]
pub fn test_num_buffer_capacity() -> bool {
    core::fmt::NumBuffer::<u8>::new().capacity() == 40
}
