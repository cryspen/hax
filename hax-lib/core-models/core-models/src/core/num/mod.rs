#![allow(non_camel_case_types, unused_variables)]

use crate::option::Option;
use crate::result::Result;
use pastey::paste;

pub mod error;

use rust_primitives::arithmetic::*;

// Bounds must be spelled `<$Name>::MAX`/`MIN` (referring to core models), not
// `$Self::MAX`/`MIN` (real `core`): both print the same, but only the former is a
// dependency hax sees, and cycles it misses become recursive backend modules.
macro_rules! uint_impl {
    (
        $Self: ty,
        $ISelf: ty,
        $Name: ty,
        $Max: expr,
        $Bits: expr,
        $Bytes: expr,
    ) => {
        #[hax_lib::attributes]
        impl $Name {
            /// See [`std::primitive::u8::MIN`] (and similar for other unsigned integer types)
            pub const MIN: $Self = 0;
            /// See [`std::primitive::u8::MAX`] (and similar for other unsigned integer types)
            pub const MAX: $Self = $Max;
            /// See [`std::primitive::u8::BITS`] (and similar for other unsigned integer types)
            pub const BITS: core::primitive::u32 = $Bits;
            /// See [`std::primitive::u8::wrapping_add`] (and similar for other unsigned integer types)
            pub fn wrapping_add(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_add_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
            pub fn saturating_add(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_add_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
            pub fn overflowing_add(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_add_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
            pub fn checked_add(x: $Self, y: $Self) -> Option<$Self> {
                let (result, overflowed) = Self::overflowing_add(x, y);
                if overflowed {
                    Option::None
                } else {
                    Option::Some(result)
                }
            }
            /// See [`std::primitive::u8::unchecked_add`] (and similar for other integer types)
            #[hax_lib::requires(x.to_int() + y.to_int() <= <$Name>::MAX.to_int())]
            pub unsafe fn unchecked_add(x: $Self, y: $Self) -> $Self {
                x + y
            }
            /// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
            pub fn wrapping_sub(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_sub_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
            pub fn saturating_sub(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_sub_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
            pub fn overflowing_sub(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_sub_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
            pub fn checked_sub(x: $Self, y: $Self) -> Option<$Self> {
                let (result, overflowed) = Self::overflowing_sub(x, y);
                if overflowed {
                    Option::None
                } else {
                    Option::Some(result)
                }
            }
            /// See [`std::primitive::u8::unchecked_sub`] (and similar for other integer types)
            #[hax_lib::requires(x >= y)]
            pub unsafe fn unchecked_sub(x: $Self, y: $Self) -> $Self {
                x - y
            }
            /// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
            pub fn wrapping_mul(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_mul_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
            pub fn saturating_mul(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_mul_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
            pub fn overflowing_mul(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_mul_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
            pub fn checked_mul(x: $Self, y: $Self) -> Option<$Self> {
                let (result, overflowed) = Self::overflowing_mul(x, y);
                if overflowed {
                    Option::None
                } else {
                    Option::Some(result)
                }
            }
            /// See [`std::primitive::u8::unchecked_mul`] (and similar for other integer types)
            #[hax_lib::requires(x.to_int() * y.to_int() <= <$Name>::MAX.to_int())]
            pub unsafe fn unchecked_mul(x: $Self, y: $Self) -> $Self {
                x * y
            }
            /// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
            #[hax_lib::requires(y != 0)]
            pub fn rem_euclid(x: $Self, y: $Self) -> $Self {
                paste! { [<rem_euclid_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::pow`] (and similar for other integer types)
            pub fn pow(x: $Self, exp: core::primitive::u32) -> $Self {
                paste! { [<pow_ $Name>](x, exp) }
            }
            /// See [`std::primitive::u8::overflowing_pow`] (and similar for other integer types)
            pub fn overflowing_pow(x: $Self, exp: core::primitive::u32) -> ($Self, bool) {
                paste! { [<overflowing_pow_ $Name>](x, exp) }
            }
            /// See [`std::primitive::u8::checked_pow`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::exclude)] //avoid cyclic dependency
            pub fn checked_pow(x: $Self, exp: core::primitive::u32) -> Option<$Self> {
                let (result, overflowed) = Self::overflowing_pow(x, exp);
                if overflowed {
                    Option::None
                } else {
                    Option::Some(result)
                }
            }
            /// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
            pub fn count_ones(x: $Self) -> core::primitive::u32 {
                paste! { [<count_ones_ $Name>](x) }
            }
            /// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn rotate_right(x: $Self, n: core::primitive::u32) -> $Self {
                paste! { [<rotate_right_ $Name>](x, n) }
            }
            /// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn rotate_left(x: $Self, n: core::primitive::u32) -> $Self {
                paste! { [<rotate_left_ $Name>](x, n) }
            }
            /// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn leading_zeros(x: $Self) -> core::primitive::u32 {
                paste! { [<leading_zeros_ $Name>](x) }
            }
            /// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn ilog2(x: $Self) -> core::primitive::u32 {
                paste! { [<ilog2_ $Name>](x) }
            }
            /// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
            #[hax_lib::opaque]
            pub fn from_str_radix(
                src: &str,
                radix: core::primitive::u32,
            ) -> Result<$Self, error::ParseIntError> {
                let (parsed, value) = paste! { [<from_str_radix_ $Name>](src, radix) };
                if parsed {
                    Result::Ok(value)
                } else {
                    // The model's `ParseIntError` carries no distinguishable kind.
                    Result::Err(error::ParseIntError {
                        kind: error::IntErrorKind,
                    })
                }
            }
            /// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn from_be_bytes(bytes: [core::primitive::u8; $Bytes]) -> $Self {
                paste! { [<from_be_bytes_ $Name>](bytes) }
            }
            /// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn from_le_bytes(bytes: [core::primitive::u8; $Bytes]) -> $Self {
                paste! { [<from_le_bytes_ $Name>](bytes) }
            }
            /// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn to_be_bytes(bytes: $Self) -> [core::primitive::u8; $Bytes] {
                paste! { [<to_be_bytes_ $Name>](bytes) }
            }
            /// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn to_le_bytes(bytes: $Self) -> [core::primitive::u8; $Bytes] {
                paste! { [<to_le_bytes_ $Name>](bytes) }
            }
            /// See [`std::primitive::u8::checked_div`] (and similar for other integer types)
            pub fn checked_div(x: $Self, y: $Self) -> Option<$Self> {
                if y == 0 {
                    Option::None
                } else {
                    Option::Some(x / y)
                }
            }
            /// See [`std::primitive::u8::unchecked_div`] (and similar for other integer types)
            #[hax_lib::requires(y != 0)]
            pub unsafe fn unchecked_div(x: $Self, y: $Self) -> $Self {
                x / y
            }
            /// See [`std::primitive::u8::checked_rem`] (and similar for other integer types)
            pub fn checked_rem(x: $Self, y: $Self) -> Option<$Self> {
                if y == 0 {
                    Option::None
                } else {
                    Option::Some(x % y)
                }
            }
            /// See [`std::primitive::u8::unchecked_rem`] (and similar for other integer types)
            #[hax_lib::requires(y != 0)]
            pub unsafe fn unchecked_rem(x: $Self, y: $Self) -> $Self {
                x % y
            }
            /// See [`std::primitive::u8::is_power_of_two`] (and similar for other unsigned integer types)
            pub fn is_power_of_two(x: $Self) -> bool {
                x != 0 && (x & (x - 1)) == 0
            }
            /// See [`std::primitive::u8::div_ceil`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn div_ceil(x: $Self, y: $Self) -> $Self {
                let d = x / y;
                let r = x % y;
                if r > 0 { d + 1 } else { d }
            }
            /// See [`std::primitive::u8::is_multiple_of`] (and similar for other unsigned integer types)
            pub fn is_multiple_of(x: $Self, y: $Self) -> bool {
                if y == 0 {
                    x == 0 // 0 divides only 0
                } else {
                    x % y == 0
                }
            }
            // The following methods require additions to rust_primitives:
            // /// See [`std::primitive::u8::trailing_zeros`] (and similar for other integer types)
            // #[hax_lib::opaque]
            // fn trailing_zeros(x: $Self) -> core::primitive::u32 {
            //     paste! { [<trailing_zeros_ $Name>](x) }
            // }
            // /// See [`std::primitive::u8::swap_bytes`] (and similar for other integer types)
            // #[hax_lib::opaque]
            // fn swap_bytes(x: $Self) -> $Self {
            //     paste! { [<swap_bytes_ $Name>](x) }
            // }
            /// See [`std::primitive::u8::wrapping_neg`] (and similar for other integer types)
            // Modelled as `0.wrapping_sub(x)` (the definition of `wrapping_neg`)
            // to reuse the existing `wrapping_sub` primitive.
            pub fn wrapping_neg(x: $Self) -> $Self {
                paste! { [<wrapping_sub_ $Name>](0, x) }
            /// See [`std::primitive::u8::min_value`] (and similar for other integer types)
            pub fn min_value() -> $Self {
                <$Name>::MIN
            }
            /// See [`std::primitive::u8::max_value`] (and similar for other integer types)
            pub fn max_value() -> $Self {
                <$Name>::MAX
            }
            /// See [`std::primitive::u8::cast_signed`] (and similar for other unsigned integer types)
            pub fn cast_signed(x: $Self) -> $ISelf {
                x as $ISelf
            }
            /// See [`std::primitive::u8::count_zeros`] (and similar for other integer types)
            pub fn count_zeros(x: $Self) -> core::primitive::u32 {
                <$Name>::BITS - Self::count_ones(x)
            }
            /// See [`std::primitive::u8::checked_ilog2`] (and similar for other integer types)
            pub fn checked_ilog2(x: $Self) -> Option<core::primitive::u32> {
                if x == 0 {
                    Option::None
                } else {
                    Option::Some(Self::ilog2(x))
                }
            }
            /// See [`std::primitive::u8::wrapping_neg`] (and similar for other integer types)
            pub fn wrapping_neg(x: $Self) -> $Self {
                Self::wrapping_sub(0, x)
            }
            /// See [`std::primitive::u8::overflowing_neg`] (and similar for other integer types)
            pub fn overflowing_neg(x: $Self) -> ($Self, bool) {
                (Self::wrapping_neg(x), x != 0)
            }
            /// See [`std::primitive::u8::checked_neg`] (and similar for other integer types)
            pub fn checked_neg(x: $Self) -> Option<$Self> {
                if x == 0 {
                    Option::Some(0)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::u8::strict_neg`] (and similar for other integer types)
            #[hax_lib::requires(x == 0)]
            pub fn strict_neg(x: $Self) -> $Self {
                if x == 0 {
                    0
                } else {
                    crate::panicking::internal::panic()
                }
            }
            /// See [`std::primitive::u8::wrapping_pow`] (and similar for other integer types)
            pub fn wrapping_pow(x: $Self, exp: core::primitive::u32) -> $Self {
                let (result, _) = Self::overflowing_pow(x, exp);
                result
            }
            /// See [`std::primitive::u8::saturating_pow`] (and similar for other unsigned integer types)
            pub fn saturating_pow(x: $Self, exp: core::primitive::u32) -> $Self {
                let (result, overflowed) = Self::overflowing_pow(x, exp);
                if overflowed {
                    <$Name>::MAX
                } else {
                    result
                }
            }
            /// See [`std::primitive::u8::strict_pow`] (and similar for other integer types)
            #[hax_lib::requires(!<$Name>::overflowing_pow(x, exp).1)]
            pub fn strict_pow(x: $Self, exp: core::primitive::u32) -> $Self {
                let (result, overflowed) = Self::overflowing_pow(x, exp);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::u8::strict_add`] (and similar for other integer types)
            #[hax_lib::requires(x.to_int() + y.to_int() <= <$Name>::MAX.to_int())]
            pub fn strict_add(x: $Self, y: $Self) -> $Self {
                let (result, overflowed) = Self::overflowing_add(x, y);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::u8::strict_sub`] (and similar for other integer types)
            #[hax_lib::requires(x >= y)]
            pub fn strict_sub(x: $Self, y: $Self) -> $Self {
                let (result, overflowed) = Self::overflowing_sub(x, y);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::u8::strict_mul`] (and similar for other integer types)
            #[hax_lib::requires(x.to_int() * y.to_int() <= <$Name>::MAX.to_int())]
            pub fn strict_mul(x: $Self, y: $Self) -> $Self {
                let (result, overflowed) = Self::overflowing_mul(x, y);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::u8::wrapping_div`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn wrapping_div(x: $Self, y: $Self) -> $Self {
                x / y
            }
            /// See [`std::primitive::u8::wrapping_rem`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn wrapping_rem(x: $Self, y: $Self) -> $Self {
                x % y
            }
            /// See [`std::primitive::u8::wrapping_div_euclid`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn wrapping_div_euclid(x: $Self, y: $Self) -> $Self {
                x / y
            }
            /// See [`std::primitive::u8::wrapping_rem_euclid`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn wrapping_rem_euclid(x: $Self, y: $Self) -> $Self {
                x % y
            }
            /// See [`std::primitive::u8::saturating_div`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn saturating_div(x: $Self, y: $Self) -> $Self {
                x / y
            }
            /// See [`std::primitive::u8::strict_div`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn strict_div(x: $Self, y: $Self) -> $Self {
                x / y
            }
            /// See [`std::primitive::u8::strict_rem`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn strict_rem(x: $Self, y: $Self) -> $Self {
                x % y
            }
            /// See [`std::primitive::u8::strict_div_euclid`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn strict_div_euclid(x: $Self, y: $Self) -> $Self {
                x / y
            }
            /// See [`std::primitive::u8::strict_rem_euclid`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn strict_rem_euclid(x: $Self, y: $Self) -> $Self {
                x % y
            }
            /// See [`std::primitive::u8::div_euclid`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn div_euclid(x: $Self, y: $Self) -> $Self {
                x / y
            }
            /// See [`std::primitive::u8::div_floor`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn div_floor(x: $Self, y: $Self) -> $Self {
                x / y
            }
            /// See [`std::primitive::u8::overflowing_div`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn overflowing_div(x: $Self, y: $Self) -> ($Self, bool) {
                (x / y, false)
            }
            /// See [`std::primitive::u8::overflowing_rem`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn overflowing_rem(x: $Self, y: $Self) -> ($Self, bool) {
                (x % y, false)
            }
            /// See [`std::primitive::u8::overflowing_div_euclid`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn overflowing_div_euclid(x: $Self, y: $Self) -> ($Self, bool) {
                (x / y, false)
            }
            /// See [`std::primitive::u8::overflowing_rem_euclid`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn overflowing_rem_euclid(x: $Self, y: $Self) -> ($Self, bool) {
                (x % y, false)
            }
            /// See [`std::primitive::u8::checked_div_euclid`] (and similar for other unsigned integer types)
            pub fn checked_div_euclid(x: $Self, y: $Self) -> Option<$Self> {
                if y == 0 {
                    Option::None
                } else {
                    Option::Some(x / y)
                }
            }
            /// See [`std::primitive::u8::checked_rem_euclid`] (and similar for other unsigned integer types)
            pub fn checked_rem_euclid(x: $Self, y: $Self) -> Option<$Self> {
                if y == 0 {
                    Option::None
                } else {
                    Option::Some(x % y)
                }
            }
            /// See [`std::primitive::u8::div_exact`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0)]
            pub fn div_exact(x: $Self, y: $Self) -> Option<$Self> {
                if x % y != 0 {
                    Option::None
                } else {
                    Option::Some(x / y)
                }
            }
            /// See [`std::primitive::u8::checked_div_exact`] (and similar for other unsigned integer types)
            pub fn checked_div_exact(x: $Self, y: $Self) -> Option<$Self> {
                if y == 0 || x % y != 0 {
                    Option::None
                } else {
                    Option::Some(x / y)
                }
            }
            /// See [`std::primitive::u8::unchecked_div_exact`] (and similar for other unsigned integer types)
            #[hax_lib::requires(y != 0 && x % y == 0)]
            pub unsafe fn unchecked_div_exact(x: $Self, y: $Self) -> $Self {
                x / y
            }
            /// See [`std::primitive::u8::abs_diff`] (and similar for other unsigned integer types)
            pub fn abs_diff(x: $Self, y: $Self) -> $Self {
                if x < y {
                    y - x
                } else {
                    x - y
                }
            }
            /// See [`std::primitive::u8::midpoint`] (and similar for other unsigned integer types)
            pub fn midpoint(x: $Self, y: $Self) -> $Self {
                // Hacker's Delight's `((x ^ y) >> 1) + (x & y)`. The sum cannot
                // overflow, but showing that needs bit-level reasoning, so we spare
                // the backends the proof and use `wrapping_add`.
                Self::wrapping_add((x ^ y) >> 1, x & y)
            }
            /// See [`std::primitive::u8::next_multiple_of`] (and similar for other unsigned integer types)
            // `(y - x % y) % y` is `0` when `y` divides `x` and `y - x % y` otherwise,
            // which is what `core` selects with a `match`.
            #[hax_lib::requires(y != 0 && x.to_int() + ((y - x % y) % y).to_int() <= <$Name>::MAX.to_int())]
            pub fn next_multiple_of(x: $Self, y: $Self) -> $Self {
                x + (y - x % y) % y
            }
            /// See [`std::primitive::u8::checked_next_multiple_of`] (and similar for other unsigned integer types)
            pub fn checked_next_multiple_of(x: $Self, y: $Self) -> Option<$Self> {
                if y == 0 {
                    Option::None
                } else {
                    Self::checked_add(x, (y - x % y) % y)
                }
            }
            /// See [`std::primitive::u8::checked_signed_diff`] (and similar for other unsigned integer types)
            pub fn checked_signed_diff(x: $Self, y: $Self) -> Option<$ISelf> {
                let result = Self::wrapping_sub(x, y) as $ISelf;
                if (x >= y) == (result < 0) {
                    Option::None
                } else {
                    Option::Some(result)
                }
            }
            /// See [`std::primitive::u8::wrapping_add_signed`] (and similar for other unsigned integer types)
            pub fn wrapping_add_signed(x: $Self, y: $ISelf) -> $Self {
                Self::wrapping_add(x, y as $Self)
            }
            /// See [`std::primitive::u8::wrapping_sub_signed`] (and similar for other unsigned integer types)
            pub fn wrapping_sub_signed(x: $Self, y: $ISelf) -> $Self {
                Self::wrapping_sub(x, y as $Self)
            }
            /// See [`std::primitive::u8::overflowing_add_signed`] (and similar for other unsigned integer types)
            pub fn overflowing_add_signed(x: $Self, y: $ISelf) -> ($Self, bool) {
                let (result, overflowed) = Self::overflowing_add(x, y as $Self);
                (result, overflowed != (y < 0))
            }
            /// See [`std::primitive::u8::overflowing_sub_signed`] (and similar for other unsigned integer types)
            pub fn overflowing_sub_signed(x: $Self, y: $ISelf) -> ($Self, bool) {
                let (result, overflowed) = Self::overflowing_sub(x, y as $Self);
                (result, overflowed != (y < 0))
            }
            /// See [`std::primitive::u8::checked_add_signed`] (and similar for other unsigned integer types)
            pub fn checked_add_signed(x: $Self, y: $ISelf) -> Option<$Self> {
                let (result, overflowed) = Self::overflowing_add_signed(x, y);
                if overflowed {
                    Option::None
                } else {
                    Option::Some(result)
                }
            }
            /// See [`std::primitive::u8::checked_sub_signed`] (and similar for other unsigned integer types)
            pub fn checked_sub_signed(x: $Self, y: $ISelf) -> Option<$Self> {
                let (result, overflowed) = Self::overflowing_sub_signed(x, y);
                if overflowed {
                    Option::None
                } else {
                    Option::Some(result)
                }
            }
            /// See [`std::primitive::u8::saturating_add_signed`] (and similar for other unsigned integer types)
            pub fn saturating_add_signed(x: $Self, y: $ISelf) -> $Self {
                let (result, overflowed) = Self::overflowing_add_signed(x, y);
                if !overflowed {
                    result
                } else if y < 0 {
                    <$Name>::MIN
                } else {
                    <$Name>::MAX
                }
            }
            /// See [`std::primitive::u8::saturating_sub_signed`] (and similar for other unsigned integer types)
            pub fn saturating_sub_signed(x: $Self, y: $ISelf) -> $Self {
                let (result, overflowed) = Self::overflowing_sub_signed(x, y);
                if !overflowed {
                    result
                } else if y < 0 {
                    <$Name>::MAX
                } else {
                    <$Name>::MIN
                }
            }
            /// See [`std::primitive::u8::strict_add_signed`] (and similar for other unsigned integer types)
            #[hax_lib::requires(x.to_int() + y.to_int() >= <$Name>::MIN.to_int() && x.to_int() + y.to_int() <= <$Name>::MAX.to_int())]
            pub fn strict_add_signed(x: $Self, y: $ISelf) -> $Self {
                let (result, overflowed) = Self::overflowing_add_signed(x, y);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::u8::strict_sub_signed`] (and similar for other unsigned integer types)
            #[hax_lib::requires(x.to_int() - y.to_int() >= <$Name>::MIN.to_int() && x.to_int() - y.to_int() <= <$Name>::MAX.to_int())]
            pub fn strict_sub_signed(x: $Self, y: $ISelf) -> $Self {
                let (result, overflowed) = Self::overflowing_sub_signed(x, y);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
        }
    };
}

use hax_lib::int::ToInt;

macro_rules! iint_impl {
    (
        $Self: ty,
        $USelf: ty,
        $Name: ty,
        $Max: expr,
        $Min: expr,
        $Bits: expr,
        $Bytes: expr,
    ) => {
        #[hax_lib::attributes]
        impl $Name {
            /// See [`std::primitive::i8::MIN`] (and similar for other signed integer types)
            pub const MIN: $Self = $Min;
            /// See [`std::primitive::i8::MAX`] (and similar for other signed integer types)
            pub const MAX: $Self = $Max;
            /// See [`std::primitive::i8::BITS`] (and similar for other signed integer types)
            pub const BITS: core::primitive::u32 = $Bits;
            pub fn wrapping_add(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_add_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
            pub fn saturating_add(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_add_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
            pub fn overflowing_add(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_add_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
            pub fn checked_add(x: $Self, y: $Self) -> Option<$Self> {
                let (result, overflowed) = Self::overflowing_add(x, y);
                if overflowed {
                    Option::None
                } else {
                    Option::Some(result)
                }
            }
            /// See [`std::primitive::u8::unchecked_add`] (and similar for other integer types)
            #[hax_lib::requires(x.to_int() + y.to_int() <= <$Name>::MAX.to_int() && x.to_int() + y.to_int() >= <$Name>::MIN.to_int())]
            pub unsafe fn unchecked_add(x: $Self, y: $Self) -> $Self {
                x + y
            }
            /// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
            pub fn wrapping_sub(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_sub_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
            pub fn saturating_sub(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_sub_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
            pub fn overflowing_sub(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_sub_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
            pub fn checked_sub(x: $Self, y: $Self) -> Option<$Self> {
                let (result, overflowed) = Self::overflowing_sub(x, y);
                if overflowed {
                    Option::None
                } else {
                    Option::Some(result)
                }
            }
            /// See [`std::primitive::u8::unchecked_sub`] (and similar for other integer types)
            #[hax_lib::requires(x.to_int() - y.to_int() <= <$Name>::MAX.to_int() && x.to_int() - y.to_int() >= <$Name>::MIN.to_int())]
            pub unsafe fn unchecked_sub(x: $Self, y: $Self) -> $Self {
                x - y
            }
            /// See [`std::primitive::i8::checked_add_unsigned`] (and similar for other signed integer types)
            pub fn checked_add_unsigned(x: $Self, y: $USelf) -> Option<$Self> {
                // Signed overflow from wrapping_add(x, y as $Self) represents unsigned overflow
                // iff the signed overflow flag matches whether y exceeds the signed maximum.
                let (result, overflowed) = Self::overflowing_add(x, y as $Self);
                if overflowed == (y > <$Name>::MAX as $USelf) {
                    Option::Some(result)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::i8::checked_sub_unsigned`] (and similar for other signed integer types)
            pub fn checked_sub_unsigned(x: $Self, y: $USelf) -> Option<$Self> {
                let (result, overflowed) = Self::overflowing_sub(x, y as $Self);
                if overflowed == (y > <$Name>::MAX as $USelf) {
                    Option::Some(result)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
            pub fn wrapping_mul(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_mul_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
            pub fn saturating_mul(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_mul_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
            pub fn overflowing_mul(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_mul_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
            pub fn checked_mul(x: $Self, y: $Self) -> Option<$Self> {
                let (result, overflowed) = Self::overflowing_mul(x, y);
                if overflowed {
                    Option::None
                } else {
                    Option::Some(result)
                }
            }
            /// See [`std::primitive::u8::unchecked_mul`] (and similar for other integer types)
            #[hax_lib::requires(x.to_int() * y.to_int() <= <$Name>::MAX.to_int() && x.to_int() * y.to_int() >= <$Name>::MIN.to_int())]
            pub unsafe fn unchecked_mul(x: $Self, y: $Self) -> $Self {
                x * y
            }
            /// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
            // `MIN % -1` overflows, like `MIN / -1`.
            #[hax_lib::requires(y != 0 && !(x == <$Name>::MIN && y == -1))]
            pub fn rem_euclid(x: $Self, y: $Self) -> $Self {
                paste! { [<rem_euclid_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::pow`] (and similar for other integer types)
            pub fn pow(x: $Self, exp: core::primitive::u32) -> $Self {
                paste! { [<pow_ $Name>](x, exp) }
            }
            /// See [`std::primitive::u8::overflowing_pow`] (and similar for other integer types)
            pub fn overflowing_pow(x: $Self, exp: core::primitive::u32) -> ($Self, bool) {
                paste! { [<overflowing_pow_ $Name>](x, exp) }
            }
            /// See [`std::primitive::u8::checked_pow`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::exclude)] //avoid cyclic dependency
            pub fn checked_pow(x: $Self, exp: core::primitive::u32) -> Option<$Self> {
                let (result, overflowed) = Self::overflowing_pow(x, exp);
                if overflowed {
                    Option::None
                } else {
                    Option::Some(result)
                }
            }
            /// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
            pub fn count_ones(x: $Self) -> core::primitive::u32 {
                paste! { [<count_ones_ $Name>](x) }
            }
            /// See [`std::primitive::i8::abs`] (and similar for other signed integer types)
            #[hax_lib::requires(x > <$Name>::MIN)]
            pub fn abs(x: $Self) -> $Self {
                paste! { [<abs_ $Name>](x) }
            }
            /// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn rotate_right(x: $Self, n: core::primitive::u32) -> $Self {
                paste! { [<rotate_right_ $Name>](x, n) }
            }
            /// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn rotate_left(x: $Self, n: core::primitive::u32) -> $Self {
                paste! { [<rotate_left_ $Name>](x, n) }
            }
            /// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn leading_zeros(x: $Self) -> core::primitive::u32 {
                paste! { [<leading_zeros_ $Name>](x) }
            }
            /// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn ilog2(x: $Self) -> core::primitive::u32 {
                paste! { [<ilog2_ $Name>](x) }
            }
            /// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
            #[hax_lib::opaque]
            pub fn from_str_radix(
                src: &str,
                radix: core::primitive::u32,
            ) -> Result<$Self, error::ParseIntError> {
                let (parsed, value) = paste! { [<from_str_radix_ $Name>](src, radix) };
                if parsed {
                    Result::Ok(value)
                } else {
                    // The model's `ParseIntError` carries no distinguishable kind.
                    Result::Err(error::ParseIntError {
                        kind: error::IntErrorKind,
                    })
                }
            }
            /// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn from_be_bytes(bytes: [core::primitive::u8; $Bytes]) -> $Self {
                paste! { [<from_be_bytes_ $Name>](bytes) }
            }
            /// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn from_le_bytes(bytes: [core::primitive::u8; $Bytes]) -> $Self {
                paste! { [<from_le_bytes_ $Name>](bytes) }
            }
            /// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn to_be_bytes(bytes: $Self) -> [core::primitive::u8; $Bytes] {
                paste! { [<to_be_bytes_ $Name>](bytes) }
            }
            /// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn to_le_bytes(bytes: $Self) -> [core::primitive::u8; $Bytes] {
                paste! { [<to_le_bytes_ $Name>](bytes) }
            }
            /// See [`std::primitive::i8::checked_div`] (and similar for other signed integer types)
            pub fn checked_div(x: $Self, y: $Self) -> Option<$Self> {
                if y == 0 || (x == <$Name>::MIN && y == -1) {
                    Option::None
                } else {
                    Option::Some(x / y)
                }
            }
            /// See [`std::primitive::u8::unchecked_div`] (and similar for other integer types)
            #[hax_lib::requires(y != 0 && (x != <$Name>::MIN || y != -1))]
            pub unsafe fn unchecked_div(x: $Self, y: $Self) -> $Self {
                x / y
            }
            /// See [`std::primitive::i8::checked_rem`] (and similar for other signed integer types)
            pub fn checked_rem(x: $Self, y: $Self) -> Option<$Self> {
                if y == 0 || (x == <$Name>::MIN && y == -1) {
                    Option::None
                } else {
                    Option::Some(x % y)
                }
            }
            /// See [`std::primitive::u8::unchecked_rem`] (and similar for other integer types)
            #[hax_lib::requires(y != 0 && (x != <$Name>::MIN || y != -1))]
            pub unsafe fn unchecked_rem(x: $Self, y: $Self) -> $Self {
                x % y
            }
            /// See [`std::primitive::i8::signum`] (and similar for other signed integer types)
            pub fn signum(x: $Self) -> $Self {
                if x > 0 {
                    1
                } else if x == 0 {
                    0
                } else {
                    -1
                }
            }
            /// See [`std::primitive::i8::div_ceil`] (and similar for other signed integer types)
            // `requires` rules out the div-by-zero and `MIN / -1` panics.
            #[hax_lib::requires(y != 0 && !(x == <$Name>::MIN && y == -1))]
            pub fn div_ceil(x: $Self, y: $Self) -> $Self {
                let d = x / y;
                let r = x % y;
                // round up only when the remainder shares the divisor's sign
                if (r > 0 && y > 0) || (r < 0 && y < 0) {
                    d + 1
                } else {
                    d
                }
            }
            // The following methods require additions to rust_primitives:
            // /// See [`std::primitive::i8::trailing_zeros`] (and similar for other signed integer types)
            // #[hax_lib::opaque]
            // fn trailing_zeros(x: $Self) -> core::primitive::u32 {
            //     paste! { [<trailing_zeros_ $Name>](x) }
            // }
            // /// See [`std::primitive::i8::swap_bytes`] (and similar for other signed integer types)
            // #[hax_lib::opaque]
            // fn swap_bytes(x: $Self) -> $Self {
            //     paste! { [<swap_bytes_ $Name>](x) }
            // }
            /// See [`std::primitive::i8::wrapping_neg`] (and similar for other signed integer types)
            // Modelled as `0.wrapping_sub(x)` (the definition of `wrapping_neg`)
            // to reuse the existing `wrapping_sub` primitive.
            pub fn wrapping_neg(x: $Self) -> $Self {
                paste! { [<wrapping_sub_ $Name>](0, x) }
            /// See [`std::primitive::i8::min_value`] (and similar for other integer types)
            pub fn min_value() -> $Self {
                <$Name>::MIN
            }
            /// See [`std::primitive::i8::max_value`] (and similar for other integer types)
            pub fn max_value() -> $Self {
                <$Name>::MAX
            }
            /// See [`std::primitive::i8::cast_unsigned`] (and similar for other signed integer types)
            pub fn cast_unsigned(x: $Self) -> $USelf {
                x as $USelf
            }
            /// See [`std::primitive::i8::is_positive`] (and similar for other signed integer types)
            pub fn is_positive(x: $Self) -> bool {
                x > 0
            }
            /// See [`std::primitive::i8::is_negative`] (and similar for other signed integer types)
            pub fn is_negative(x: $Self) -> bool {
                x < 0
            }
            /// See [`std::primitive::i8::count_zeros`] (and similar for other integer types)
            pub fn count_zeros(x: $Self) -> core::primitive::u32 {
                <$Name>::BITS - Self::count_ones(x)
            }
            /// See [`std::primitive::i8::checked_ilog2`] (and similar for other integer types)
            pub fn checked_ilog2(x: $Self) -> Option<core::primitive::u32> {
                if x <= 0 {
                    Option::None
                } else {
                    Option::Some(Self::ilog2(x))
                }
            }
            /// See [`std::primitive::i8::wrapping_neg`] (and similar for other integer types)
            pub fn wrapping_neg(x: $Self) -> $Self {
                Self::wrapping_sub(0, x)
            }
            /// See [`std::primitive::i8::overflowing_neg`] (and similar for other integer types)
            pub fn overflowing_neg(x: $Self) -> ($Self, bool) {
                if x == <$Name>::MIN {
                    (<$Name>::MIN, true)
                } else {
                    (Self::wrapping_neg(x), false)
                }
            }
            /// See [`std::primitive::i8::checked_neg`] (and similar for other integer types)
            pub fn checked_neg(x: $Self) -> Option<$Self> {
                if x == <$Name>::MIN {
                    Option::None
                } else {
                    Option::Some(Self::wrapping_neg(x))
                }
            }
            /// See [`std::primitive::i8::saturating_neg`] (and similar for other signed integer types)
            pub fn saturating_neg(x: $Self) -> $Self {
                if x == <$Name>::MIN {
                    <$Name>::MAX
                } else {
                    Self::wrapping_neg(x)
                }
            }
            /// See [`std::primitive::i8::strict_neg`] (and similar for other integer types)
            #[hax_lib::requires(x != <$Name>::MIN)]
            pub fn strict_neg(x: $Self) -> $Self {
                if x == <$Name>::MIN {
                    crate::panicking::internal::panic()
                } else {
                    Self::wrapping_neg(x)
                }
            }
            /// See [`std::primitive::i8::unchecked_neg`] (and similar for other signed integer types)
            #[hax_lib::requires(x != <$Name>::MIN)]
            pub unsafe fn unchecked_neg(x: $Self) -> $Self {
                0 - x
            }
            /// See [`std::primitive::i8::wrapping_abs`] (and similar for other signed integer types)
            pub fn wrapping_abs(x: $Self) -> $Self {
                if x < 0 {
                    Self::wrapping_neg(x)
                } else {
                    x
                }
            }
            /// See [`std::primitive::i8::overflowing_abs`] (and similar for other signed integer types)
            pub fn overflowing_abs(x: $Self) -> ($Self, bool) {
                (Self::wrapping_abs(x), x == <$Name>::MIN)
            }
            /// See [`std::primitive::i8::checked_abs`] (and similar for other signed integer types)
            pub fn checked_abs(x: $Self) -> Option<$Self> {
                if x < 0 {
                    Self::checked_neg(x)
                } else {
                    Option::Some(x)
                }
            }
            /// See [`std::primitive::i8::saturating_abs`] (and similar for other signed integer types)
            pub fn saturating_abs(x: $Self) -> $Self {
                if x < 0 {
                    Self::saturating_neg(x)
                } else {
                    x
                }
            }
            /// See [`std::primitive::i8::strict_abs`] (and similar for other signed integer types)
            #[hax_lib::requires(x != <$Name>::MIN)]
            pub fn strict_abs(x: $Self) -> $Self {
                if x < 0 {
                    Self::strict_neg(x)
                } else {
                    x
                }
            }
            /// See [`std::primitive::i8::unsigned_abs`] (and similar for other signed integer types)
            pub fn unsigned_abs(x: $Self) -> $USelf {
                Self::wrapping_abs(x) as $USelf
            }
            /// See [`std::primitive::i8::wrapping_pow`] (and similar for other integer types)
            pub fn wrapping_pow(x: $Self, exp: core::primitive::u32) -> $Self {
                let (result, _) = Self::overflowing_pow(x, exp);
                result
            }
            /// See [`std::primitive::i8::saturating_pow`] (and similar for other signed integer types)
            pub fn saturating_pow(x: $Self, exp: core::primitive::u32) -> $Self {
                let (result, overflowed) = Self::overflowing_pow(x, exp);
                if !overflowed {
                    result
                } else if x < 0 && exp % 2 == 1 {
                    <$Name>::MIN
                } else {
                    <$Name>::MAX
                }
            }
            /// See [`std::primitive::i8::strict_pow`] (and similar for other integer types)
            #[hax_lib::requires(!<$Name>::overflowing_pow(x, exp).1)]
            pub fn strict_pow(x: $Self, exp: core::primitive::u32) -> $Self {
                let (result, overflowed) = Self::overflowing_pow(x, exp);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::i8::strict_add`] (and similar for other integer types)
            #[hax_lib::requires(x.to_int() + y.to_int() <= <$Name>::MAX.to_int() && x.to_int() + y.to_int() >= <$Name>::MIN.to_int())]
            pub fn strict_add(x: $Self, y: $Self) -> $Self {
                let (result, overflowed) = Self::overflowing_add(x, y);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::i8::strict_sub`] (and similar for other integer types)
            #[hax_lib::requires(x.to_int() - y.to_int() <= <$Name>::MAX.to_int() && x.to_int() - y.to_int() >= <$Name>::MIN.to_int())]
            pub fn strict_sub(x: $Self, y: $Self) -> $Self {
                let (result, overflowed) = Self::overflowing_sub(x, y);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::i8::strict_mul`] (and similar for other integer types)
            #[hax_lib::requires(x.to_int() * y.to_int() <= <$Name>::MAX.to_int() && x.to_int() * y.to_int() >= <$Name>::MIN.to_int())]
            pub fn strict_mul(x: $Self, y: $Self) -> $Self {
                let (result, overflowed) = Self::overflowing_mul(x, y);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::i8::overflowing_div`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0)]
            pub fn overflowing_div(x: $Self, y: $Self) -> ($Self, bool) {
                if x == <$Name>::MIN && y == -1 {
                    (x, true)
                } else {
                    (x / y, false)
                }
            }
            /// See [`std::primitive::i8::overflowing_rem`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0)]
            pub fn overflowing_rem(x: $Self, y: $Self) -> ($Self, bool) {
                if y == -1 {
                    (0, x == <$Name>::MIN)
                } else {
                    (x % y, false)
                }
            }
            /// See [`std::primitive::i8::wrapping_div`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0)]
            pub fn wrapping_div(x: $Self, y: $Self) -> $Self {
                let (result, _) = Self::overflowing_div(x, y);
                result
            }
            /// See [`std::primitive::i8::wrapping_rem`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0)]
            pub fn wrapping_rem(x: $Self, y: $Self) -> $Self {
                let (result, _) = Self::overflowing_rem(x, y);
                result
            }
            /// See [`std::primitive::i8::saturating_div`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0)]
            pub fn saturating_div(x: $Self, y: $Self) -> $Self {
                let (result, overflowed) = Self::overflowing_div(x, y);
                if overflowed {
                    <$Name>::MAX
                } else {
                    result
                }
            }
            /// See [`std::primitive::i8::strict_div`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0 && !(x == <$Name>::MIN && y == -1))]
            pub fn strict_div(x: $Self, y: $Self) -> $Self {
                let (result, overflowed) = Self::overflowing_div(x, y);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::i8::strict_rem`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0 && !(x == <$Name>::MIN && y == -1))]
            pub fn strict_rem(x: $Self, y: $Self) -> $Self {
                let (result, overflowed) = Self::overflowing_rem(x, y);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::i8::div_euclid`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0 && !(x == <$Name>::MIN && y == -1))]
            pub fn div_euclid(x: $Self, y: $Self) -> $Self {
                let q = x / y;
                if x % y < 0 {
                    // `q` is not at a bound here, but proving it needs case analysis;
                    // the wrapping forms spare the backends the proof.
                    if y > 0 {
                        Self::wrapping_sub(q, 1)
                    } else {
                        Self::wrapping_add(q, 1)
                    }
                } else {
                    q
                }
            }
            /// See [`std::primitive::i8::overflowing_div_euclid`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0)]
            pub fn overflowing_div_euclid(x: $Self, y: $Self) -> ($Self, bool) {
                if x == <$Name>::MIN && y == -1 {
                    (x, true)
                } else {
                    (Self::div_euclid(x, y), false)
                }
            }
            /// See [`std::primitive::i8::wrapping_div_euclid`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0)]
            pub fn wrapping_div_euclid(x: $Self, y: $Self) -> $Self {
                let (result, _) = Self::overflowing_div_euclid(x, y);
                result
            }
            /// See [`std::primitive::i8::checked_div_euclid`] (and similar for other signed integer types)
            pub fn checked_div_euclid(x: $Self, y: $Self) -> Option<$Self> {
                if y == 0 || (x == <$Name>::MIN && y == -1) {
                    Option::None
                } else {
                    Option::Some(Self::div_euclid(x, y))
                }
            }
            /// See [`std::primitive::i8::strict_div_euclid`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0 && !(x == <$Name>::MIN && y == -1))]
            pub fn strict_div_euclid(x: $Self, y: $Self) -> $Self {
                let (result, overflowed) = Self::overflowing_div_euclid(x, y);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::i8::overflowing_rem_euclid`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0)]
            pub fn overflowing_rem_euclid(x: $Self, y: $Self) -> ($Self, bool) {
                if y == -1 {
                    (0, x == <$Name>::MIN)
                } else {
                    (Self::rem_euclid(x, y), false)
                }
            }
            /// See [`std::primitive::i8::wrapping_rem_euclid`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0)]
            pub fn wrapping_rem_euclid(x: $Self, y: $Self) -> $Self {
                let (result, _) = Self::overflowing_rem_euclid(x, y);
                result
            }
            /// See [`std::primitive::i8::checked_rem_euclid`] (and similar for other signed integer types)
            pub fn checked_rem_euclid(x: $Self, y: $Self) -> Option<$Self> {
                if y == 0 || (x == <$Name>::MIN && y == -1) {
                    Option::None
                } else {
                    Option::Some(Self::rem_euclid(x, y))
                }
            }
            /// See [`std::primitive::i8::strict_rem_euclid`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0 && !(x == <$Name>::MIN && y == -1))]
            pub fn strict_rem_euclid(x: $Self, y: $Self) -> $Self {
                let (result, overflowed) = Self::overflowing_rem_euclid(x, y);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::i8::div_floor`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0 && !(x == <$Name>::MIN && y == -1))]
            pub fn div_floor(x: $Self, y: $Self) -> $Self {
                let d = x / y;
                let r = x % y;
                // Truncating division rounds towards zero, so it rounded up exactly when
                // the operands have opposite signs and the division was inexact.
                if r != 0 && ((x < 0) != (y < 0)) {
                    Self::wrapping_sub(d, 1)
                } else {
                    d
                }
            }
            /// See [`std::primitive::i8::div_exact`] (and similar for other signed integer types)
            #[hax_lib::requires(y != 0 && !(x == <$Name>::MIN && y == -1))]
            pub fn div_exact(x: $Self, y: $Self) -> Option<$Self> {
                if x % y != 0 {
                    Option::None
                } else {
                    Option::Some(x / y)
                }
            }
            /// See [`std::primitive::i8::checked_div_exact`] (and similar for other signed integer types)
            pub fn checked_div_exact(x: $Self, y: $Self) -> Option<$Self> {
                if y == 0 || (x == <$Name>::MIN && y == -1) || x % y != 0 {
                    Option::None
                } else {
                    Option::Some(x / y)
                }
            }
            /// See [`std::primitive::i8::unchecked_div_exact`] (and similar for other signed integer types)
            // `core` documents the precondition as `y > 0`, which also rules out the
            // `MIN / -1` overflow.
            #[hax_lib::requires(y > 0 && x % y == 0)]
            pub unsafe fn unchecked_div_exact(x: $Self, y: $Self) -> $Self {
                x / y
            }
            /// See [`std::primitive::i8::abs_diff`] (and similar for other signed integer types)
            pub fn abs_diff(x: $Self, y: $Self) -> $USelf {
                // The signed difference wraps, but reinterpreting the result as unsigned
                // gives the (always representable) absolute difference.
                if x < y {
                    Self::wrapping_sub(y, x) as $USelf
                } else {
                    Self::wrapping_sub(x, y) as $USelf
                }
            }
            /// See [`std::primitive::i8::midpoint`] (and similar for other signed integer types)
            pub fn midpoint(x: $Self, y: $Self) -> $Self {
                // Hacker's Delight's `((x ^ y) >> 1) + (x & y)`, plus `core`'s correction
                // for sums that are odd and negative. Neither addition can overflow, but
                // showing that needs bit-level reasoning, so we use the wrapping forms.
                let d = x ^ y;
                let t = Self::wrapping_add(d >> 1, x & y);
                if t < 0 {
                    Self::wrapping_add(t, d & 1)
                } else {
                    t
                }
            }
            /// See [`std::primitive::i8::checked_next_multiple_of`] (and similar for other signed integer types)
            pub fn checked_next_multiple_of(x: $Self, y: $Self) -> Option<$Self> {
                if y == -1 {
                    // `x % -1` overflows at `MIN`, and every integer is a multiple of -1.
                    Option::Some(x)
                } else if y == 0 {
                    Option::None
                } else {
                    let r = x % y;
                    // `r + y` has operands of opposite signs and `y - m` operands of the
                    // same sign, so neither overflows; the wrapping forms spare the
                    // backends the proof.
                    let m = if (r > 0 && y < 0) || (r < 0 && y > 0) {
                        Self::wrapping_add(r, y)
                    } else {
                        r
                    };
                    if m == 0 {
                        Option::Some(x)
                    } else {
                        Self::checked_add(x, Self::wrapping_sub(y, m))
                    }
                }
            }
            /// See [`std::primitive::i8::wrapping_add_unsigned`] (and similar for other signed integer types)
            pub fn wrapping_add_unsigned(x: $Self, y: $USelf) -> $Self {
                Self::wrapping_add(x, y as $Self)
            }
            /// See [`std::primitive::i8::wrapping_sub_unsigned`] (and similar for other signed integer types)
            pub fn wrapping_sub_unsigned(x: $Self, y: $USelf) -> $Self {
                Self::wrapping_sub(x, y as $Self)
            }
            /// See [`std::primitive::i8::overflowing_add_unsigned`] (and similar for other signed integer types)
            pub fn overflowing_add_unsigned(x: $Self, y: $USelf) -> ($Self, bool) {
                let rhs = y as $Self;
                let (result, overflowed) = Self::overflowing_add(x, rhs);
                (result, overflowed != (rhs < 0))
            }
            /// See [`std::primitive::i8::overflowing_sub_unsigned`] (and similar for other signed integer types)
            pub fn overflowing_sub_unsigned(x: $Self, y: $USelf) -> ($Self, bool) {
                let rhs = y as $Self;
                let (result, overflowed) = Self::overflowing_sub(x, rhs);
                (result, overflowed != (rhs < 0))
            }
            /// See [`std::primitive::i8::saturating_add_unsigned`] (and similar for other signed integer types)
            pub fn saturating_add_unsigned(x: $Self, y: $USelf) -> $Self {
                // Adding a non-negative value can only overflow at the upper bound.
                let (result, overflowed) = Self::overflowing_add_unsigned(x, y);
                if overflowed {
                    <$Name>::MAX
                } else {
                    result
                }
            }
            /// See [`std::primitive::i8::saturating_sub_unsigned`] (and similar for other signed integer types)
            pub fn saturating_sub_unsigned(x: $Self, y: $USelf) -> $Self {
                // Subtracting a non-negative value can only overflow at the lower bound.
                let (result, overflowed) = Self::overflowing_sub_unsigned(x, y);
                if overflowed {
                    <$Name>::MIN
                } else {
                    result
                }
            }
            /// See [`std::primitive::i8::strict_add_unsigned`] (and similar for other signed integer types)
            #[hax_lib::requires(x.to_int() + y.to_int() <= <$Name>::MAX.to_int())]
            pub fn strict_add_unsigned(x: $Self, y: $USelf) -> $Self {
                let (result, overflowed) = Self::overflowing_add_unsigned(x, y);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::i8::strict_sub_unsigned`] (and similar for other signed integer types)
            #[hax_lib::requires(x.to_int() - y.to_int() >= <$Name>::MIN.to_int())]
            pub fn strict_sub_unsigned(x: $Self, y: $USelf) -> $Self {
                let (result, overflowed) = Self::overflowing_sub_unsigned(x, y);
                if overflowed {
                    crate::panicking::internal::panic()
                } else {
                    result
                }
            }
            /// See [`std::primitive::i8::clamp_magnitude`] (and similar for other signed integer types)
            pub fn clamp_magnitude(x: $Self, limit: $USelf) -> $Self {
                if limit > <$Name>::MAX as $USelf {
                    // No `$Self` is out of range, so there is nothing to clamp.
                    x
                } else {
                    let hi = limit as $Self;
                    let lo = Self::wrapping_neg(hi);
                    if x < lo {
                        lo
                    } else if x > hi {
                        hi
                    } else {
                        x
                    }
                }
            }
        }
    };
}

// These types are a trick to define impls on the right names as
// it is forbidden to do it on primitive types
/// See [`std::primitive::u8`]
// F*-only: `charon::exclude` would drop these dummy types while their `impl`
// blocks still reference them (see f32.rs).
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub struct u8;
/// See [`std::primitive::u16`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub struct u16;
/// See [`std::primitive::u32`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub struct u32;
/// See [`std::primitive::u64`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub struct u64;
/// See [`std::primitive::u128`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub struct u128;
/// See [`std::primitive::usize`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub struct usize;
/// See [`std::primitive::i8`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub struct i8;
/// See [`std::primitive::i16`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub struct i16;
/// See [`std::primitive::i32`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub struct i32;
/// See [`std::primitive::i64`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub struct i64;
/// See [`std::primitive::i128`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub struct i128;
/// See [`std::primitive::isize`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub struct isize;

// Placeholders to get the same impl numbering as in core:
#[hax_lib::attributes]
impl i8 {}
#[hax_lib::attributes]
impl i16 {}
#[hax_lib::attributes]
impl i32 {}
#[hax_lib::attributes]
impl i64 {}
#[hax_lib::attributes]
impl i128 {}
#[hax_lib::attributes]
impl isize {}

uint_impl! {
    core::primitive::u8,
    core::primitive::i8,
    u8,
    255,
    8,
    1,
}

uint_impl! {
    core::primitive::u16,
    core::primitive::i16,
    u16,
    65535,
    16,
    2,
}

uint_impl! {
    core::primitive::u32,
    core::primitive::i32,
    u32,
    4294967295,
    32,
    4,
}

uint_impl! {
    core::primitive::u64,
    core::primitive::i64,
    u64,
    18446744073709551615,
    64,
    8,
}

uint_impl! {
    core::primitive::u128,
    core::primitive::i128,
    u128,
    340282366920938463463374607431768211455,
    128,
    16,
}

uint_impl! {
    core::primitive::usize,
    core::primitive::isize,
    usize,
    USIZE_MAX,
    SIZE_BITS,
    SIZE_BYTES,
}

iint_impl! {
    core::primitive::i8,
    core::primitive::u8,
    i8,
    127,
    -128,
    8,
    1,
}

iint_impl! {
    core::primitive::i16,
    core::primitive::u16,
    i16,
    32767,
    -32768,
    16,
    2,
}

iint_impl! {
    core::primitive::i32,
    core::primitive::u32,
    i32,
    2147483647,
    -2147483648,
    32,
    4,
}

iint_impl! {
    core::primitive::i64,
    core::primitive::u64,
    i64,
    9223372036854775807,
    -9223372036854775808,
    64,
    8,
}

iint_impl! {
    core::primitive::i128,
    core::primitive::u128,
    i128,
    170141183460469231731687303715884105727,
    -170141183460469231731687303715884105728,
    128,
    16,
}

iint_impl! {
    core::primitive::isize,
    core::primitive::usize,
    isize,
    ISIZE_MAX,
    ISIZE_MIN,
    SIZE_BITS,
    SIZE_BYTES,
}

macro_rules! impl_default_for_int {
    ($($t:ty),*) => {
        $(
            #[hax_lib::attributes]
            impl crate::default::Default for $t {
                fn default() -> $t {
                    0
                }
            }
        )*
    };
}

impl_default_for_int!(
    core::primitive::u8,
    core::primitive::u16,
    core::primitive::u32,
    core::primitive::u64,
    core::primitive::u128,
    core::primitive::usize,
    core::primitive::i8,
    core::primitive::i16,
    core::primitive::i32,
    core::primitive::i64,
    core::primitive::i128,
    core::primitive::isize
);

#[hax_lib::attributes]
impl crate::default::Default for bool {
    /// See [`std::default::Default`]
    fn default() -> bool {
        false
    }
}

#[cfg(test)]
mod tests {
    use crate::testing::Inject;
    use pastey::paste;
    use proptest::prelude::*;

    macro_rules! int_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $t _min>]() {
                        assert_eq!(super::$t::MIN, $t::MIN)
                    }
                    #[test]
                    fn [<test_ $t _max>]() {
                        assert_eq!(super::$t::MAX, $t::MAX)
                    }
                    #[test]
                    fn [<test_ $t _bits>]() {
                        assert_eq!(super::$t::BITS, $t::BITS)
                    }
                    proptest! {
                        #[test]
                        fn [<test_ $t _wrapping_add>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::wrapping_add(x.inject(), y.inject()), x.wrapping_add(y));
                        }

                        #[test]
                        fn [<test_ $t _saturating_add>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::saturating_add(x.inject(), y.inject()), x.saturating_add(y));
                        }

                        #[test]
                        fn [<test_ $t _overflowing_add>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::overflowing_add(x.inject(), y.inject()), x.overflowing_add(y));
                        }

                        #[test]
                        fn [<test_ $t _checked_add>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::checked_add(x.inject(), y.inject()), x.checked_add(y).inject());
                        }

                        #[test]
                        fn [<test_ $t _checked_sub>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::checked_sub(x.inject(), y.inject()), x.checked_sub(y).inject());
                        }

                        #[test]
                        fn [<test_ $t _checked_mul>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::checked_mul(x.inject(), y.inject()), x.checked_mul(y).inject());
                        }

                        #[test]
                        fn [<test_ $t _overflowing_pow>](x in any::<$t>(), exp in 0u32..=140) {
                            prop_assert_eq!(super::$t::overflowing_pow(x.inject(), exp), x.overflowing_pow(exp));
                        }

                        #[test]
                        fn [<test_ $t _checked_pow>](x in any::<$t>(), exp in 0u32..=140) {
                            prop_assert_eq!(super::$t::checked_pow(x.inject(), exp), x.checked_pow(exp).inject());
                        }

                        #[test]
                        fn [<test_ $t _wrapping_sub>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::wrapping_sub(x.inject(), y.inject()), x.wrapping_sub(y));
                        }

                        #[test]
                        fn [<test_ $t _wrapping_neg>](x in any::<$t>()) {
                            prop_assert_eq!(super::$t::wrapping_neg(x.inject()), x.wrapping_neg());
                        }

                        #[test]
                        fn [<test_ $t _saturating_sub>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::saturating_sub(x.inject(), y.inject()), x.saturating_sub(y));
                        }

                        #[test]
                        fn [<test_ $t _overflowing_sub>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::overflowing_sub(x.inject(), y.inject()), x.overflowing_sub(y));
                        }

                        #[test]
                        fn [<test_ $t _wrapping_mul>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::wrapping_mul(x.inject(), y.inject()), x.wrapping_mul(y));
                        }

                        #[test]
                        fn [<test_ $t _saturating_mul>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::saturating_mul(x.inject(), y.inject()), x.saturating_mul(y));
                        }

                        #[test]
                        fn [<test_ $t _overflowing_mul>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::overflowing_mul(x.inject(), y.inject()), x.overflowing_mul(y));
                        }

                        // `checked_rem_euclid`, not `y != 0`: signed `MIN % -1`
                        // overflows too, and both sides panic on it.
                        #[test]
                        fn [<test_ $t _rem_euclid>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(x.checked_rem_euclid(y).is_some());
                            prop_assert_eq!(super::$t::rem_euclid(x.inject(), y.inject()), x.rem_euclid(y));
                        }

                        #[test]
                        fn [<test_ $t _count_ones>](x in any::<$t>()) {
                            prop_assert_eq!(super::$t::count_ones(x.inject()), x.count_ones());
                        }

                        #[test]
                        fn [<test_ $t _rotate_right>](x in any::<$t>(), n in 0u32..$t::BITS) {
                            prop_assert_eq!(super::$t::rotate_right(x.inject(), n), x.rotate_right(n));
                        }

                        #[test]
                        fn [<test_ $t _rotate_left>](x in any::<$t>(), n in 0u32..$t::BITS) {
                            prop_assert_eq!(super::$t::rotate_left(x.inject(), n), x.rotate_left(n));
                        }

                        #[test]
                        fn [<test_ $t _leading_zeros>](x in any::<$t>()) {
                            prop_assert_eq!(super::$t::leading_zeros(x.inject()), x.leading_zeros());
                        }

                        #[test]
                        fn [<test_ $t _from_be_bytes>](bytes in any::<[u8; $t::BITS as usize / 8]>()) {
                            prop_assert_eq!(super::$t::from_be_bytes(bytes.inject()), $t::from_be_bytes(bytes));
                        }

                        #[test]
                        fn [<test_ $t _from_le_bytes>](bytes in any::<[u8; $t::BITS as usize / 8]>()) {
                            prop_assert_eq!(super::$t::from_le_bytes(bytes.inject()), $t::from_le_bytes(bytes));
                        }

                        #[test]
                        fn [<test_ $t _to_be_bytes>](x in any::<$t>()) {
                            prop_assert_eq!(super::$t::to_be_bytes(x.inject()), x.to_be_bytes().inject());
                        }

                        #[test]
                        fn [<test_ $t _to_le_bytes>](x in any::<$t>()) {
                            prop_assert_eq!(super::$t::to_le_bytes(x.inject()), x.to_le_bytes().inject());
                        }

                        #[test]
                        fn [<test_ $t _checked_div>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::checked_div(x.inject(), y.inject()), x.checked_div(y).inject());
                        }

                        #[test]
                        fn [<test_ $t _checked_rem>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::checked_rem(x.inject(), y.inject()), x.checked_rem(y).inject());
                        }

                        // `y` is fixed at zero: a full-range `y` almost never hits
                        // the divide-by-zero arm for the wider types.
                        #[test]
                        fn [<test_ $t _checked_div_by_zero>](x in any::<$t>()) {
                            prop_assert_eq!(
                                super::$t::checked_div(x.inject(), (0 as $t).inject()),
                                x.checked_div(0).inject());
                        }

                        #[test]
                        fn [<test_ $t _checked_rem_by_zero>](x in any::<$t>()) {
                            prop_assert_eq!(
                                super::$t::checked_rem(x.inject(), (0 as $t).inject()),
                                x.checked_rem(0).inject());
                        }

                        // Three generators: short digits mostly parse, the wider
                        // alphabet overflows or fails per radix, `.*` is junk.
                        #[test]
                        fn [<test_ $t _from_str_radix>](
                            s in prop_oneof!["[0-9]{1,2}", "[0-9a-zA-Z+-]{0,12}", ".*"],
                            radix in 2u32..=36,
                        ) {
                            prop_assert_eq!(
                                super::$t::from_str_radix(&s, radix),
                                $t::from_str_radix(&s, radix).inject()
                            );
                        }

                        #[test]
                        fn [<test_ $t _div_ceil>](x in any::<$t>(), y in any::<$t>()) {
                            // skip inputs where div_ceil panics (same cases as checked_div == None)
                            if x.checked_div(y).is_some() {
                                prop_assert_eq!(super::$t::div_ceil(x.inject(), y.inject()), x.div_ceil(y));
                            }
                        }

                        #[test]
                        fn [<test_ $t _count_zeros>](x in any::<$t>()) {
                            prop_assert_eq!(super::$t::count_zeros(x.inject()), x.count_zeros());
                        }

                        #[test]
                        fn [<test_ $t _checked_ilog2>](x in any::<$t>()) {
                            prop_assert_eq!(super::$t::checked_ilog2(x.inject()), x.checked_ilog2().inject());
                        }

                        #[test]
                        fn [<test_ $t _wrapping_neg>](x in any::<$t>()) {
                            prop_assert_eq!(super::$t::wrapping_neg(x.inject()), x.wrapping_neg());
                        }

                        #[test]
                        fn [<test_ $t _overflowing_neg>](x in any::<$t>()) {
                            prop_assert_eq!(super::$t::overflowing_neg(x.inject()), x.overflowing_neg());
                        }

                        #[test]
                        fn [<test_ $t _checked_neg>](x in any::<$t>()) {
                            prop_assert_eq!(super::$t::checked_neg(x.inject()), x.checked_neg().inject());
                        }

                        #[test]
                        fn [<test_ $t _wrapping_pow>](x in any::<$t>(), exp in 0u32..=140) {
                            prop_assert_eq!(super::$t::wrapping_pow(x.inject(), exp), x.wrapping_pow(exp));
                        }

                        #[test]
                        fn [<test_ $t _saturating_pow>](x in any::<$t>(), exp in 0u32..=140) {
                            prop_assert_eq!(super::$t::saturating_pow(x.inject(), exp), x.saturating_pow(exp));
                        }

                        // A small exponent range: with `exp` up to 140 nearly every
                        // base overflows and the test would reject everything.
                        #[test]
                        fn [<test_ $t _strict_pow>](x in any::<$t>(), exp in 0u32..=8) {
                            if x.checked_pow(exp).is_some() {
                                prop_assert_eq!(super::$t::strict_pow(x.inject(), exp), x.strict_pow(exp));
                            }
                        }

                        #[test]
                        fn [<test_ $t _strict_add>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(x.checked_add(y).is_some());
                            prop_assert_eq!(super::$t::strict_add(x.inject(), y.inject()), x.strict_add(y));
                        }

                        #[test]
                        fn [<test_ $t _strict_sub>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(x.checked_sub(y).is_some());
                            prop_assert_eq!(super::$t::strict_sub(x.inject(), y.inject()), x.strict_sub(y));
                        }

                        // Full-range pairs almost always overflow: halve `y` until it fits.
                        #[test]
                        fn [<test_ $t _strict_mul>](x in any::<$t>(), y in any::<$t>()) {
                            let mut y = y;
                            while x.checked_mul(y).is_none() {
                                y /= 2;
                            }
                            prop_assert_eq!(super::$t::strict_mul(x.inject(), y.inject()), x.strict_mul(y));
                        }

                        // `checked_div`'s domain is exactly the one where none of the
                        // division-shaped operations panic: `y != 0`, and for signed
                        // types also not `MIN / -1`.
                        #[test]
                        fn [<test_ $t _division_family>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(x.checked_div(y).is_some());
                            let (mx, my) = (x.inject(), y.inject());
                            prop_assert_eq!(super::$t::div_euclid(mx, my), x.div_euclid(y));
                            prop_assert_eq!(super::$t::div_floor(mx, my), x.div_floor(y));
                            prop_assert_eq!(super::$t::strict_div(mx, my), x.strict_div(y));
                            prop_assert_eq!(super::$t::strict_rem(mx, my), x.strict_rem(y));
                            prop_assert_eq!(super::$t::strict_div_euclid(mx, my), x.strict_div_euclid(y));
                            prop_assert_eq!(super::$t::strict_rem_euclid(mx, my), x.strict_rem_euclid(y));
                            // The pinned toolchain still calls `div_exact` `exact_div`.
                            prop_assert_eq!(super::$t::div_exact(mx, my), x.exact_div(y).inject());
                        }

                        // Only `y != 0` is needed here: these all answer `MIN / -1`
                        // without panicking.
                        #[test]
                        fn [<test_ $t _wrapping_division_family>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(y != 0);
                            let (mx, my) = (x.inject(), y.inject());
                            prop_assert_eq!(super::$t::wrapping_div(mx, my), x.wrapping_div(y));
                            prop_assert_eq!(super::$t::wrapping_rem(mx, my), x.wrapping_rem(y));
                            prop_assert_eq!(super::$t::wrapping_div_euclid(mx, my), x.wrapping_div_euclid(y));
                            prop_assert_eq!(super::$t::wrapping_rem_euclid(mx, my), x.wrapping_rem_euclid(y));
                            prop_assert_eq!(super::$t::saturating_div(mx, my), x.saturating_div(y));
                            prop_assert_eq!(super::$t::overflowing_div(mx, my), x.overflowing_div(y));
                            prop_assert_eq!(super::$t::overflowing_rem(mx, my), x.overflowing_rem(y));
                            prop_assert_eq!(super::$t::overflowing_div_euclid(mx, my), x.overflowing_div_euclid(y));
                            prop_assert_eq!(super::$t::overflowing_rem_euclid(mx, my), x.overflowing_rem_euclid(y));
                        }

                        // Total, so no guard at all.
                        #[test]
                        fn [<test_ $t _checked_division_family>](x in any::<$t>(), y in any::<$t>()) {
                            let (mx, my) = (x.inject(), y.inject());
                            prop_assert_eq!(super::$t::checked_div_euclid(mx, my), x.checked_div_euclid(y).inject());
                            prop_assert_eq!(super::$t::checked_rem_euclid(mx, my), x.checked_rem_euclid(y).inject());
                            // The pinned toolchain still calls `checked_div_exact` `checked_exact_div`.
                            prop_assert_eq!(super::$t::checked_div_exact(mx, my), x.checked_exact_div(y).inject());
                            prop_assert_eq!(
                                super::$t::checked_next_multiple_of(mx, my),
                                x.checked_next_multiple_of(y).inject(),
                            );
                        }

                        #[test]
                        fn [<test_ $t _abs_diff>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::abs_diff(x.inject(), y.inject()), x.abs_diff(y));
                        }

                        #[test]
                        fn [<test_ $t _midpoint>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::midpoint(x.inject(), y.inject()), x.midpoint(y));
                        }
                    }

                    #[test]
                    #[allow(deprecated)]
                    fn [<test_ $t _min_value>]() {
                        assert_eq!(super::$t::min_value(), $t::min_value())
                    }
                    #[test]
                    #[allow(deprecated)]
                    fn [<test_ $t _max_value>]() {
                        assert_eq!(super::$t::max_value(), $t::max_value())
                    }
                )*
            }
        }
    }

    // Tests for unsigned-only operations.
    macro_rules! uint_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    proptest! {
                        #[test]
                        fn [<test_ $t _pow>](x in any::<$t>(), exp in 0u32..=2) {
                            if x <= 2 {
                                prop_assert_eq!(super::$t::pow(x.inject(), exp), x.pow(exp));
                            }
                        }

                        #[test]
                        fn [<test_ $t _ilog2>](x in any::<$t>()) {
                            if x > 0 {
                                prop_assert_eq!(super::$t::ilog2(x.inject()), x.ilog2());
                            }
                        }

                        #[test]
                        fn [<test_ $t _is_power_of_two>](x in any::<$t>()) {
                            prop_assert_eq!(super::$t::is_power_of_two(x.inject()), x.is_power_of_two());
                        }

                        #[test]
                        fn [<test_ $t _is_multiple_of>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assert_eq!(super::$t::is_multiple_of(x.inject(), y.inject()), x.is_multiple_of(y));
                        }

                        // Zero divides only zero; `y` is pinned so the arm is
                        // always taken, and `x` covers both answers.
                        #[test]
                        fn [<test_ $t _is_multiple_of_zero>](x in prop_oneof![Just(0 as $t), any::<$t>()]) {
                            prop_assert_eq!(
                                super::$t::is_multiple_of(x.inject(), (0 as $t).inject()),
                                x.is_multiple_of(0));
                        #[test]
                        fn [<test_ $t _next_multiple_of>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(x.checked_next_multiple_of(y).is_some());
                            prop_assert_eq!(super::$t::next_multiple_of(x.inject(), y.inject()), x.next_multiple_of(y));
                        }
                    }

                    // Unsigned negation only succeeds on zero, so there is nothing to
                    // randomize.
                    #[test]
                    fn [<test_ $t _strict_neg_zero>]() {
                        assert_eq!(super::$t::strict_neg(0), (0 as $t).strict_neg())
                    }
                )*
            }
        }
    }

    // Tests for unsigned operations that take or return the signed sibling type.
    macro_rules! uint_mixed_test {
        ($(($unsigned:ty, $signed:ty))*) => {
            paste! {
                $(
                    proptest! {
                        #[test]
                        fn [<test_ $unsigned _cast_signed>](x in any::<$unsigned>()) {
                            prop_assert_eq!(super::$unsigned::cast_signed(x.inject()), x.cast_signed());
                        }

                        #[test]
                        fn [<test_ $unsigned _checked_signed_diff>](x in any::<$unsigned>(), y in any::<$unsigned>()) {
                            prop_assert_eq!(
                                super::$unsigned::checked_signed_diff(x.inject(), y.inject()),
                                x.checked_signed_diff(y).inject(),
                            );
                        }

                        #[test]
                        fn [<test_ $unsigned _signed_arg_family>](x in any::<$unsigned>(), y in any::<$signed>()) {
                            let (mx, my) = (x.inject(), y.inject());
                            prop_assert_eq!(super::$unsigned::wrapping_add_signed(mx, my), x.wrapping_add_signed(y));
                            prop_assert_eq!(super::$unsigned::wrapping_sub_signed(mx, my), x.wrapping_sub_signed(y));
                            prop_assert_eq!(super::$unsigned::overflowing_add_signed(mx, my), x.overflowing_add_signed(y));
                            prop_assert_eq!(super::$unsigned::overflowing_sub_signed(mx, my), x.overflowing_sub_signed(y));
                            prop_assert_eq!(super::$unsigned::saturating_add_signed(mx, my), x.saturating_add_signed(y));
                            prop_assert_eq!(super::$unsigned::saturating_sub_signed(mx, my), x.saturating_sub_signed(y));
                            prop_assert_eq!(super::$unsigned::checked_add_signed(mx, my), x.checked_add_signed(y).inject());
                            prop_assert_eq!(super::$unsigned::checked_sub_signed(mx, my), x.checked_sub_signed(y).inject());
                        }

                        #[test]
                        fn [<test_ $unsigned _strict_add_signed>](x in any::<$unsigned>(), y in any::<$signed>()) {
                            prop_assume!(x.checked_add_signed(y).is_some());
                            prop_assert_eq!(super::$unsigned::strict_add_signed(x.inject(), y.inject()), x.strict_add_signed(y));
                        }

                        #[test]
                        fn [<test_ $unsigned _strict_sub_signed>](x in any::<$unsigned>(), y in any::<$signed>()) {
                            prop_assume!(x.checked_sub_signed(y).is_some());
                            prop_assert_eq!(super::$unsigned::strict_sub_signed(x.inject(), y.inject()), x.strict_sub_signed(y));
                        }
                    }
                )*
            }
        }
    }

    // Tests for signed-only operations.
    macro_rules! iint_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    proptest! {
                        #[test]
                        fn [<test_ $t _pow>](x in any::<$t>(), exp in 0u32..=2) {
                            if x >= -2 && x <= 2 {
                                prop_assert_eq!(super::$t::pow(x.inject(), exp), x.pow(exp));
                            }
                        }

                        #[test]
                        fn [<test_ $t _abs>](x in any::<$t>()) {
                            if x != $t::MIN {
                                prop_assert_eq!(super::$t::abs(x.inject()), x.abs());
                            }
                        }

                        #[test]
                        fn [<test_ $t _ilog2>](x in any::<$t>()) {
                            if x > 0 {
                                prop_assert_eq!(super::$t::ilog2(x.inject()), x.ilog2());
                            }
                        }

                        // `x` is pinned to `MIN` so that the `y == -1` half of the
                        // `checked_div`/`checked_rem` overflow guard is reached.
                        #[test]
                        fn [<test_ $t _checked_div_at_min>](y in prop_oneof![Just(-1 as $t), any::<$t>()]) {
                            prop_assert_eq!(
                                super::$t::checked_div(<$t>::MIN.inject(), y.inject()),
                                <$t>::MIN.checked_div(y).inject());
                        }

                        #[test]
                        fn [<test_ $t _checked_rem_at_min>](y in prop_oneof![Just(-1 as $t), any::<$t>()]) {
                            prop_assert_eq!(
                                super::$t::checked_rem(<$t>::MIN.inject(), y.inject()),
                                <$t>::MIN.checked_rem(y).inject());
                        }

                        // `0` is biased in: the zero arm is otherwise out of reach
                        // for the wider types.
                        #[test]
                        fn [<test_ $t _signum>](x in prop_oneof![Just(0 as $t), any::<$t>()]) {
                            prop_assert_eq!(super::$t::signum(x.inject()), x.signum());
                        }

                        #[test]
                        fn [<test_ $t _sign_predicates>](x in any::<$t>()) {
                            prop_assert_eq!(super::$t::is_positive(x.inject()), x.is_positive());
                            prop_assert_eq!(super::$t::is_negative(x.inject()), x.is_negative());
                        }

                        #[test]
                        fn [<test_ $t _abs_family>](x in any::<$t>()) {
                            let mx = x.inject();
                            prop_assert_eq!(super::$t::wrapping_abs(mx), x.wrapping_abs());
                            prop_assert_eq!(super::$t::overflowing_abs(mx), x.overflowing_abs());
                            prop_assert_eq!(super::$t::checked_abs(mx), x.checked_abs().inject());
                            prop_assert_eq!(super::$t::saturating_abs(mx), x.saturating_abs());
                            prop_assert_eq!(super::$t::unsigned_abs(mx), x.unsigned_abs());
                            prop_assert_eq!(super::$t::saturating_neg(mx), x.saturating_neg());
                            prop_assert_eq!(super::$t::cast_unsigned(mx), x.cast_unsigned());
                        }

                        #[test]
                        fn [<test_ $t _strict_abs>](x in any::<$t>()) {
                            prop_assume!(x != $t::MIN);
                            prop_assert_eq!(super::$t::strict_abs(x.inject()), x.strict_abs());
                        }

                        #[test]
                        fn [<test_ $t _strict_neg>](x in any::<$t>()) {
                            prop_assume!(x != $t::MIN);
                            prop_assert_eq!(super::$t::strict_neg(x.inject()), x.strict_neg());
                        }
                    }
                )*
            }
        }
    }

    // Tests for signed operations that take an unsigned argument.
    macro_rules! iint_mixed_test {
        ($(($signed:ty, $unsigned:ty))*) => {
            paste! {
                $(
                    proptest! {
                        #[test]
                        fn [<test_ $signed _checked_add_unsigned>](x in any::<$signed>(), y in any::<$unsigned>()) {
                            prop_assert_eq!(
                                super::$signed::checked_add_unsigned(x.inject(), y.inject()),
                                x.checked_add_unsigned(y).inject(),
                            );
                        }

                        #[test]
                        fn [<test_ $signed _checked_sub_unsigned>](x in any::<$signed>(), y in any::<$unsigned>()) {
                            prop_assert_eq!(
                                super::$signed::checked_sub_unsigned(x.inject(), y.inject()),
                                x.checked_sub_unsigned(y).inject(),
                            );
                        }

                        #[test]
                        fn [<test_ $signed _unsigned_arg_family>](x in any::<$signed>(), y in any::<$unsigned>()) {
                            let (mx, my) = (x.inject(), y.inject());
                            prop_assert_eq!(super::$signed::wrapping_add_unsigned(mx, my), x.wrapping_add_unsigned(y));
                            prop_assert_eq!(super::$signed::wrapping_sub_unsigned(mx, my), x.wrapping_sub_unsigned(y));
                            prop_assert_eq!(super::$signed::overflowing_add_unsigned(mx, my), x.overflowing_add_unsigned(y));
                            prop_assert_eq!(super::$signed::overflowing_sub_unsigned(mx, my), x.overflowing_sub_unsigned(y));
                            prop_assert_eq!(super::$signed::saturating_add_unsigned(mx, my), x.saturating_add_unsigned(y));
                            prop_assert_eq!(super::$signed::saturating_sub_unsigned(mx, my), x.saturating_sub_unsigned(y));
                        }

                        #[test]
                        fn [<test_ $signed _strict_add_unsigned>](x in any::<$signed>(), y in any::<$unsigned>()) {
                            prop_assume!(x.checked_add_unsigned(y).is_some());
                            prop_assert_eq!(super::$signed::strict_add_unsigned(x.inject(), y.inject()), x.strict_add_unsigned(y));
                        }

                        #[test]
                        fn [<test_ $signed _strict_sub_unsigned>](x in any::<$signed>(), y in any::<$unsigned>()) {
                            prop_assume!(x.checked_sub_unsigned(y).is_some());
                            prop_assert_eq!(super::$signed::strict_sub_unsigned(x.inject(), y.inject()), x.strict_sub_unsigned(y));
                        }

                        // `clamp_magnitude` has no counterpart on the pinned toolchain, so
                        // the expected value is spelled out from its documented behaviour:
                        // clamp to `±limit`, or leave `x` alone when no `$signed` exceeds it.
                        #[test]
                        fn [<test_ $signed _clamp_magnitude>](x in any::<$signed>(), y in any::<$unsigned>()) {
                            let expected = if y > $signed::MAX as $unsigned {
                                x
                            } else {
                                x.clamp(-(y as $signed), y as $signed)
                            };
                            prop_assert_eq!(super::$signed::clamp_magnitude(x.inject(), y.inject()), expected);
                        }
                    }
                )*
            }
        }
    }

    // Their `requires` rules out overflow, so the domain is exactly where
    // `checked_*` answers `Some` — including `i*::MIN / -1`.
    macro_rules! unchecked_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    proptest! {
                        #[test]
                        fn [<test_ $t _unchecked_add>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(x.checked_add(y).is_some());
                            prop_assert_eq!(
                                unsafe { super::$t::unchecked_add(x.inject(), y.inject()) },
                                unsafe { x.unchecked_add(y) });
                        }

                        #[test]
                        fn [<test_ $t _unchecked_sub>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(x.checked_sub(y).is_some());
                            prop_assert_eq!(
                                unsafe { super::$t::unchecked_sub(x.inject(), y.inject()) },
                                unsafe { x.unchecked_sub(y) });
                        }

                        // Full-range pairs almost always overflow: halve `y` until it fits.
                        #[test]
                        fn [<test_ $t _unchecked_mul>](x in any::<$t>(), y in any::<$t>()) {
                            let mut y = y;
                            while x.checked_mul(y).is_none() {
                                y /= 2;
                            }
                            prop_assert_eq!(
                                unsafe { super::$t::unchecked_mul(x.inject(), y.inject()) },
                                unsafe { x.unchecked_mul(y) });
                        }

                        // std has no `unchecked_div`/`unchecked_rem`; `/` and `%` stand in.
                        #[test]
                        fn [<test_ $t _unchecked_div>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(x.checked_div(y).is_some());
                            prop_assert_eq!(
                                unsafe { super::$t::unchecked_div(x.inject(), y.inject()) },
                                x / y);
                        }

                        #[test]
                        fn [<test_ $t _unchecked_rem>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(x.checked_rem(y).is_some());
                            prop_assert_eq!(
                                unsafe { super::$t::unchecked_rem(x.inject(), y.inject()) },
                                x % y);
                        }

                        // No `unchecked_div_exact` in std on the pinned toolchain; under
                        // its precondition (`y > 0` and an exact division) `/` stands in.
                        #[test]
                        fn [<test_ $t _unchecked_div_exact>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(y > 0);
                            // Round `x` down to a multiple of `y`: exact divisions are far
                            // too rare among random pairs to reach by rejection.
                            let x = x - x % y;
                            prop_assert_eq!(
                                unsafe { super::$t::unchecked_div_exact(x.inject(), y.inject()) },
                                x / y);
                        }
                    }
                )*
            }
        }
    }

    // Signed-only `unchecked_*`, same shape as `unchecked_test!`.
    macro_rules! iint_unchecked_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    proptest! {
                        #[test]
                        fn [<test_ $t _unchecked_neg>](x in any::<$t>()) {
                            prop_assume!(x != $t::MIN);
                            prop_assert_eq!(
                                unsafe { super::$t::unchecked_neg(x.inject()) },
                                unsafe { x.unchecked_neg() });
                        }
                    }
                )*
            }
        }
    }
    iint_unchecked_test! { i8 i16 i32 i64 i128 isize }

    macro_rules! rem_euclid_panic_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $t _rem_euclid_by_zero_panics>]() {
                        let (x, y) = (std::hint::black_box(7 as $t), std::hint::black_box(0 as $t));
                        crate::testing::panics_like_core(
                            || super::$t::rem_euclid(x.inject(), y.inject()),
                            || x.rem_euclid(y),
                        );
                    }
                )*
            }
        }
    }
    rem_euclid_panic_test! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

    macro_rules! rem_euclid_overflow_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $t _rem_euclid_min_by_neg_one_panics>]() {
                        let (x, y) = (std::hint::black_box(<$t>::MIN), std::hint::black_box(-1 as $t));
                        crate::testing::panics_like_core(
                            || super::$t::rem_euclid(x.inject(), y.inject()),
                            || x.rem_euclid(y),
                        );
                    }
                )*
            }
        }
    }
    rem_euclid_overflow_test! { i8 i16 i32 i64 i128 isize }

    // Every division-shaped operation with a `y != 0` precondition, on `y == 0`.
    macro_rules! div_by_zero_panic_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $t _division_by_zero_panics>]() {
                        let (x, y) = (std::hint::black_box(7 as $t), std::hint::black_box(0 as $t));
                        let (mx, my) = (x.inject(), y.inject());
                        crate::testing::panics_like_core(|| super::$t::wrapping_div(mx, my), || x.wrapping_div(y));
                        crate::testing::panics_like_core(|| super::$t::wrapping_rem(mx, my), || x.wrapping_rem(y));
                        crate::testing::panics_like_core(|| super::$t::wrapping_div_euclid(mx, my), || x.wrapping_div_euclid(y));
                        crate::testing::panics_like_core(|| super::$t::wrapping_rem_euclid(mx, my), || x.wrapping_rem_euclid(y));
                        crate::testing::panics_like_core(|| super::$t::saturating_div(mx, my), || x.saturating_div(y));
                        crate::testing::panics_like_core(|| super::$t::overflowing_div(mx, my), || x.overflowing_div(y));
                        crate::testing::panics_like_core(|| super::$t::overflowing_rem(mx, my), || x.overflowing_rem(y));
                        crate::testing::panics_like_core(|| super::$t::overflowing_div_euclid(mx, my), || x.overflowing_div_euclid(y));
                        crate::testing::panics_like_core(|| super::$t::overflowing_rem_euclid(mx, my), || x.overflowing_rem_euclid(y));
                        crate::testing::panics_like_core(|| super::$t::div_euclid(mx, my), || x.div_euclid(y));
                        crate::testing::panics_like_core(|| super::$t::div_floor(mx, my), || x.div_floor(y));
                        crate::testing::panics_like_core(|| super::$t::strict_div(mx, my), || x.strict_div(y));
                        crate::testing::panics_like_core(|| super::$t::strict_rem(mx, my), || x.strict_rem(y));
                        crate::testing::panics_like_core(|| super::$t::strict_div_euclid(mx, my), || x.strict_div_euclid(y));
                        crate::testing::panics_like_core(|| super::$t::strict_rem_euclid(mx, my), || x.strict_rem_euclid(y));
                        crate::testing::panics_like_core(|| super::$t::div_exact(mx, my), || x.exact_div(y));
                    }
                )*
            }
        }
    }
    div_by_zero_panic_test! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

    // The signed `MIN / -1` overflow, for the operations that do not absorb it.
    macro_rules! min_div_neg_one_panic_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $t _min_div_neg_one_panics>]() {
                        let (x, y) = (std::hint::black_box(<$t>::MIN), std::hint::black_box(-1 as $t));
                        let (mx, my) = (x.inject(), y.inject());
                        crate::testing::panics_like_core(|| super::$t::div_euclid(mx, my), || x.div_euclid(y));
                        crate::testing::panics_like_core(|| super::$t::div_floor(mx, my), || x.div_floor(y));
                        crate::testing::panics_like_core(|| super::$t::strict_div(mx, my), || x.strict_div(y));
                        crate::testing::panics_like_core(|| super::$t::strict_rem(mx, my), || x.strict_rem(y));
                        crate::testing::panics_like_core(|| super::$t::strict_div_euclid(mx, my), || x.strict_div_euclid(y));
                        crate::testing::panics_like_core(|| super::$t::strict_rem_euclid(mx, my), || x.strict_rem_euclid(y));
                        crate::testing::panics_like_core(|| super::$t::div_exact(mx, my), || x.exact_div(y));
                    }
                )*
            }
        }
    }
    min_div_neg_one_panic_test! { i8 i16 i32 i64 i128 isize }

    // `strict_*` panics on overflow in every build profile, unlike `+`/`-`/`*`.
    macro_rules! strict_panic_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $t _strict_add_overflow_panics>]() {
                        let (x, y) = (std::hint::black_box(<$t>::MAX), std::hint::black_box(1 as $t));
                        crate::testing::panics_like_core(
                            || super::$t::strict_add(x.inject(), y.inject()),
                            || x.strict_add(y),
                        );
                    }
                    #[test]
                    fn [<test_ $t _strict_sub_overflow_panics>]() {
                        let (x, y) = (std::hint::black_box(<$t>::MIN), std::hint::black_box(1 as $t));
                        crate::testing::panics_like_core(
                            || super::$t::strict_sub(x.inject(), y.inject()),
                            || x.strict_sub(y),
                        );
                    }
                    #[test]
                    fn [<test_ $t _strict_mul_overflow_panics>]() {
                        let (x, y) = (std::hint::black_box(<$t>::MAX), std::hint::black_box(2 as $t));
                        crate::testing::panics_like_core(
                            || super::$t::strict_mul(x.inject(), y.inject()),
                            || x.strict_mul(y),
                        );
                    }
                    #[test]
                    fn [<test_ $t _strict_pow_overflow_panics>]() {
                        let (x, exp) = (std::hint::black_box(<$t>::MAX), std::hint::black_box(2u32));
                        crate::testing::panics_like_core(
                            || super::$t::strict_pow(x.inject(), exp),
                            || x.strict_pow(exp),
                        );
                    }
                )*
            }
        }
    }
    strict_panic_test! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

    // `strict_neg` overflows on any non-zero unsigned value, and on signed `MIN`.
    macro_rules! strict_neg_panic_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $t _strict_neg_overflow_panics>]() {
                        let x = std::hint::black_box(1 as $t);
                        crate::testing::panics_like_core(
                            || super::$t::strict_neg(x.inject()),
                            || x.strict_neg(),
                        );
                    }
                )*
            }
        }
    }
    strict_neg_panic_test! { u8 u16 u32 u64 u128 usize }

    macro_rules! iint_strict_neg_panic_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $t _strict_neg_overflow_panics>]() {
                        let x = std::hint::black_box(<$t>::MIN);
                        crate::testing::panics_like_core(
                            || super::$t::strict_neg(x.inject()),
                            || x.strict_neg(),
                        );
                    }
                    #[test]
                    fn [<test_ $t _strict_abs_overflow_panics>]() {
                        let x = std::hint::black_box(<$t>::MIN);
                        crate::testing::panics_like_core(
                            || super::$t::strict_abs(x.inject()),
                            || x.strict_abs(),
                        );
                    }
                )*
            }
        }
    }
    iint_strict_neg_panic_test! { i8 i16 i32 i64 i128 isize }

    macro_rules! next_multiple_of_panic_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $t _next_multiple_of_by_zero_panics>]() {
                        let (x, y) = (std::hint::black_box(7 as $t), std::hint::black_box(0 as $t));
                        crate::testing::panics_like_core(
                            || super::$t::next_multiple_of(x.inject(), y.inject()),
                            || x.next_multiple_of(y),
                        );
                    }
                    #[test]
                    fn [<test_ $t _next_multiple_of_overflow_panics>]() {
                        // `MAX % 4 == 3`, so rounding up leaves the range.
                        let (x, y) = (std::hint::black_box(<$t>::MAX), std::hint::black_box(4 as $t));
                        crate::testing::panics_like_core(
                            || super::$t::next_multiple_of(x.inject(), y.inject()),
                            || x.next_multiple_of(y),
                        );
                    }
                )*
            }
        }
    }
    next_multiple_of_panic_test! { u8 u16 u32 u64 u128 usize }

    macro_rules! strict_signed_arg_panic_test {
        ($(($unsigned:ty, $signed:ty))*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $unsigned _strict_add_signed_overflow_panics>]() {
                        let (x, y) = (std::hint::black_box(<$unsigned>::MAX), std::hint::black_box(1 as $signed));
                        crate::testing::panics_like_core(
                            || super::$unsigned::strict_add_signed(x.inject(), y.inject()),
                            || x.strict_add_signed(y),
                        );
                    }
                    #[test]
                    fn [<test_ $unsigned _strict_sub_signed_overflow_panics>]() {
                        let (x, y) = (std::hint::black_box(0 as $unsigned), std::hint::black_box(1 as $signed));
                        crate::testing::panics_like_core(
                            || super::$unsigned::strict_sub_signed(x.inject(), y.inject()),
                            || x.strict_sub_signed(y),
                        );
                    }
                    #[test]
                    fn [<test_ $signed _strict_add_unsigned_overflow_panics>]() {
                        let (x, y) = (std::hint::black_box(<$signed>::MAX), std::hint::black_box(1 as $unsigned));
                        crate::testing::panics_like_core(
                            || super::$signed::strict_add_unsigned(x.inject(), y.inject()),
                            || x.strict_add_unsigned(y),
                        );
                    }
                    #[test]
                    fn [<test_ $signed _strict_sub_unsigned_overflow_panics>]() {
                        let (x, y) = (std::hint::black_box(<$signed>::MIN), std::hint::black_box(1 as $unsigned));
                        crate::testing::panics_like_core(
                            || super::$signed::strict_sub_unsigned(x.inject(), y.inject()),
                            || x.strict_sub_unsigned(y),
                        );
                    }
                )*
            }
        }
    }
    strict_signed_arg_panic_test! { (u8, i8) (u16, i16) (u32, i32) (u64, i64) (u128, i128) (usize, isize) }

    int_test! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }
    unchecked_test! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }
    uint_test! { u8 u16 u32 u64 u128 usize }
    iint_test! { i8 i16 i32 i64 i128 isize }
    iint_mixed_test! { (i8, u8) (i16, u16) (i32, u32) (i64, u64) (i128, u128) (isize, usize) }
    uint_mixed_test! { (u8, i8) (u16, i16) (u32, i32) (u64, i64) (u128, i128) (usize, isize) }

    macro_rules! default_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $t _default>]() {
                        assert_eq!(<$t as crate::default::Default>::default(), <$t as std::default::Default>::default());
                    }
                )*
            }
        }
    }

    default_test! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize bool }
}
