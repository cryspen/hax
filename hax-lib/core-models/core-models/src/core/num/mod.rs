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
        // Methods `core` provides on one width only (the `u8` ASCII helpers) go
        // here rather than in a separate `impl` block, which would renumber the
        // impls the backends name items after.
        extras: { $($extra: tt)* },
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

            // F*-only: `charon::opaque` drops the declaration too, and the Lean
            // lane has this primitive, so it can take the body instead.
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn rotate_right(x: $Self, n: core::primitive::u32) -> $Self {
                paste! { [<rotate_right_ $Name>](x, n) }
            }
            /// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)

            // F*-only: `charon::opaque` drops the declaration too, and the Lean
            // lane has this primitive, so it can take the body instead.
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
            }
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
            // Spelled `== false` rather than `!`: hax's F* printer mis-parenthesizes a
            // negated tuple projection.
            #[hax_lib::requires(<$Name>::overflowing_pow(x, exp).1 == false)]
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
            /// See [`std::primitive::u8::trailing_zeros`] (and similar for other integer types)
            pub fn trailing_zeros(x: $Self) -> core::primitive::u32 {
                // `x & -x` keeps only the lowest set bit; one less than it is a mask of
                // exactly the trailing zeros, so counting its ones counts them.
                if x == 0 {
                    <$Name>::BITS
                } else {
                    Self::count_ones(Self::wrapping_sub(x & Self::wrapping_neg(x), 1))
                }
            }
            /// See [`std::primitive::u8::trailing_ones`] (and similar for other integer types)
            pub fn trailing_ones(x: $Self) -> core::primitive::u32 {
                // `MAX - x` is `!x` for an unsigned type.
                Self::trailing_zeros(Self::wrapping_sub(<$Name>::MAX, x))
            }
            /// See [`std::primitive::u8::leading_ones`] (and similar for other integer types)
            pub fn leading_ones(x: $Self) -> core::primitive::u32 {
                Self::leading_zeros(Self::wrapping_sub(<$Name>::MAX, x))
            }
            /// See [`std::primitive::u8::bit_width`] (and similar for other unsigned integer types)
            // F*-only: the body is `BITS - leading_zeros(x)` and F* cannot see the
            // subtraction is in range. Lean's `Result` carries the failure instead.
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn bit_width(x: $Self) -> core::primitive::u32 {
                <$Name>::BITS - Self::leading_zeros(x)
            }
            /// See [`std::primitive::u8::highest_one`] (and similar for other unsigned integer types)
            pub fn highest_one(x: $Self) -> Option<core::primitive::u32> {
                // The index of the highest set bit is `floor(log2(x))`.
                Self::checked_ilog2(x)
            }
            /// See [`std::primitive::u8::lowest_one`] (and similar for other integer types)
            pub fn lowest_one(x: $Self) -> Option<core::primitive::u32> {
                if x == 0 {
                    Option::None
                } else {
                    Option::Some(Self::trailing_zeros(x))
                }
            }
            /// See [`std::primitive::u8::isolate_lowest_one`] (and similar for other integer types)
            pub fn isolate_lowest_one(x: $Self) -> $Self {
                x & Self::wrapping_neg(x)
            }
            /// See [`std::primitive::u8::isolate_highest_one`] (and similar for other integer types)
            pub fn isolate_highest_one(x: $Self) -> $Self {
                // `MAX / 2 + 1` is the top bit; shifting it down by the leading-zero
                // count lands it on the highest set bit (and on nothing, for `x == 0`).
                x & Self::wrapping_shr(<$Name>::MAX / 2 + 1, Self::leading_zeros(x))
            }
            // The remaining operations in this block are endianness-dependent. The model
            // fixes a little-endian target, consistent with the fixed 64-bit `usize` it
            // already assumes (`rust_primitives::arithmetic::SIZE_BYTES`).
            /// See [`std::primitive::u8::swap_bytes`] (and similar for other integer types)
            pub fn swap_bytes(x: $Self) -> $Self {
                // Reading the big-endian bytes of `x` back as little-endian reverses them.
                Self::from_le_bytes(Self::to_be_bytes(x))
            }
            /// See [`std::primitive::u8::to_be`] (and similar for other integer types)
            pub fn to_be(x: $Self) -> $Self {
                Self::swap_bytes(x)
            }
            /// See [`std::primitive::u8::to_le`] (and similar for other integer types)
            pub fn to_le(x: $Self) -> $Self {
                x
            }
            /// See [`std::primitive::u8::from_be`] (and similar for other integer types)
            pub fn from_be(x: $Self) -> $Self {
                Self::swap_bytes(x)
            }
            /// See [`std::primitive::u8::from_le`] (and similar for other integer types)
            pub fn from_le(x: $Self) -> $Self {
                x
            }
            /// See [`std::primitive::u8::to_ne_bytes`] (and similar for other integer types)
            pub fn to_ne_bytes(x: $Self) -> [core::primitive::u8; $Bytes] {
                Self::to_le_bytes(x)
            }
            /// See [`std::primitive::u8::from_ne_bytes`] (and similar for other integer types)
            pub fn from_ne_bytes(bytes: [core::primitive::u8; $Bytes]) -> $Self {
                Self::from_le_bytes(bytes)
            }
            /// See [`std::primitive::u8::wrapping_shl`] (and similar for other integer types)
            pub fn wrapping_shl(x: $Self, n: core::primitive::u32) -> $Self {
                // `n % BITS` is `core`'s `n & (BITS - 1)`; spelled as a remainder it is
                // the form the backends can see stays below `BITS`.
                x << (n % <$Name>::BITS)
            }
            /// See [`std::primitive::u8::wrapping_shr`] (and similar for other integer types)
            pub fn wrapping_shr(x: $Self, n: core::primitive::u32) -> $Self {
                x >> (n % <$Name>::BITS)
            }
            /// See [`std::primitive::u8::overflowing_shl`] (and similar for other integer types)
            pub fn overflowing_shl(x: $Self, n: core::primitive::u32) -> ($Self, bool) {
                (Self::wrapping_shl(x, n), n >= <$Name>::BITS)
            }
            /// See [`std::primitive::u8::overflowing_shr`] (and similar for other integer types)
            pub fn overflowing_shr(x: $Self, n: core::primitive::u32) -> ($Self, bool) {
                (Self::wrapping_shr(x, n), n >= <$Name>::BITS)
            }
            /// See [`std::primitive::u8::checked_shl`] (and similar for other integer types)
            pub fn checked_shl(x: $Self, n: core::primitive::u32) -> Option<$Self> {
                if n < <$Name>::BITS {
                    Option::Some(x << n)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::u8::checked_shr`] (and similar for other integer types)
            pub fn checked_shr(x: $Self, n: core::primitive::u32) -> Option<$Self> {
                if n < <$Name>::BITS {
                    Option::Some(x >> n)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::u8::strict_shl`] (and similar for other integer types)
            #[hax_lib::requires(n < <$Name>::BITS)]
            pub fn strict_shl(x: $Self, n: core::primitive::u32) -> $Self {
                if n < <$Name>::BITS {
                    x << n
                } else {
                    crate::panicking::internal::panic()
                }
            }
            /// See [`std::primitive::u8::strict_shr`] (and similar for other integer types)
            #[hax_lib::requires(n < <$Name>::BITS)]
            pub fn strict_shr(x: $Self, n: core::primitive::u32) -> $Self {
                if n < <$Name>::BITS {
                    x >> n
                } else {
                    crate::panicking::internal::panic()
                }
            }
            /// See [`std::primitive::u8::unbounded_shl`] (and similar for other integer types)
            pub fn unbounded_shl(x: $Self, n: core::primitive::u32) -> $Self {
                if n < <$Name>::BITS {
                    x << n
                } else {
                    0
                }
            }
            /// See [`std::primitive::u8::unbounded_shr`] (and similar for other unsigned integer types)
            pub fn unbounded_shr(x: $Self, n: core::primitive::u32) -> $Self {
                if n < <$Name>::BITS {
                    x >> n
                } else {
                    0
                }
            }
            /// See [`std::primitive::u8::unchecked_shl`] (and similar for other integer types)
            #[hax_lib::requires(n < <$Name>::BITS)]
            pub unsafe fn unchecked_shl(x: $Self, n: core::primitive::u32) -> $Self {
                x << n
            }
            /// See [`std::primitive::u8::unchecked_shr`] (and similar for other integer types)
            #[hax_lib::requires(n < <$Name>::BITS)]
            pub unsafe fn unchecked_shr(x: $Self, n: core::primitive::u32) -> $Self {
                x >> n
            }
            /// See [`std::primitive::u8::shl_exact`] (and similar for other unsigned integer types)
            pub fn shl_exact(x: $Self, n: core::primitive::u32) -> Option<$Self> {
                if n <= Self::leading_zeros(x) && n < <$Name>::BITS {
                    Option::Some(x << n)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::u8::shr_exact`] (and similar for other integer types)
            pub fn shr_exact(x: $Self, n: core::primitive::u32) -> Option<$Self> {
                if n <= Self::trailing_zeros(x) && n < <$Name>::BITS {
                    Option::Some(x >> n)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::u8::unchecked_shl_exact`] (and similar for other unsigned integer types)
            #[hax_lib::requires(n <= <$Name>::leading_zeros(x) && n < <$Name>::BITS)]
            pub unsafe fn unchecked_shl_exact(x: $Self, n: core::primitive::u32) -> $Self {
                x << n
            }
            /// See [`std::primitive::u8::unchecked_shr_exact`] (and similar for other integer types)
            #[hax_lib::requires(n <= <$Name>::trailing_zeros(x) && n < <$Name>::BITS)]
            pub unsafe fn unchecked_shr_exact(x: $Self, n: core::primitive::u32) -> $Self {
                x >> n
            }
            /// See [`std::primitive::u8::funnel_shl`] (and similar for other unsigned integer types)
            // `x:y` shifted left by `n`, keeping the more significant half.
            #[hax_lib::requires(n < <$Name>::BITS)]
            pub fn funnel_shl(x: $Self, y: $Self, n: core::primitive::u32) -> $Self {
                if n == 0 {
                    x
                } else {
                    Self::wrapping_shl(x, n) | Self::wrapping_shr(y, <$Name>::BITS - n)
                }
            }
            /// See [`std::primitive::u8::funnel_shr`] (and similar for other unsigned integer types)
            // `x:y` shifted right by `n`, keeping the less significant half.
            #[hax_lib::requires(n < <$Name>::BITS)]
            pub fn funnel_shr(x: $Self, y: $Self, n: core::primitive::u32) -> $Self {
                if n == 0 {
                    y
                } else {
                    Self::wrapping_shr(y, n) | Self::wrapping_shl(x, <$Name>::BITS - n)
                }
            }
            /// See [`std::primitive::u8::unchecked_disjoint_bitor`] (and similar for other unsigned integer types)
            #[hax_lib::requires(x & y == 0)]
            pub unsafe fn unchecked_disjoint_bitor(x: $Self, y: $Self) -> $Self {
                x | y
            }
            /// See [`std::primitive::u8::checked_next_power_of_two`] (and similar for other unsigned integer types)
            pub fn checked_next_power_of_two(x: $Self) -> Option<$Self> {
                if x <= 1 {
                    Option::Some(1)
                } else {
                    // `MAX >> leading_zeros(x - 1)` is `core`'s "one less than the next
                    // power of two". `x >= 2` makes the shift in range; the remainder makes
                    // that visible to the backends without changing the value.
                    Self::checked_add(<$Name>::MAX >> (Self::leading_zeros(x - 1) % <$Name>::BITS), 1)
                }
            }
            /// See [`std::primitive::u8::wrapping_next_power_of_two`] (and similar for other unsigned integer types)
            pub fn wrapping_next_power_of_two(x: $Self) -> $Self {
                if x <= 1 {
                    1
                } else {
                    Self::wrapping_add(<$Name>::MAX >> (Self::leading_zeros(x - 1) % <$Name>::BITS), 1)
                }
            }
            /// See [`std::primitive::u8::next_power_of_two`] (and similar for other unsigned integer types)
            // F*-only: the `+ 1` is in range exactly when a next power of two
            // exists, and tying that to `leading_zeros` needs bit-level
            // reasoning. Lean's `Result` carries the failure instead.
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            #[hax_lib::requires(x.to_int() * 2.to_int() <= <$Name>::MAX.to_int() + 1.to_int())]
            pub fn next_power_of_two(x: $Self) -> $Self {
                match Self::checked_next_power_of_two(x) {
                    Option::Some(result) => result,
                    Option::None => crate::panicking::internal::panic(),
                }
            }
            /// See [`std::primitive::u8::reverse_bits`] (and similar for other unsigned integer types)
            pub fn reverse_bits(x: $Self) -> $Self {
                // Swap adjacent bits, then adjacent pairs, then adjacent nibbles, and
                // finally the bytes. `MAX / 3`, `MAX / 5` and `MAX / 17` are the
                // `0x55..`, `0x33..` and `0x0f..` masks at this width.
                let m1 = <$Name>::MAX / 3;
                let m2 = <$Name>::MAX / 5;
                let m4 = <$Name>::MAX / 17;
                let x = Self::wrapping_shl(x & m1, 1) | (Self::wrapping_shr(x, 1) & m1);
                let x = Self::wrapping_shl(x & m2, 2) | (Self::wrapping_shr(x, 2) & m2);
                let x = Self::wrapping_shl(x & m4, 4) | (Self::wrapping_shr(x, 4) & m4);
                Self::swap_bytes(x)
            }
            /// See [`std::primitive::u8::widening_mul`] (and similar for other unsigned integer types)
            pub fn widening_mul(x: $Self, y: $Self) -> ($Self, $Self) {
                // Schoolbook multiplication on half-width limbs, so no wider
                // intermediate type is needed (`u128` has none). Every partial product
                // and sum below stays in range, but showing that needs nonlinear
                // reasoning, so the wrapping forms are used throughout.
                let half = <$Name>::BITS / 2;
                let lo_mask = Self::wrapping_shr(<$Name>::MAX, half);
                let xl = x & lo_mask;
                let xh = Self::wrapping_shr(x, half);
                let yl = y & lo_mask;
                let yh = Self::wrapping_shr(y, half);
                let ll = Self::wrapping_mul(xl, yl);
                let lh = Self::wrapping_mul(xl, yh);
                let hl = Self::wrapping_mul(xh, yl);
                let hh = Self::wrapping_mul(xh, yh);
                let mid = Self::wrapping_add(
                    Self::wrapping_add(Self::wrapping_shr(ll, half), lh & lo_mask),
                    hl & lo_mask,
                );
                let low = (ll & lo_mask) | Self::wrapping_shl(mid & lo_mask, half);
                let high = Self::wrapping_add(
                    Self::wrapping_add(
                        Self::wrapping_add(hh, Self::wrapping_shr(lh, half)),
                        Self::wrapping_shr(hl, half),
                    ),
                    Self::wrapping_shr(mid, half),
                );
                (low, high)
            }
            /// See [`std::primitive::u8::carrying_mul_add`] (and similar for other unsigned integer types)
            pub fn carrying_mul_add(x: $Self, y: $Self, carry: $Self, add: $Self) -> ($Self, $Self) {
                let (low, high) = Self::widening_mul(x, y);
                // `x * y + carry + add` is at most `(2^N - 1)^2 + 2 * (2^N - 1)`, which
                // still fits in `2 * N` bits, so the high word cannot overflow.
                let (low, c1) = Self::overflowing_add(low, carry);
                let (low, c2) = Self::overflowing_add(low, add);
                let high = Self::wrapping_add(high, if c1 { 1 } else { 0 });
                let high = Self::wrapping_add(high, if c2 { 1 } else { 0 });
                (low, high)
            }
            /// See [`std::primitive::u8::carrying_mul`] (and similar for other unsigned integer types)
            pub fn carrying_mul(x: $Self, y: $Self, carry: $Self) -> ($Self, $Self) {
                Self::carrying_mul_add(x, y, carry, 0)
            }
            /// See [`std::primitive::u8::carrying_add`] (and similar for other integer types)
            pub fn carrying_add(x: $Self, y: $Self, carry: bool) -> ($Self, bool) {
                let (a, c1) = Self::overflowing_add(x, y);
                let (b, c2) = Self::overflowing_add(a, if carry { 1 } else { 0 });
                // At most one of the two additions can carry.
                (b, c1 || c2)
            }
            /// See [`std::primitive::u8::borrowing_sub`] (and similar for other integer types)
            pub fn borrowing_sub(x: $Self, y: $Self, borrow: bool) -> ($Self, bool) {
                let (a, c1) = Self::overflowing_sub(x, y);
                let (b, c2) = Self::overflowing_sub(a, if borrow { 1 } else { 0 });
                // At most one of the two subtractions can borrow.
                (b, c1 || c2)
            }
            $($extra)*
        }
    };
}

use hax_lib::int::ToInt;

macro_rules! iint_impl {
    (
        $Self: ty,
        $USelf: ty,
        $Name: ty,
        $UName: ty,
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

            // F*-only: `charon::opaque` drops the declaration too, and the Lean
            // lane has this primitive, so it can take the body instead.
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn rotate_right(x: $Self, n: core::primitive::u32) -> $Self {
                paste! { [<rotate_right_ $Name>](x, n) }
            }
            /// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)

            // F*-only: `charon::opaque` drops the declaration too, and the Lean
            // lane has this primitive, so it can take the body instead.
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
            }
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
            // Spelled `== false` rather than `!`: hax's F* printer mis-parenthesizes a
            // negated tuple projection.
            #[hax_lib::requires(<$Name>::overflowing_pow(x, exp).1 == false)]
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
            /// See [`std::primitive::i8::reverse_bits`] (and similar for other signed integer types)
            pub fn reverse_bits(x: $Self) -> $Self {
                // Bit reversal only depends on the bit pattern, so go through the
                // unsigned sibling rather than repeating the mask dance for signs.
                <$UName>::reverse_bits(x as $USelf) as $Self
            }
            /// See [`std::primitive::i8::next_multiple_of`] (and similar for other signed integer types)
            // The precondition is "the checked form succeeds": stating it arithmetically
            // would mean repeating the whole sign analysis of the body.
            #[hax_lib::requires(match <$Name>::checked_next_multiple_of(x, y) {
                Option::Some(_) => true,
                Option::None => false,
            })]
            pub fn next_multiple_of(x: $Self, y: $Self) -> $Self {
                match Self::checked_next_multiple_of(x, y) {
                    Option::Some(result) => result,
                    Option::None => crate::panicking::internal::panic(),
                }
            }
            /// See [`std::primitive::i8::widening_mul`] (and similar for other signed integer types)
            pub fn widening_mul(x: $Self, y: $Self) -> ($USelf, $Self) {
                // A signed value is its unsigned bit pattern minus `2^N` when negative,
                // so the signed high word is the unsigned one minus the *other* operand's
                // bit pattern for each negative operand.
                let (low, high) = <$UName>::widening_mul(x as $USelf, y as $USelf);
                let high = high as $Self;
                let high = if x < 0 {
                    Self::wrapping_sub(high, y)
                } else {
                    high
                };
                let high = if y < 0 {
                    Self::wrapping_sub(high, x)
                } else {
                    high
                };
                (low, high)
            }
            /// See [`std::primitive::i8::carrying_mul_add`] (and similar for other signed integer types)
            pub fn carrying_mul_add(x: $Self, y: $Self, carry: $Self, add: $Self) -> ($USelf, $Self) {
                let (low, high) = Self::widening_mul(x, y);
                // `carry` and `add` enter the `2 * N`-bit product sign-extended: each
                // contributes its bit pattern to the low word and its sign to the high one.
                let (low, c1) = <$UName>::overflowing_add(low, carry as $USelf);
                let (low, c2) = <$UName>::overflowing_add(low, add as $USelf);
                let high = Self::wrapping_add(high, if c1 { 1 } else { 0 });
                let high = Self::wrapping_add(high, if c2 { 1 } else { 0 });
                let high = Self::wrapping_add(high, if carry < 0 { -1 } else { 0 });
                let high = Self::wrapping_add(high, if add < 0 { -1 } else { 0 });
                (low, high)
            }
            /// See [`std::primitive::i8::carrying_mul`] (and similar for other signed integer types)
            pub fn carrying_mul(x: $Self, y: $Self, carry: $Self) -> ($USelf, $Self) {
                Self::carrying_mul_add(x, y, carry, 0)
            }
            /// See [`std::primitive::i8::carrying_add`] (and similar for other integer types)
            pub fn carrying_add(x: $Self, y: $Self, carry: bool) -> ($Self, bool) {
                let (a, b) = Self::overflowing_add(x, y);
                let (c, d) = Self::overflowing_add(a, if carry { 1 } else { 0 });
                // The two additions overflow in opposite directions, so a single
                // overflow of either is a real one and two cancel out.
                (c, b != d)
            }
            /// See [`std::primitive::i8::borrowing_sub`] (and similar for other integer types)
            pub fn borrowing_sub(x: $Self, y: $Self, borrow: bool) -> ($Self, bool) {
                let (a, b) = Self::overflowing_sub(x, y);
                let (c, d) = Self::overflowing_sub(a, if borrow { 1 } else { 0 });
                (c, b != d)
            }
            /// See [`std::primitive::i8::trailing_zeros`] (and similar for other integer types)
            pub fn trailing_zeros(x: $Self) -> core::primitive::u32 {
                // `x & -x` keeps only the lowest set bit; one less than it is a mask of
                // exactly the trailing zeros, so counting its ones counts them.
                if x == 0 {
                    <$Name>::BITS
                } else {
                    Self::count_ones(Self::wrapping_sub(x & Self::wrapping_neg(x), 1))
                }
            }
            /// See [`std::primitive::i8::trailing_ones`] (and similar for other integer types)
            pub fn trailing_ones(x: $Self) -> core::primitive::u32 {
                // `-1 - x` is `!x`, and it never overflows.
                Self::trailing_zeros(Self::wrapping_sub(-1, x))
            }
            /// See [`std::primitive::i8::leading_ones`] (and similar for other integer types)
            pub fn leading_ones(x: $Self) -> core::primitive::u32 {
                Self::leading_zeros(Self::wrapping_sub(-1, x))
            }
            /// See [`std::primitive::i8::highest_one`] (and similar for other signed integer types)
            // F*-only: F* cannot see that subtracting `leading_zeros` from
            // `BITS - 1` stays in range. Lean's `Result` carries the failure.
            #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
            pub fn highest_one(x: $Self) -> Option<core::primitive::u32> {
                if x == 0 {
                    Option::None
                } else {
                    Option::Some(<$Name>::BITS - 1 - Self::leading_zeros(x))
                }
            }
            /// See [`std::primitive::i8::lowest_one`] (and similar for other integer types)
            pub fn lowest_one(x: $Self) -> Option<core::primitive::u32> {
                if x == 0 {
                    Option::None
                } else {
                    Option::Some(Self::trailing_zeros(x))
                }
            }
            /// See [`std::primitive::i8::isolate_lowest_one`] (and similar for other integer types)
            pub fn isolate_lowest_one(x: $Self) -> $Self {
                x & Self::wrapping_neg(x)
            }
            /// See [`std::primitive::i8::isolate_highest_one`] (and similar for other integer types)
            pub fn isolate_highest_one(x: $Self) -> $Self {
                // `MIN` is the top bit; an arithmetic shift down by the leading-zero count
                // lands its lowest one on the highest set bit of `x`.
                x & Self::wrapping_shr(<$Name>::MIN, Self::leading_zeros(x))
            }
            // The remaining operations in this block are endianness-dependent. The model
            // fixes a little-endian target, consistent with the fixed 64-bit `isize` it
            // already assumes (`rust_primitives::arithmetic::SIZE_BYTES`).
            /// See [`std::primitive::i8::swap_bytes`] (and similar for other integer types)
            pub fn swap_bytes(x: $Self) -> $Self {
                // Reading the big-endian bytes of `x` back as little-endian reverses them.
                Self::from_le_bytes(Self::to_be_bytes(x))
            }
            /// See [`std::primitive::i8::to_be`] (and similar for other integer types)
            pub fn to_be(x: $Self) -> $Self {
                Self::swap_bytes(x)
            }
            /// See [`std::primitive::i8::to_le`] (and similar for other integer types)
            pub fn to_le(x: $Self) -> $Self {
                x
            }
            /// See [`std::primitive::i8::from_be`] (and similar for other integer types)
            pub fn from_be(x: $Self) -> $Self {
                Self::swap_bytes(x)
            }
            /// See [`std::primitive::i8::from_le`] (and similar for other integer types)
            pub fn from_le(x: $Self) -> $Self {
                x
            }
            /// See [`std::primitive::i8::to_ne_bytes`] (and similar for other integer types)
            pub fn to_ne_bytes(x: $Self) -> [core::primitive::u8; $Bytes] {
                Self::to_le_bytes(x)
            }
            /// See [`std::primitive::i8::from_ne_bytes`] (and similar for other integer types)
            pub fn from_ne_bytes(bytes: [core::primitive::u8; $Bytes]) -> $Self {
                Self::from_le_bytes(bytes)
            }
            /// See [`std::primitive::i8::wrapping_shl`] (and similar for other integer types)
            pub fn wrapping_shl(x: $Self, n: core::primitive::u32) -> $Self {
                // `n % BITS` is `core`'s `n & (BITS - 1)`; spelled as a remainder it is
                // the form the backends can see stays below `BITS`.
                x << (n % <$Name>::BITS)
            }
            /// See [`std::primitive::i8::wrapping_shr`] (and similar for other integer types)
            pub fn wrapping_shr(x: $Self, n: core::primitive::u32) -> $Self {
                x >> (n % <$Name>::BITS)
            }
            /// See [`std::primitive::i8::overflowing_shl`] (and similar for other integer types)
            pub fn overflowing_shl(x: $Self, n: core::primitive::u32) -> ($Self, bool) {
                (Self::wrapping_shl(x, n), n >= <$Name>::BITS)
            }
            /// See [`std::primitive::i8::overflowing_shr`] (and similar for other integer types)
            pub fn overflowing_shr(x: $Self, n: core::primitive::u32) -> ($Self, bool) {
                (Self::wrapping_shr(x, n), n >= <$Name>::BITS)
            }
            /// See [`std::primitive::i8::checked_shl`] (and similar for other integer types)
            pub fn checked_shl(x: $Self, n: core::primitive::u32) -> Option<$Self> {
                if n < <$Name>::BITS {
                    Option::Some(x << n)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::i8::checked_shr`] (and similar for other integer types)
            pub fn checked_shr(x: $Self, n: core::primitive::u32) -> Option<$Self> {
                if n < <$Name>::BITS {
                    Option::Some(x >> n)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::i8::strict_shl`] (and similar for other integer types)
            #[hax_lib::requires(n < <$Name>::BITS)]
            pub fn strict_shl(x: $Self, n: core::primitive::u32) -> $Self {
                if n < <$Name>::BITS {
                    x << n
                } else {
                    crate::panicking::internal::panic()
                }
            }
            /// See [`std::primitive::i8::strict_shr`] (and similar for other integer types)
            #[hax_lib::requires(n < <$Name>::BITS)]
            pub fn strict_shr(x: $Self, n: core::primitive::u32) -> $Self {
                if n < <$Name>::BITS {
                    x >> n
                } else {
                    crate::panicking::internal::panic()
                }
            }
            /// See [`std::primitive::i8::unbounded_shl`] (and similar for other integer types)
            pub fn unbounded_shl(x: $Self, n: core::primitive::u32) -> $Self {
                if n < <$Name>::BITS {
                    x << n
                } else {
                    0
                }
            }
            /// See [`std::primitive::i8::unbounded_shr`] (and similar for other signed integer types)
            pub fn unbounded_shr(x: $Self, n: core::primitive::u32) -> $Self {
                if n < <$Name>::BITS {
                    x >> n
                } else {
                    // An arithmetic shift by `BITS - 1` fills with the sign bit, which is
                    // what shifting a signed value all the way out gives.
                    x >> (<$Name>::BITS - 1)
                }
            }
            /// See [`std::primitive::i8::unchecked_shl`] (and similar for other integer types)
            #[hax_lib::requires(n < <$Name>::BITS)]
            pub unsafe fn unchecked_shl(x: $Self, n: core::primitive::u32) -> $Self {
                x << n
            }
            /// See [`std::primitive::i8::unchecked_shr`] (and similar for other integer types)
            #[hax_lib::requires(n < <$Name>::BITS)]
            pub unsafe fn unchecked_shr(x: $Self, n: core::primitive::u32) -> $Self {
                x >> n
            }
            /// See [`std::primitive::i8::shl_exact`] (and similar for other signed integer types)
            // The `n < BITS` conjunct is implied by the other two (both counts are at most
            // `BITS`), but spelling it out is what makes the shift in range for a backend.
            pub fn shl_exact(x: $Self, n: core::primitive::u32) -> Option<$Self> {
                if (n < Self::leading_zeros(x) || n < Self::leading_ones(x)) && n < <$Name>::BITS {
                    Option::Some(x << n)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::i8::shr_exact`] (and similar for other integer types)
            pub fn shr_exact(x: $Self, n: core::primitive::u32) -> Option<$Self> {
                if n <= Self::trailing_zeros(x) && n < <$Name>::BITS {
                    Option::Some(x >> n)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::i8::unchecked_shl_exact`] (and similar for other signed integer types)
            #[hax_lib::requires((n < <$Name>::leading_zeros(x) || n < <$Name>::leading_ones(x)) && n < <$Name>::BITS)]
            pub unsafe fn unchecked_shl_exact(x: $Self, n: core::primitive::u32) -> $Self {
                x << n
            }
            /// See [`std::primitive::i8::unchecked_shr_exact`] (and similar for other integer types)
            #[hax_lib::requires(n <= <$Name>::trailing_zeros(x) && n < <$Name>::BITS)]
            pub unsafe fn unchecked_shr_exact(x: $Self, n: core::primitive::u32) -> $Self {
                x >> n
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
    // `core` puts the ASCII helpers on `u8` only. They take `&self`/`&mut self`,
    // so the model mirrors that rather than taking the byte by value.
    extras: {
        /// See [`std::primitive::u8::is_ascii`]
        pub fn is_ascii(x: &core::primitive::u8) -> bool {
            *x < 128
        }
        /// See [`std::primitive::u8::is_ascii_uppercase`]
        pub fn is_ascii_uppercase(x: &core::primitive::u8) -> bool {
            *x >= b'A' && *x <= b'Z'
        }
        /// See [`std::primitive::u8::is_ascii_lowercase`]
        pub fn is_ascii_lowercase(x: &core::primitive::u8) -> bool {
            *x >= b'a' && *x <= b'z'
        }
        /// See [`std::primitive::u8::is_ascii_alphabetic`]
        pub fn is_ascii_alphabetic(x: &core::primitive::u8) -> bool {
            Self::is_ascii_uppercase(x) || Self::is_ascii_lowercase(x)
        }
        /// See [`std::primitive::u8::is_ascii_digit`]
        pub fn is_ascii_digit(x: &core::primitive::u8) -> bool {
            *x >= b'0' && *x <= b'9'
        }
        /// See [`std::primitive::u8::is_ascii_octdigit`]
        pub fn is_ascii_octdigit(x: &core::primitive::u8) -> bool {
            *x >= b'0' && *x <= b'7'
        }
        /// See [`std::primitive::u8::is_ascii_hexdigit`]
        pub fn is_ascii_hexdigit(x: &core::primitive::u8) -> bool {
            Self::is_ascii_digit(x) || (*x >= b'A' && *x <= b'F') || (*x >= b'a' && *x <= b'f')
        }
        /// See [`std::primitive::u8::is_ascii_alphanumeric`]
        pub fn is_ascii_alphanumeric(x: &core::primitive::u8) -> bool {
            Self::is_ascii_alphabetic(x) || Self::is_ascii_digit(x)
        }
        /// See [`std::primitive::u8::is_ascii_punctuation`]
        pub fn is_ascii_punctuation(x: &core::primitive::u8) -> bool {
            (*x >= b'!' && *x <= b'/')
                || (*x >= b':' && *x <= b'@')
                || (*x >= b'[' && *x <= b'`')
                || (*x >= b'{' && *x <= b'~')
        }
        /// See [`std::primitive::u8::is_ascii_graphic`]
        pub fn is_ascii_graphic(x: &core::primitive::u8) -> bool {
            *x >= b'!' && *x <= b'~'
        }
        /// See [`std::primitive::u8::is_ascii_whitespace`]
        pub fn is_ascii_whitespace(x: &core::primitive::u8) -> bool {
            *x == b' ' || *x == b'\t' || *x == b'\n' || *x == 12 || *x == b'\r'
        }
        /// See [`std::primitive::u8::is_ascii_control`]
        pub fn is_ascii_control(x: &core::primitive::u8) -> bool {
            *x <= 31 || *x == 127
        }
        /// See [`std::primitive::u8::to_ascii_uppercase`]
        // The bounds are repeated rather than reusing `is_ascii_lowercase` so that a
        // backend sees directly that the subtraction stays in range.
        pub fn to_ascii_uppercase(x: &core::primitive::u8) -> core::primitive::u8 {
            if *x >= b'a' && *x <= b'z' { *x - 32 } else { *x }
        }
        /// See [`std::primitive::u8::to_ascii_lowercase`]
        pub fn to_ascii_lowercase(x: &core::primitive::u8) -> core::primitive::u8 {
            if *x >= b'A' && *x <= b'Z' { *x + 32 } else { *x }
        }
        /// See [`std::primitive::u8::eq_ignore_ascii_case`]
        pub fn eq_ignore_ascii_case(x: &core::primitive::u8, other: &core::primitive::u8) -> bool {
            Self::to_ascii_lowercase(x) == Self::to_ascii_lowercase(other)
        }
        /// See [`std::primitive::u8::make_ascii_uppercase`]
        pub fn make_ascii_uppercase(x: &mut core::primitive::u8) {
            *x = Self::to_ascii_uppercase(x)
        }
        /// See [`std::primitive::u8::make_ascii_lowercase`]
        pub fn make_ascii_lowercase(x: &mut core::primitive::u8) {
            *x = Self::to_ascii_lowercase(x)
        }
    },
}

uint_impl! {
    core::primitive::u16,
    core::primitive::i16,
    u16,
    65535,
    16,
    2,
    // `core` puts this on `u16` only.
    extras: {
        /// See [`std::primitive::u16::is_utf16_surrogate`]
        pub fn is_utf16_surrogate(x: core::primitive::u16) -> bool {
            x >= 0xD800 && x <= 0xDFFF
        }
    },
}

uint_impl! {
    core::primitive::u32,
    core::primitive::i32,
    u32,
    4294967295,
    32,
    4,
    extras: {},
}

uint_impl! {
    core::primitive::u64,
    core::primitive::i64,
    u64,
    18446744073709551615,
    64,
    8,
    extras: {},
}

uint_impl! {
    core::primitive::u128,
    core::primitive::i128,
    u128,
    340282366920938463463374607431768211455,
    128,
    16,
    extras: {},
}

uint_impl! {
    core::primitive::usize,
    core::primitive::isize,
    usize,
    USIZE_MAX,
    SIZE_BITS,
    SIZE_BYTES,
    extras: {},
}

iint_impl! {
    core::primitive::i8,
    core::primitive::u8,
    i8,
    u8,
    127,
    -128,
    8,
    1,
}

iint_impl! {
    core::primitive::i16,
    core::primitive::u16,
    i16,
    u16,
    32767,
    -32768,
    16,
    2,
}

iint_impl! {
    core::primitive::i32,
    core::primitive::u32,
    i32,
    u32,
    2147483647,
    -2147483648,
    32,
    4,
}

iint_impl! {
    core::primitive::i64,
    core::primitive::u64,
    i64,
    u64,
    9223372036854775807,
    -9223372036854775808,
    64,
    8,
}

iint_impl! {
    core::primitive::i128,
    core::primitive::u128,
    i128,
    u128,
    170141183460469231731687303715884105727,
    -170141183460469231731687303715884105728,
    128,
    16,
}

iint_impl! {
    core::primitive::isize,
    core::primitive::usize,
    isize,
    usize,
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

// `core` defines these three wrapper types in the private modules
// `core::num::{nonzero,wrapping,saturating}` and re-exports them from
// `core::num`. The extracted item paths follow the *defining* module, so the
// model has to mirror that structure for the two to line up: an Aeneas
// reference to `core.num.wrapping.WrappingU8.count_ones` only resolves if our
// definition sits in `num::wrapping` too.
mod nonzero {
    use super::*;

    /// See [`std::num::NonZero`]
    // `core` bounds this on the sealed unstable `ZeroablePrimitive` and keeps the
    // field private; the model drops the bound (nothing here needs it) and makes the
    // field `pub(crate)` so the internal constructions below and the test-side
    // `Inject` can build values directly. Outside the crate, `new`/`new_unchecked`
    // are still the only way in, so the non-zero invariant holds by construction.
    // It is not a type-level refinement, though, which is why `div_ceil` has to
    // restate the divisor's non-zeroness as a precondition.
    #[cfg_attr(test, derive(PartialEq, Eq, Debug, Clone, Copy))]
    pub struct NonZero<T>(pub(crate) T);

    /// See [`std::num::NonZeroU8`]
    pub type NonZeroU8 = NonZero<core::primitive::u8>;
    /// See [`std::num::NonZeroU16`]
    pub type NonZeroU16 = NonZero<core::primitive::u16>;
    /// See [`std::num::NonZeroU32`]
    pub type NonZeroU32 = NonZero<core::primitive::u32>;
    /// See [`std::num::NonZeroU64`]
    pub type NonZeroU64 = NonZero<core::primitive::u64>;
    /// See [`std::num::NonZeroU128`]
    pub type NonZeroU128 = NonZero<core::primitive::u128>;
    /// See [`std::num::NonZeroUsize`]
    pub type NonZeroUsize = NonZero<core::primitive::usize>;
    /// See [`std::num::NonZeroI8`]
    pub type NonZeroI8 = NonZero<core::primitive::i8>;
    /// See [`std::num::NonZeroI16`]
    pub type NonZeroI16 = NonZero<core::primitive::i16>;
    /// See [`std::num::NonZeroI32`]
    pub type NonZeroI32 = NonZero<core::primitive::i32>;
    /// See [`std::num::NonZeroI64`]
    pub type NonZeroI64 = NonZero<core::primitive::i64>;
    /// See [`std::num::NonZeroI128`]
    pub type NonZeroI128 = NonZero<core::primitive::i128>;
    /// See [`std::num::NonZeroIsize`]
    pub type NonZeroIsize = NonZero<core::primitive::isize>;

    macro_rules! nonzero_impl {
        (
            $Self: ty,
            $Name: ty,
            $Min: expr,
            $($extra: tt)*
        ) => {
            #[hax_lib::attributes]
            impl NonZero<$Self> {
                /// See [`std::num::NonZero::<u8>::BITS`] (and similar for other integer types)
                pub const BITS: core::primitive::u32 = <$Name>::BITS;
                /// See [`std::num::NonZero::<u8>::MIN`] (and similar for other integer types)
                pub const MIN: Self = NonZero($Min);
                /// See [`std::num::NonZero::<u8>::MAX`] (and similar for other integer types)
                pub const MAX: Self = NonZero(<$Name>::MAX);
                /// See [`std::num::NonZero::new`] (and similar for other integer types)
                pub fn new(n: $Self) -> Option<NonZero<$Self>> {
                    if n == 0 {
                        Option::None
                    } else {
                        Option::Some(NonZero(n))
                    }
                }
                /// See [`std::num::NonZero::new_unchecked`] (and similar for other integer types)
                #[hax_lib::requires(n != 0)]
                pub unsafe fn new_unchecked(n: $Self) -> NonZero<$Self> {
                    NonZero(n)
                }
                /// See [`std::num::NonZero::get`] (and similar for other integer types)
                pub fn get(self) -> $Self {
                    self.0
                }
                /// See [`std::num::NonZero::<u8>::from_str_radix`] (and similar for other integer types)
                // Excluded from coverage: the Lean library models no string
                // primitives, so the body is a placeholder rather than a model.
                #[cfg_attr(coverage_nightly, coverage(off))]
                #[hax_lib::opaque]
                pub fn from_str_radix(
                    src: &str,
                    radix: core::primitive::u32,
                ) -> Result<NonZero<$Self>, error::ParseIntError> {
                    crate::panicking::internal::panic()
                }
                /// See [`std::num::NonZero::<u8>::leading_zeros`] (and similar for other integer types)
                pub fn leading_zeros(self) -> core::primitive::u32 {
                    <$Name>::leading_zeros(self.0)
                }
                /// See [`std::num::NonZero::<u8>::trailing_zeros`] (and similar for other integer types)
                pub fn trailing_zeros(self) -> core::primitive::u32 {
                    <$Name>::trailing_zeros(self.0)
                }
                /// See [`std::num::NonZero::<u8>::lowest_one`] (and similar for other integer types)
                pub fn lowest_one(self) -> core::primitive::u32 {
                    <$Name>::trailing_zeros(self.0)
                }
                /// See [`std::num::NonZero::<u8>::count_ones`] (and similar for other integer types)
                pub fn count_ones(self) -> NonZero<core::primitive::u32> {
                    NonZero(<$Name>::count_ones(self.0))
                }
                /// See [`std::num::NonZero::<u8>::isolate_highest_one`] (and similar for other integer types)
                pub fn isolate_highest_one(self) -> Self {
                    NonZero(<$Name>::isolate_highest_one(self.0))
                }
                /// See [`std::num::NonZero::<u8>::isolate_lowest_one`] (and similar for other integer types)
                pub fn isolate_lowest_one(self) -> Self {
                    NonZero(<$Name>::isolate_lowest_one(self.0))
                }
                /// See [`std::num::NonZero::<u8>::rotate_left`] (and similar for other integer types)
                pub fn rotate_left(self, n: core::primitive::u32) -> Self {
                    NonZero(<$Name>::rotate_left(self.0, n))
                }
                /// See [`std::num::NonZero::<u8>::rotate_right`] (and similar for other integer types)
                pub fn rotate_right(self, n: core::primitive::u32) -> Self {
                    NonZero(<$Name>::rotate_right(self.0, n))
                }
                /// See [`std::num::NonZero::<u8>::reverse_bits`] (and similar for other integer types)
                pub fn reverse_bits(self) -> Self {
                    NonZero(<$Name>::reverse_bits(self.0))
                }
                /// See [`std::num::NonZero::<u8>::swap_bytes`] (and similar for other integer types)
                pub fn swap_bytes(self) -> Self {
                    NonZero(<$Name>::swap_bytes(self.0))
                }
                /// See [`std::num::NonZero::<u8>::to_be`] (and similar for other integer types)
                pub fn to_be(self) -> Self {
                    NonZero(<$Name>::to_be(self.0))
                }
                /// See [`std::num::NonZero::<u8>::to_le`] (and similar for other integer types)
                pub fn to_le(self) -> Self {
                    NonZero(<$Name>::to_le(self.0))
                }
                /// See [`std::num::NonZero::<u8>::from_be`] (and similar for other integer types)
                pub fn from_be(x: Self) -> Self {
                    NonZero(<$Name>::from_be(x.0))
                }
                /// See [`std::num::NonZero::<u8>::from_le`] (and similar for other integer types)
                pub fn from_le(x: Self) -> Self {
                    NonZero(<$Name>::from_le(x.0))
                }
                /// See [`std::num::NonZero::<u8>::checked_mul`] (and similar for other integer types)
                pub fn checked_mul(self, other: Self) -> Option<Self> {
                    let (result, overflowed) = <$Name>::overflowing_mul(self.0, other.0);
                    if overflowed {
                        Option::None
                    } else {
                        Option::Some(NonZero(result))
                    }
                }
                /// See [`std::num::NonZero::<u8>::saturating_mul`] (and similar for other integer types)
                pub fn saturating_mul(self, other: Self) -> Self {
                    NonZero(<$Name>::saturating_mul(self.0, other.0))
                }
                /// See [`std::num::NonZero::<u8>::checked_pow`] (and similar for other integer types)
                pub fn checked_pow(self, other: core::primitive::u32) -> Option<Self> {
                    let (result, overflowed) = <$Name>::overflowing_pow(self.0, other);
                    if overflowed {
                        Option::None
                    } else {
                        Option::Some(NonZero(result))
                    }
                }
                /// See [`std::num::NonZero::<u8>::saturating_pow`] (and similar for other integer types)
                pub fn saturating_pow(self, other: core::primitive::u32) -> Self {
                    NonZero(<$Name>::saturating_pow(self.0, other))
                }
                $($extra)*
            }
        };
    }

    macro_rules! nonzero_uint_impls {
        ($($Self: ty | $ISelf: ty | $Name: ty)*) => {
            $(
                nonzero_impl! { $Self, $Name, 1,
                    /// See [`std::num::NonZero::<u8>::highest_one`] (and similar for other unsigned integer types)
                    pub fn highest_one(self) -> core::primitive::u32 {
                        // The index of the highest set bit of a non-zero value is `ilog2`.
                        <$Name>::ilog2(self.0)
                    }
                    /// See [`std::num::NonZero::<u8>::ilog2`] (and similar for other unsigned integer types)
                    pub fn ilog2(self) -> core::primitive::u32 {
                        <$Name>::ilog2(self.0)
                    }
                    /// See [`std::num::NonZero::<u8>::bit_width`] (and similar for other unsigned integer types)
                    pub fn bit_width(self) -> NonZero<core::primitive::u32> {
                        NonZero(<$Name>::bit_width(self.0))
                    }
                    /// See [`std::num::NonZero::<u8>::checked_add`] (and similar for other unsigned integer types)
                    pub fn checked_add(self, other: $Self) -> Option<Self> {
                        let (result, overflowed) = <$Name>::overflowing_add(self.0, other);
                        if overflowed {
                            Option::None
                        } else {
                            Option::Some(NonZero(result))
                        }
                    }
                    /// See [`std::num::NonZero::<u8>::saturating_add`] (and similar for other unsigned integer types)
                    pub fn saturating_add(self, other: $Self) -> Self {
                        NonZero(<$Name>::saturating_add(self.0, other))
                    }
                    /// See [`std::num::NonZero::<u8>::unchecked_add`] (and similar for other unsigned integer types)
                    #[hax_lib::requires(self.0.to_int() + other.to_int() <= <$Name>::MAX.to_int())]
                    pub unsafe fn unchecked_add(self, other: $Self) -> Self {
                        NonZero(<$Name>::unchecked_add(self.0, other))
                    }
                    /// See [`std::num::NonZero::<u8>::unchecked_mul`] (and similar for other unsigned integer types)
                    #[hax_lib::requires(self.0.to_int() * other.0.to_int() <= <$Name>::MAX.to_int())]
                    pub unsafe fn unchecked_mul(self, other: Self) -> Self {
                        NonZero(<$Name>::unchecked_mul(self.0, other.0))
                    }
                    /// See [`std::num::NonZero::<u8>::checked_next_power_of_two`] (and similar for other unsigned integer types)
                    pub fn checked_next_power_of_two(self) -> Option<Self> {
                        match <$Name>::checked_next_power_of_two(self.0) {
                            Option::Some(result) => Option::Some(NonZero(result)),
                            Option::None => Option::None,
                        }
                    }
                    /// See [`std::num::NonZero::<u8>::midpoint`] (and similar for other unsigned integer types)
                    pub fn midpoint(self, rhs: Self) -> Self {
                        NonZero(<$Name>::midpoint(self.0, rhs.0))
                    }
                    /// See [`std::num::NonZero::<u8>::is_power_of_two`] (and similar for other unsigned integer types)
                    pub fn is_power_of_two(self) -> bool {
                        // A non-zero value is a power of two exactly when it has one bit set.
                        <$Name>::count_ones(self.0) < 2
                    }
                    /// See [`std::num::NonZero::<u8>::cast_signed`] (and similar for other unsigned integer types)
                    pub fn cast_signed(self) -> NonZero<$ISelf> {
                        NonZero(<$Name>::cast_signed(self.0))
                    }
                    /// See [`std::num::NonZero::<u8>::div_ceil`] (and similar for other unsigned integer types)
                    // The model's `NonZero` carries no type-level invariant, so the divisor's
                    // non-zeroness has to be restated here for the backends.
                    #[hax_lib::requires(rhs.0 != 0)]
                    pub fn div_ceil(self, rhs: Self) -> Self {
                        NonZero(<$Name>::div_ceil(self.0, rhs.0))
                    }
                }
            )*
        };
    }

    macro_rules! nonzero_iint_impls {
        ($($Self: ty | $USelf: ty | $Name: ty)*) => {
            $(
                nonzero_impl! { $Self, $Name, <$Name>::MIN,
                    /// See [`std::num::NonZero::<i8>::highest_one`] (and similar for other signed integer types)
                    // Opaque: `leading_zeros` is opaque, so no backend can see that subtracting
                    // it from `BITS - 1` stays in range.
                    #[hax_lib::opaque]
                    pub fn highest_one(self) -> core::primitive::u32 {
                        <$Name>::BITS - 1 - <$Name>::leading_zeros(self.0)
                    }
                    /// See [`std::num::NonZero::<i8>::unchecked_mul`] (and similar for other signed integer types)
                    #[hax_lib::requires(self.0.to_int() * other.0.to_int() <= <$Name>::MAX.to_int() && self.0.to_int() * other.0.to_int() >= <$Name>::MIN.to_int())]
                    pub unsafe fn unchecked_mul(self, other: Self) -> Self {
                        NonZero(<$Name>::unchecked_mul(self.0, other.0))
                    }
                    /// See [`std::num::NonZero::<i8>::abs`] (and similar for other signed integer types)
                    #[hax_lib::requires(self.0 > <$Name>::MIN)]
                    pub fn abs(self) -> Self {
                        NonZero(<$Name>::abs(self.0))
                    }
                    /// See [`std::num::NonZero::<i8>::checked_abs`] (and similar for other signed integer types)
                    pub fn checked_abs(self) -> Option<Self> {
                        match <$Name>::checked_abs(self.0) {
                            Option::Some(result) => Option::Some(NonZero(result)),
                            Option::None => Option::None,
                        }
                    }
                    /// See [`std::num::NonZero::<i8>::overflowing_abs`] (and similar for other signed integer types)
                    pub fn overflowing_abs(self) -> (Self, bool) {
                        let (result, overflowed) = <$Name>::overflowing_abs(self.0);
                        (NonZero(result), overflowed)
                    }
                    /// See [`std::num::NonZero::<i8>::saturating_abs`] (and similar for other signed integer types)
                    pub fn saturating_abs(self) -> Self {
                        NonZero(<$Name>::saturating_abs(self.0))
                    }
                    /// See [`std::num::NonZero::<i8>::wrapping_abs`] (and similar for other signed integer types)
                    pub fn wrapping_abs(self) -> Self {
                        NonZero(<$Name>::wrapping_abs(self.0))
                    }
                    /// See [`std::num::NonZero::<i8>::unsigned_abs`] (and similar for other signed integer types)
                    pub fn unsigned_abs(self) -> NonZero<$USelf> {
                        NonZero(<$Name>::unsigned_abs(self.0))
                    }
                    /// See [`std::num::NonZero::<i8>::is_positive`] (and similar for other signed integer types)
                    pub fn is_positive(self) -> bool {
                        <$Name>::is_positive(self.0)
                    }
                    /// See [`std::num::NonZero::<i8>::is_negative`] (and similar for other signed integer types)
                    pub fn is_negative(self) -> bool {
                        <$Name>::is_negative(self.0)
                    }
                    /// See [`std::num::NonZero::<i8>::checked_neg`] (and similar for other signed integer types)
                    pub fn checked_neg(self) -> Option<Self> {
                        match <$Name>::checked_neg(self.0) {
                            Option::Some(result) => Option::Some(NonZero(result)),
                            Option::None => Option::None,
                        }
                    }
                    /// See [`std::num::NonZero::<i8>::overflowing_neg`] (and similar for other signed integer types)
                    pub fn overflowing_neg(self) -> (Self, bool) {
                        let (result, overflowed) = <$Name>::overflowing_neg(self.0);
                        (NonZero(result), overflowed)
                    }
                    /// See [`std::num::NonZero::<i8>::saturating_neg`] (and similar for other signed integer types)
                    pub fn saturating_neg(self) -> Self {
                        NonZero(<$Name>::saturating_neg(self.0))
                    }
                    /// See [`std::num::NonZero::<i8>::wrapping_neg`] (and similar for other signed integer types)
                    pub fn wrapping_neg(self) -> Self {
                        NonZero(<$Name>::wrapping_neg(self.0))
                    }
                    /// See [`std::num::NonZero::<i8>::cast_unsigned`] (and similar for other signed integer types)
                    pub fn cast_unsigned(self) -> NonZero<$USelf> {
                        NonZero(<$Name>::cast_unsigned(self.0))
                    }
                }
            )*
        };
    }

    nonzero_uint_impls! {
        core::primitive::u8 | core::primitive::i8 | u8
        core::primitive::u16 | core::primitive::i16 | u16
        core::primitive::u32 | core::primitive::i32 | u32
        core::primitive::u64 | core::primitive::i64 | u64
        core::primitive::u128 | core::primitive::i128 | u128
        core::primitive::usize | core::primitive::isize | usize
    }

    nonzero_iint_impls! {
        core::primitive::i8 | core::primitive::u8 | i8
        core::primitive::i16 | core::primitive::u16 | i16
        core::primitive::i32 | core::primitive::u32 | i32
        core::primitive::i64 | core::primitive::u64 | i64
        core::primitive::i128 | core::primitive::u128 | i128
        core::primitive::isize | core::primitive::usize | isize
    }
}

pub use nonzero::{
    NonZero, NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize, NonZeroU8,
    NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize,
};

// `Wrapping`/`Saturating` only differ in which of the modelled integer
// operations they delegate to, so both are generated from the same three
// macros: the width-independent part, plus the unsigned-only and signed-only
// extras `core` adds in separate `impl` blocks.
macro_rules! wrapper_impl {
    (
        $Wrap: ident,
        $Self: ty,
        $Name: ty,
        $pow: ident,
        $($extra: tt)*
    ) => {
        impl $Wrap<$Self> {
            /// See [`std::num::Wrapping::MIN`] (and similar for `Saturating` and other integer types)
            pub const MIN: Self = $Wrap(<$Name>::MIN);
            /// See [`std::num::Wrapping::MAX`] (and similar for `Saturating` and other integer types)
            pub const MAX: Self = $Wrap(<$Name>::MAX);
            /// See [`std::num::Wrapping::BITS`] (and similar for `Saturating` and other integer types)
            pub const BITS: core::primitive::u32 = <$Name>::BITS;
            /// See [`std::num::Wrapping::count_ones`] (and similar for `Saturating` and other integer types)
            pub fn count_ones(self) -> core::primitive::u32 {
                <$Name>::count_ones(self.0)
            }
            /// See [`std::num::Wrapping::count_zeros`] (and similar for `Saturating` and other integer types)
            pub fn count_zeros(self) -> core::primitive::u32 {
                <$Name>::count_zeros(self.0)
            }
            /// See [`std::num::Wrapping::trailing_zeros`] (and similar for `Saturating` and other integer types)
            pub fn trailing_zeros(self) -> core::primitive::u32 {
                <$Name>::trailing_zeros(self.0)
            }
            /// See [`std::num::Wrapping::leading_zeros`] (and similar for `Saturating` and other integer types)
            pub fn leading_zeros(self) -> core::primitive::u32 {
                <$Name>::leading_zeros(self.0)
            }
            /// See [`std::num::Wrapping::rotate_left`] (and similar for `Saturating` and other integer types)
            pub fn rotate_left(self, n: core::primitive::u32) -> Self {
                $Wrap(<$Name>::rotate_left(self.0, n))
            }
            /// See [`std::num::Wrapping::rotate_right`] (and similar for `Saturating` and other integer types)
            pub fn rotate_right(self, n: core::primitive::u32) -> Self {
                $Wrap(<$Name>::rotate_right(self.0, n))
            }
            /// See [`std::num::Wrapping::swap_bytes`] (and similar for `Saturating` and other integer types)
            pub fn swap_bytes(self) -> Self {
                $Wrap(<$Name>::swap_bytes(self.0))
            }
            /// See [`std::num::Wrapping::to_be`] (and similar for `Saturating` and other integer types)
            pub fn to_be(self) -> Self {
                $Wrap(<$Name>::to_be(self.0))
            }
            /// See [`std::num::Wrapping::to_le`] (and similar for `Saturating` and other integer types)
            pub fn to_le(self) -> Self {
                $Wrap(<$Name>::to_le(self.0))
            }
            /// See [`std::num::Wrapping::from_be`] (and similar for `Saturating` and other integer types)
            pub fn from_be(x: Self) -> Self {
                $Wrap(<$Name>::from_be(x.0))
            }
            /// See [`std::num::Wrapping::from_le`] (and similar for `Saturating` and other integer types)
            pub fn from_le(x: Self) -> Self {
                $Wrap(<$Name>::from_le(x.0))
            }
            /// See [`std::num::Wrapping::reverse_bits`] (and similar for `Saturating` and other integer types)
            pub fn reverse_bits(self) -> Self {
                $Wrap(<$Name>::reverse_bits(self.0))
            }
            /// See [`std::num::Wrapping::pow`] (and similar for `Saturating` and other integer types)
            pub fn pow(self, exp: core::primitive::u32) -> Self {
                $Wrap(<$Name>::$pow(self.0, exp))
            }
            $($extra)*
        }
    };
}

mod wrapping {
    use super::*;

    /// See [`std::num::Wrapping`]
    #[cfg_attr(test, derive(PartialEq, Eq, Debug, Clone, Copy))]
    pub struct Wrapping<T>(pub T);

    macro_rules! wrapping_uint_impls {
        ($($Self: ty | $Name: ty)*) => {
            $(
                wrapper_impl! { Wrapping, $Self, $Name, wrapping_pow,
                    /// See [`std::num::Wrapping::is_power_of_two`] (and similar for other unsigned integer types)
                    pub fn is_power_of_two(self) -> bool {
                        <$Name>::is_power_of_two(self.0)
                    }
                    /// See [`std::num::Wrapping::next_power_of_two`] (and similar for other unsigned integer types)
                    pub fn next_power_of_two(self) -> Self {
                        Wrapping(<$Name>::wrapping_next_power_of_two(self.0))
                    }
                }
            )*
        };
    }

    macro_rules! wrapping_iint_impls {
        ($($Self: ty | $Name: ty)*) => {
            $(
                wrapper_impl! { Wrapping, $Self, $Name, wrapping_pow,
                    /// See [`std::num::Wrapping::abs`] (and similar for other signed integer types)
                    pub fn abs(self) -> Wrapping<$Self> {
                        Wrapping(<$Name>::wrapping_abs(self.0))
                    }
                    /// See [`std::num::Wrapping::signum`] (and similar for other signed integer types)
                    pub fn signum(self) -> Wrapping<$Self> {
                        Wrapping(<$Name>::signum(self.0))
                    }
                    /// See [`std::num::Wrapping::is_positive`] (and similar for other signed integer types)
                    pub fn is_positive(self) -> bool {
                        <$Name>::is_positive(self.0)
                    }
                    /// See [`std::num::Wrapping::is_negative`] (and similar for other signed integer types)
                    pub fn is_negative(self) -> bool {
                        <$Name>::is_negative(self.0)
                    }
                }
            )*
        };
    }

    wrapping_uint_impls! {
        core::primitive::u8 | u8
        core::primitive::u16 | u16
        core::primitive::u32 | u32
        core::primitive::u64 | u64
        core::primitive::u128 | u128
        core::primitive::usize | usize
    }

    wrapping_iint_impls! {
        core::primitive::i8 | i8
        core::primitive::i16 | i16
        core::primitive::i32 | i32
        core::primitive::i64 | i64
        core::primitive::i128 | i128
        core::primitive::isize | isize
    }
}

pub use wrapping::Wrapping;

mod saturating {
    use super::*;

    /// See [`std::num::Saturating`]
    #[cfg_attr(test, derive(PartialEq, Eq, Debug, Clone, Copy))]
    pub struct Saturating<T>(pub T);

    macro_rules! saturating_uint_impls {
        ($($Self: ty | $Name: ty)*) => {
            $(
                wrapper_impl! { Saturating, $Self, $Name, saturating_pow,
                    /// See [`std::num::Saturating::is_power_of_two`] (and similar for other unsigned integer types)
                    pub fn is_power_of_two(self) -> bool {
                        <$Name>::is_power_of_two(self.0)
                    }
                }
            )*
        };
    }

    macro_rules! saturating_iint_impls {
        ($($Self: ty | $Name: ty)*) => {
            $(
                wrapper_impl! { Saturating, $Self, $Name, saturating_pow,
                    /// See [`std::num::Saturating::abs`] (and similar for other signed integer types)
                    pub fn abs(self) -> Saturating<$Self> {
                        Saturating(<$Name>::saturating_abs(self.0))
                    }
                    /// See [`std::num::Saturating::signum`] (and similar for other signed integer types)
                    pub fn signum(self) -> Saturating<$Self> {
                        Saturating(<$Name>::signum(self.0))
                    }
                    /// See [`std::num::Saturating::is_positive`] (and similar for other signed integer types)
                    pub fn is_positive(self) -> bool {
                        <$Name>::is_positive(self.0)
                    }
                    /// See [`std::num::Saturating::is_negative`] (and similar for other signed integer types)
                    pub fn is_negative(self) -> bool {
                        <$Name>::is_negative(self.0)
                    }
                }
            )*
        };
    }

    saturating_uint_impls! {
        core::primitive::u8 | u8
        core::primitive::u16 | u16
        core::primitive::u32 | u32
        core::primitive::u64 | u64
        core::primitive::u128 | u128
        core::primitive::usize | usize
    }

    saturating_iint_impls! {
        core::primitive::i8 | i8
        core::primitive::i16 | i16
        core::primitive::i32 | i32
        core::primitive::i64 | i64
        core::primitive::i128 | i128
        core::primitive::isize | isize
    }
}

pub use saturating::Saturating;

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
                            let std_result = $t::from_str_radix(&s, radix);
                            match super::$t::from_str_radix(&s, radix) {
                                crate::result::Result::Ok(v) => prop_assert_eq!(Ok(v), std_result),
                                crate::result::Result::Err(_) => prop_assert!(std_result.is_err()),
                            }
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
                            prop_assert_eq!(super::$t::div_exact(mx, my), x.div_exact(y).inject());
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
                            prop_assert_eq!(
                                super::$t::checked_div_exact(mx, my),
                                x.checked_div_exact(y).inject(),
                            );
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

                        // `0` is where `lowest_one`/`highest_one` answer `None`, and
                        // random draws reach it far too rarely at the wider widths, so
                        // it is one of the generated values rather than left to chance.
                        #[test]
                        fn [<test_ $t _bit_counting_family>](
                            x in prop_oneof![Just(0 as $t), any::<$t>()],
                        ) {
                            let mx = x.inject();
                            prop_assert_eq!(super::$t::trailing_zeros(mx), x.trailing_zeros());
                            prop_assert_eq!(super::$t::trailing_ones(mx), x.trailing_ones());
                            prop_assert_eq!(super::$t::leading_ones(mx), x.leading_ones());
                            prop_assert_eq!(super::$t::lowest_one(mx), x.lowest_one().inject());
                            prop_assert_eq!(super::$t::highest_one(mx), x.highest_one().inject());
                            prop_assert_eq!(super::$t::isolate_lowest_one(mx), x.isolate_lowest_one());
                            prop_assert_eq!(super::$t::isolate_highest_one(mx), x.isolate_highest_one());
                        }

                        // The model fixes a little-endian target, which is also what std
                        // does on the hosts this test suite runs on.
                        #[test]
                        fn [<test_ $t _endianness_family>](x in any::<$t>()) {
                            let mx = x.inject();
                            prop_assert_eq!(super::$t::swap_bytes(mx), x.swap_bytes());
                            prop_assert_eq!(super::$t::to_be(mx), x.to_be());
                            prop_assert_eq!(super::$t::to_le(mx), x.to_le());
                            prop_assert_eq!(super::$t::from_be(mx), $t::from_be(x));
                            prop_assert_eq!(super::$t::from_le(mx), $t::from_le(x));
                            prop_assert_eq!(super::$t::to_ne_bytes(mx), x.to_ne_bytes().inject());
                            prop_assert_eq!(super::$t::reverse_bits(mx), x.reverse_bits());
                        }

                        #[test]
                        fn [<test_ $t _from_ne_bytes>](bytes in any::<[u8; $t::BITS as usize / 8]>()) {
                            prop_assert_eq!(super::$t::from_ne_bytes(bytes.inject()), $t::from_ne_bytes(bytes));
                        }

                        // `n` ranges past `BITS` on purpose: that is where the shift
                        // variants stop agreeing with each other.
                        #[test]
                        fn [<test_ $t _shift_family>](x in any::<$t>(), n in 0u32..=(2 * $t::BITS)) {
                            let mx = x.inject();
                            prop_assert_eq!(super::$t::wrapping_shl(mx, n), x.wrapping_shl(n));
                            prop_assert_eq!(super::$t::wrapping_shr(mx, n), x.wrapping_shr(n));
                            prop_assert_eq!(super::$t::overflowing_shl(mx, n), x.overflowing_shl(n));
                            prop_assert_eq!(super::$t::overflowing_shr(mx, n), x.overflowing_shr(n));
                            prop_assert_eq!(super::$t::checked_shl(mx, n), x.checked_shl(n).inject());
                            prop_assert_eq!(super::$t::checked_shr(mx, n), x.checked_shr(n).inject());
                            prop_assert_eq!(super::$t::unbounded_shl(mx, n), x.unbounded_shl(n));
                            prop_assert_eq!(super::$t::unbounded_shr(mx, n), x.unbounded_shr(n));
                            if n < $t::BITS {
                                prop_assert_eq!(super::$t::strict_shl(mx, n), x.strict_shl(n));
                                prop_assert_eq!(super::$t::strict_shr(mx, n), x.strict_shr(n));
                            }
                        }

                        #[test]
                        fn [<test_ $t _widening_ops>](
                            x in any::<$t>(),
                            y in any::<$t>(),
                            carry in any::<$t>(),
                            add in any::<$t>(),
                        ) {
                            let (mx, my) = (x.inject(), y.inject());
                            prop_assert_eq!(super::$t::widening_mul(mx, my), x.widening_mul(y));
                            prop_assert_eq!(
                                super::$t::carrying_mul(mx, my, carry.inject()),
                                x.carrying_mul(y, carry),
                            );
                            prop_assert_eq!(
                                super::$t::carrying_mul_add(mx, my, carry.inject(), add.inject()),
                                x.carrying_mul_add(y, carry, add),
                            );
                        }

                        #[test]
                        fn [<test_ $t _carrying_ops>](x in any::<$t>(), y in any::<$t>(), c in any::<bool>()) {
                            prop_assert_eq!(super::$t::carrying_add(x.inject(), y.inject(), c), x.carrying_add(y, c));
                            prop_assert_eq!(super::$t::borrowing_sub(x.inject(), y.inject(), c), x.borrowing_sub(y, c));
                        }

                        // `shr_exact` has no counterpart on the pinned toolchain, so the
                        // expected value is spelled out from its documented behaviour.
                        #[test]
                        fn [<test_ $t _shr_exact>](x in any::<$t>(), n in 0u32..=(2 * $t::BITS)) {
                            let expected = if n <= x.trailing_zeros() && n < $t::BITS {
                                Some(x >> n)
                            } else {
                                None
                            };
                            prop_assert_eq!(super::$t::shr_exact(x.inject(), n), expected.inject());
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
                        }

                        #[test]
                        fn [<test_ $t _next_multiple_of>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(x.checked_next_multiple_of(y).is_some());
                            prop_assert_eq!(super::$t::next_multiple_of(x.inject(), y.inject()), x.next_multiple_of(y));
                        }

                        #[test]
                        fn [<test_ $t _bit_width>](x in any::<$t>()) {
                            prop_assert_eq!(super::$t::bit_width(x.inject()), x.bit_width());
                        }

                        #[test]
                        fn [<test_ $t _next_power_of_two_family>](x in any::<$t>()) {
                            let mx = x.inject();
                            prop_assert_eq!(
                                super::$t::checked_next_power_of_two(mx),
                                x.checked_next_power_of_two().inject(),
                            );
                            prop_assert_eq!(
                                super::$t::wrapping_next_power_of_two(mx),
                                x.wrapping_next_power_of_two(),
                            );
                            if x.checked_next_power_of_two().is_some() {
                                prop_assert_eq!(super::$t::next_power_of_two(mx), x.next_power_of_two());
                            }
                        }

                        #[test]
                        fn [<test_ $t _funnel_shifts>](x in any::<$t>(), y in any::<$t>(), n in 0u32..$t::BITS) {
                            prop_assert_eq!(super::$t::funnel_shl(x.inject(), y.inject(), n), x.funnel_shl(y, n));
                            prop_assert_eq!(super::$t::funnel_shr(x.inject(), y.inject(), n), x.funnel_shr(y, n));
                        }

                        // Clear `y`'s bits wherever `x` has one, so the two are disjoint.
                        #[test]
                        fn [<test_ $t _unchecked_disjoint_bitor>](x in any::<$t>(), y in any::<$t>()) {
                            let y = y & !x;
                            prop_assert_eq!(
                                unsafe { super::$t::unchecked_disjoint_bitor(x.inject(), y.inject()) },
                                unsafe { x.unchecked_disjoint_bitor(y) },
                            );
                        }

                        // `shl_exact` has no counterpart on the pinned toolchain, so the
                        // expected value is spelled out from its documented behaviour.
                        #[test]
                        fn [<test_ $t _shl_exact>](x in any::<$t>(), n in 0u32..=(2 * $t::BITS)) {
                            let expected = if n <= x.leading_zeros() && n < $t::BITS {
                                Some(x << n)
                            } else {
                                None
                            };
                            prop_assert_eq!(super::$t::shl_exact(x.inject(), n), expected.inject());
                        }

                        #[test]
                        fn [<test_ $t _unchecked_shl_exact>](x in any::<$t>(), n in 0u32..$t::BITS) {
                            // Clamp rather than reject: random values have few leading
                            // zeros, so rejection sampling would starve.
                            let n = n.min(x.leading_zeros()).min($t::BITS - 1);
                            prop_assert_eq!(
                                unsafe { super::$t::unchecked_shl_exact(x.inject(), n) },
                                x << n);
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

                        #[test]
                        fn [<test_ $t _next_multiple_of>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(x.checked_next_multiple_of(y).is_some());
                            prop_assert_eq!(super::$t::next_multiple_of(x.inject(), y.inject()), x.next_multiple_of(y));
                        }

                        // `shl_exact` has no counterpart on the pinned toolchain, so the
                        // expected value is spelled out from its documented behaviour: a
                        // signed left shift is exact while it keeps the sign bit's run.
                        #[test]
                        fn [<test_ $t _shl_exact>](x in any::<$t>(), n in 0u32..=(2 * $t::BITS)) {
                            let expected = if (n < x.leading_zeros() || n < x.leading_ones()) && n < $t::BITS {
                                Some(x << n)
                            } else {
                                None
                            };
                            prop_assert_eq!(super::$t::shl_exact(x.inject(), n), expected.inject());
                        }

                        #[test]
                        fn [<test_ $t _unchecked_shl_exact>](x in any::<$t>(), n in 0u32..$t::BITS) {
                            // Clamp rather than reject: the run of sign bits is short for
                            // most values, so rejection sampling would starve. One of the
                            // two counts is always at least 1, so `bound - 1` is valid.
                            let bound = x.leading_zeros().max(x.leading_ones());
                            let n = if n >= bound { bound - 1 } else { n };
                            prop_assert_eq!(
                                unsafe { super::$t::unchecked_shl_exact(x.inject(), n) },
                                x << n);
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

                        #[test]
                        fn [<test_ $t _unchecked_shifts>](x in any::<$t>(), n in 0u32..$t::BITS) {
                            prop_assert_eq!(
                                unsafe { super::$t::unchecked_shl(x.inject(), n) },
                                unsafe { x.unchecked_shl(n) });
                            prop_assert_eq!(
                                unsafe { super::$t::unchecked_shr(x.inject(), n) },
                                unsafe { x.unchecked_shr(n) });
                        }

                        // No `unchecked_sh{l,r}_exact` in std on the pinned toolchain;
                        // under their preconditions the plain shifts stand in. `n` is
                        // taken from the shift counts the precondition allows.
                        #[test]
                        fn [<test_ $t _unchecked_shr_exact>](x in any::<$t>(), n in 0u32..$t::BITS) {
                            // Clamp rather than reject: random values have few trailing
                            // zeros, so rejection sampling would starve.
                            let n = n.min(x.trailing_zeros()).min($t::BITS - 1);
                            prop_assert_eq!(
                                unsafe { super::$t::unchecked_shr_exact(x.inject(), n) },
                                x >> n);
                        }

                        #[test]
                        fn [<test_ $t _unchecked_div_exact>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(y > 0);
                            // Round `x` down to a multiple of `y`: exact divisions are far
                            // too rare among random pairs to reach by rejection.
                            let x = x - x % y;
                            prop_assert_eq!(
                                unsafe { super::$t::unchecked_div_exact(x.inject(), y.inject()) },
                                unsafe { x.unchecked_div_exact(y) });
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
                        crate::testing::panics_like_core(|| super::$t::div_exact(mx, my), || x.div_exact(y));
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
                        crate::testing::panics_like_core(|| super::$t::div_exact(mx, my), || x.div_exact(y));
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

    // The signed `next_multiple_of` panics on a zero divisor and on overflow, and
    // `MAX.next_multiple_of(2)` is the smallest overflowing case at every width.
    macro_rules! iint_next_multiple_of_panic_test {
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
                        let (x, y) = (std::hint::black_box(<$t>::MAX), std::hint::black_box(2 as $t));
                        crate::testing::panics_like_core(
                            || super::$t::next_multiple_of(x.inject(), y.inject()),
                            || x.next_multiple_of(y),
                        );
                    }
                )*
            }
        }
    }
    iint_next_multiple_of_panic_test! { i8 i16 i32 i64 i128 isize }

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

    // A shift count of exactly `BITS` is the first one that overflows.
    macro_rules! strict_shift_panic_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $t _strict_shl_overflow_panics>]() {
                        let (x, n) = (std::hint::black_box(1 as $t), std::hint::black_box($t::BITS));
                        crate::testing::panics_like_core(
                            || super::$t::strict_shl(x.inject(), n),
                            || x.strict_shl(n),
                        );
                    }
                    #[test]
                    fn [<test_ $t _strict_shr_overflow_panics>]() {
                        let (x, n) = (std::hint::black_box(1 as $t), std::hint::black_box($t::BITS));
                        crate::testing::panics_like_core(
                            || super::$t::strict_shr(x.inject(), n),
                            || x.strict_shr(n),
                        );
                    }
                )*
            }
        }
    }
    strict_shift_panic_test! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

    // `next_power_of_two` panics when no next power of two is representable.
    macro_rules! next_power_of_two_panic_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $t _next_power_of_two_overflow_panics>]() {
                        let x = std::hint::black_box(<$t>::MAX);
                        crate::testing::panics_like_core(
                            || super::$t::next_power_of_two(x.inject()),
                            || x.next_power_of_two(),
                        );
                    }
                )*
            }
        }
    }
    next_power_of_two_panic_test! { u8 u16 u32 u64 u128 usize }

    int_test! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }
    unchecked_test! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }
    uint_test! { u8 u16 u32 u64 u128 usize }
    iint_test! { i8 i16 i32 i64 i128 isize }
    iint_mixed_test! { (i8, u8) (i16, u16) (i32, u32) (i64, u64) (i128, u128) (isize, usize) }
    uint_mixed_test! { (u8, i8) (u16, i16) (u32, i32) (u64, i64) (u128, i128) (usize, isize) }

    // `core` puts this on `u16` only.
    proptest! {
        #[test]
        fn test_u16_is_utf16_surrogate(x in any::<u16>()) {
            prop_assert_eq!(super::u16::is_utf16_surrogate(x), x.is_utf16_surrogate());
        }
    }

    // `core` puts these on `u8` only.
    proptest! {
        #[test]
        fn test_u8_ascii_predicates(x in any::<u8>()) {
            prop_assert_eq!(super::u8::is_ascii(&x), x.is_ascii());
            prop_assert_eq!(super::u8::is_ascii_uppercase(&x), x.is_ascii_uppercase());
            prop_assert_eq!(super::u8::is_ascii_lowercase(&x), x.is_ascii_lowercase());
            prop_assert_eq!(super::u8::is_ascii_alphabetic(&x), x.is_ascii_alphabetic());
            prop_assert_eq!(super::u8::is_ascii_digit(&x), x.is_ascii_digit());
            prop_assert_eq!(super::u8::is_ascii_octdigit(&x), x.is_ascii_octdigit());
            prop_assert_eq!(super::u8::is_ascii_hexdigit(&x), x.is_ascii_hexdigit());
            prop_assert_eq!(super::u8::is_ascii_alphanumeric(&x), x.is_ascii_alphanumeric());
            prop_assert_eq!(super::u8::is_ascii_punctuation(&x), x.is_ascii_punctuation());
            prop_assert_eq!(super::u8::is_ascii_graphic(&x), x.is_ascii_graphic());
            prop_assert_eq!(super::u8::is_ascii_whitespace(&x), x.is_ascii_whitespace());
            prop_assert_eq!(super::u8::is_ascii_control(&x), x.is_ascii_control());
        }

        #[test]
        fn test_u8_ascii_case_conversion(x in any::<u8>(), y in any::<u8>()) {
            prop_assert_eq!(super::u8::to_ascii_uppercase(&x), x.to_ascii_uppercase());
            prop_assert_eq!(super::u8::to_ascii_lowercase(&x), x.to_ascii_lowercase());
            prop_assert_eq!(super::u8::eq_ignore_ascii_case(&x, &y), x.eq_ignore_ascii_case(&y));

            let (mut model, mut std) = (x, x);
            super::u8::make_ascii_uppercase(&mut model);
            std.make_ascii_uppercase();
            prop_assert_eq!(model, std);

            let (mut model, mut std) = (x, x);
            super::u8::make_ascii_lowercase(&mut model);
            std.make_ascii_lowercase();
            prop_assert_eq!(model, std);
        }
    }

    // `Wrapping<T>`/`Saturating<T>`: the width-independent methods, then the
    // unsigned-only and signed-only extras.
    macro_rules! wrapper_common_test {
        ($wrap: ident, $($t: ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $wrap:lower _ $t _consts>]() {
                        assert_eq!(super::$wrap::<$t>::MIN, std::num::$wrap(<$t>::MIN).inject());
                        assert_eq!(super::$wrap::<$t>::MAX, std::num::$wrap(<$t>::MAX).inject());
                        assert_eq!(super::$wrap::<$t>::BITS, <std::num::$wrap<$t>>::BITS);
                    }

                    proptest! {
                        #[test]
                        fn [<test_ $wrap:lower _ $t _common>](
                            x in any::<$t>(),
                            n in 0u32..$t::BITS,
                            exp in 0u32..=8,
                        ) {
                            let (m, s) = (super::$wrap(x), std::num::$wrap(x));
                            prop_assert_eq!(m.count_ones(), s.count_ones());
                            prop_assert_eq!(m.count_zeros(), s.count_zeros());
                            prop_assert_eq!(m.trailing_zeros(), s.trailing_zeros());
                            prop_assert_eq!(m.leading_zeros(), s.leading_zeros());
                            prop_assert_eq!(m.rotate_left(n), s.rotate_left(n).inject());
                            prop_assert_eq!(m.rotate_right(n), s.rotate_right(n).inject());
                            prop_assert_eq!(m.reverse_bits(), s.reverse_bits().inject());
                            prop_assert_eq!(m.swap_bytes(), s.swap_bytes().inject());
                            prop_assert_eq!(m.to_be(), s.to_be().inject());
                            prop_assert_eq!(m.to_le(), s.to_le().inject());
                            prop_assert_eq!(
                                <super::$wrap<$t>>::from_be(m),
                                <std::num::$wrap<$t>>::from_be(s).inject(),
                            );
                            prop_assert_eq!(
                                <super::$wrap<$t>>::from_le(m),
                                <std::num::$wrap<$t>>::from_le(s).inject(),
                            );
                            prop_assert_eq!(m.reverse_bits(), s.reverse_bits().inject());
                            prop_assert_eq!(m.pow(exp), s.pow(exp).inject());
                        }
                    }
                )*
            }
        }
    }
    wrapper_common_test! { Wrapping, u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }
    wrapper_common_test! { Saturating, u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

    macro_rules! wrapper_uint_test {
        ($($t: ty)*) => {
            paste! {
                $(
                    proptest! {
                        #[test]
                        fn [<test_wrapping_ $t _unsigned>](x in any::<$t>()) {
                            let (m, s) = (super::Wrapping(x), std::num::Wrapping(x));
                            prop_assert_eq!(m.is_power_of_two(), s.is_power_of_two());
                            prop_assert_eq!(m.next_power_of_two(), s.next_power_of_two().inject());
                        }

                        #[test]
                        fn [<test_saturating_ $t _unsigned>](x in any::<$t>()) {
                            prop_assert_eq!(
                                super::Saturating(x).is_power_of_two(),
                                std::num::Saturating(x).is_power_of_two(),
                            );
                        }
                    }
                )*
            }
        }
    }
    wrapper_uint_test! { u8 u16 u32 u64 u128 usize }

    macro_rules! wrapper_iint_test {
        ($($t: ty)*) => {
            paste! {
                $(
                    proptest! {
                        #[test]
                        fn [<test_wrapping_ $t _signed>](x in any::<$t>()) {
                            let (m, s) = (super::Wrapping(x), std::num::Wrapping(x));
                            prop_assert_eq!(m.abs(), s.abs().inject());
                            prop_assert_eq!(m.signum(), s.signum().inject());
                            prop_assert_eq!(m.is_positive(), s.is_positive());
                            prop_assert_eq!(m.is_negative(), s.is_negative());
                        }

                        #[test]
                        fn [<test_saturating_ $t _signed>](x in any::<$t>()) {
                            let (m, s) = (super::Saturating(x), std::num::Saturating(x));
                            prop_assert_eq!(m.abs(), s.abs().inject());
                            prop_assert_eq!(m.signum(), s.signum().inject());
                            prop_assert_eq!(m.is_positive(), s.is_positive());
                            prop_assert_eq!(m.is_negative(), s.is_negative());
                        }
                    }
                )*
            }
        }
    }
    wrapper_iint_test! { i8 i16 i32 i64 i128 isize }

    // `NonZero<T>`: the width-independent methods, then the unsigned-only and
    // signed-only extras. Random values are nudged away from zero rather than
    // rejected so the domain is not thinned out.
    macro_rules! nonzero_common_test {
        ($($t: ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_nonzero_ $t _consts>]() {
                        assert_eq!(<super::NonZero<$t>>::BITS, <std::num::NonZero<$t>>::BITS);
                        assert_eq!(<super::NonZero<$t>>::MIN, <std::num::NonZero<$t>>::MIN.inject());
                        assert_eq!(<super::NonZero<$t>>::MAX, <std::num::NonZero<$t>>::MAX.inject());
                    }

                    proptest! {
                        #[test]
                        fn [<test_nonzero_ $t _new>](x in any::<$t>()) {
                            prop_assert_eq!(
                                <super::NonZero<$t>>::new(x),
                                std::num::NonZero::new(x).inject(),
                            );
                        }

                        #[test]
                        fn [<test_nonzero_ $t _common>](
                            x in any::<$t>(),
                            y in any::<$t>(),
                            n in 0u32..$t::BITS,
                            exp in 0u32..=8,
                        ) {
                            let x = if x == 0 { 1 } else { x };
                            let y = if y == 0 { 1 } else { y };
                            let (m, s) = (super::NonZero(x), std::num::NonZero::new(x).unwrap());
                            let (mo, so) = (super::NonZero(y), std::num::NonZero::new(y).unwrap());
                            prop_assert_eq!(m.get(), s.get());
                            prop_assert_eq!(
                                unsafe { <super::NonZero<$t>>::new_unchecked(x) },
                                unsafe { std::num::NonZero::new_unchecked(x) }.inject(),
                            );
                            prop_assert_eq!(m.leading_zeros(), s.leading_zeros());
                            prop_assert_eq!(m.trailing_zeros(), s.trailing_zeros());
                            prop_assert_eq!(m.lowest_one(), s.lowest_one());
                            prop_assert_eq!(m.count_ones(), s.count_ones().inject());
                            prop_assert_eq!(m.isolate_highest_one(), s.isolate_highest_one().inject());
                            prop_assert_eq!(m.isolate_lowest_one(), s.isolate_lowest_one().inject());
                            prop_assert_eq!(m.rotate_left(n), s.rotate_left(n).inject());
                            prop_assert_eq!(m.rotate_right(n), s.rotate_right(n).inject());
                            prop_assert_eq!(m.reverse_bits(), s.reverse_bits().inject());
                            prop_assert_eq!(m.swap_bytes(), s.swap_bytes().inject());
                            prop_assert_eq!(m.to_be(), s.to_be().inject());
                            prop_assert_eq!(m.to_le(), s.to_le().inject());
                            prop_assert_eq!(
                                <super::NonZero<$t>>::from_be(m),
                                <std::num::NonZero<$t>>::from_be(s).inject(),
                            );
                            prop_assert_eq!(
                                <super::NonZero<$t>>::from_le(m),
                                <std::num::NonZero<$t>>::from_le(s).inject(),
                            );
                            prop_assert_eq!(m.checked_mul(mo), s.checked_mul(so).inject());
                            prop_assert_eq!(m.saturating_mul(mo), s.saturating_mul(so).inject());
                            prop_assert_eq!(m.checked_pow(exp), s.checked_pow(exp).inject());
                            prop_assert_eq!(m.saturating_pow(exp), s.saturating_pow(exp).inject());
                            if s.checked_mul(so).is_some() {
                                prop_assert_eq!(
                                    unsafe { m.unchecked_mul(mo) },
                                    unsafe { s.unchecked_mul(so) }.inject(),
                                );
                            }
                        }
                    }
                )*
            }
        }
    }
    nonzero_common_test! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

    macro_rules! nonzero_uint_test {
        ($($t: ty)*) => {
            paste! {
                $(
                    proptest! {
                        #[test]
                        fn [<test_nonzero_ $t _unsigned>](x in any::<$t>(), y in any::<$t>()) {
                            let x = if x == 0 { 1 } else { x };
                            let y = if y == 0 { 1 } else { y };
                            let (m, s) = (super::NonZero(x), std::num::NonZero::new(x).unwrap());
                            let (mo, so) = (super::NonZero(y), std::num::NonZero::new(y).unwrap());
                            prop_assert_eq!(m.highest_one(), s.highest_one());
                            prop_assert_eq!(m.ilog2(), s.ilog2());
                            // `NonZero::bit_width` does not exist on the pinned toolchain;
                            // the integer one does, and `NonZero`'s only wraps it.
                            prop_assert_eq!(m.bit_width(), super::NonZero(x.bit_width()));
                            prop_assert_eq!(m.checked_add(y), s.checked_add(y).inject());
                            prop_assert_eq!(m.saturating_add(y), s.saturating_add(y).inject());
                            prop_assert_eq!(
                                m.checked_next_power_of_two(),
                                s.checked_next_power_of_two().inject(),
                            );
                            prop_assert_eq!(m.midpoint(mo), s.midpoint(so).inject());
                            prop_assert_eq!(m.is_power_of_two(), s.is_power_of_two());
                            prop_assert_eq!(m.cast_signed(), s.cast_signed().inject());
                            prop_assert_eq!(m.div_ceil(mo), s.div_ceil(so).inject());
                            if s.checked_add(y).is_some() {
                                prop_assert_eq!(
                                    unsafe { m.unchecked_add(y) },
                                    unsafe { s.unchecked_add(y) }.inject(),
                                );
                            }
                        }
                    }
                )*
            }
        }
    }
    nonzero_uint_test! { u8 u16 u32 u64 u128 usize }

    macro_rules! nonzero_iint_test {
        ($($t: ty)*) => {
            paste! {
                $(
                    proptest! {
                        #[test]
                        fn [<test_nonzero_ $t _signed>](x in any::<$t>()) {
                            let x = if x == 0 { 1 } else { x };
                            let (m, s) = (super::NonZero(x), std::num::NonZero::new(x).unwrap());
                            prop_assert_eq!(m.highest_one(), s.highest_one());
                            prop_assert_eq!(m.checked_abs(), s.checked_abs().inject());
                            prop_assert_eq!(m.overflowing_abs(), s.overflowing_abs().inject());
                            prop_assert_eq!(m.saturating_abs(), s.saturating_abs().inject());
                            prop_assert_eq!(m.wrapping_abs(), s.wrapping_abs().inject());
                            prop_assert_eq!(m.unsigned_abs(), s.unsigned_abs().inject());
                            prop_assert_eq!(m.is_positive(), s.is_positive());
                            prop_assert_eq!(m.is_negative(), s.is_negative());
                            prop_assert_eq!(m.checked_neg(), s.checked_neg().inject());
                            prop_assert_eq!(m.overflowing_neg(), s.overflowing_neg().inject());
                            prop_assert_eq!(m.saturating_neg(), s.saturating_neg().inject());
                            prop_assert_eq!(m.wrapping_neg(), s.wrapping_neg().inject());
                            prop_assert_eq!(m.cast_unsigned(), s.cast_unsigned().inject());
                            if x != $t::MIN {
                                prop_assert_eq!(m.abs(), s.abs().inject());
                            }
                        }
                    }

                    #[test]
                    fn [<test_nonzero_ $t _abs_min_panics>]() {
                        let x = std::hint::black_box(<$t>::MIN);
                        let s = std::num::NonZero::new(x).unwrap();
                        crate::testing::panics_like_core(
                            || super::NonZero(x).abs(),
                            || s.abs(),
                        );
                    }
                )*
            }
        }
    }
    nonzero_iint_test! { i8 i16 i32 i64 i128 isize }

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
