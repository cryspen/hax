#![allow(non_camel_case_types, unused_variables)]

use crate::result::Result;
use pastey::paste;

pub mod error;

use rust_primitives::arithmetic::*;

macro_rules! uint_impl {
    (
        $Self: ty,
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
            fn wrapping_add(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_add_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
            fn saturating_add(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_add_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
            fn overflowing_add(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_add_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
            fn checked_add(x: $Self, y: $Self) -> Option<$Self> {
                if Self::MIN.to_int() <= x.to_int() + y.to_int()
                    && x.to_int() + y.to_int() <= Self::MAX.to_int()
                {
                    Option::Some(x + y)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
            fn wrapping_sub(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_sub_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
            fn saturating_sub(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_sub_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
            fn overflowing_sub(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_sub_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
            fn checked_sub(x: $Self, y: $Self) -> Option<$Self> {
                if Self::MIN.to_int() <= x.to_int() - y.to_int()
                    && x.to_int() - y.to_int() <= Self::MAX.to_int()
                {
                    Option::Some(x - y)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
            fn wrapping_mul(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_mul_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
            fn saturating_mul(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_mul_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
            fn overflowing_mul(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_mul_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
            fn checked_mul(x: $Self, y: $Self) -> Option<$Self> {
                if Self::MIN.to_int() <= x.to_int() * y.to_int()
                    && x.to_int() * y.to_int() <= Self::MAX.to_int()
                {
                    Option::Some(x * y)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
            #[hax_lib::requires(y != 0)]
            fn rem_euclid(x: $Self, y: $Self) -> $Self {
                paste! { [<rem_euclid_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::pow`] (and similar for other integer types)
            fn pow(x: $Self, exp: core::primitive::u32) -> $Self {
                paste! { [<pow_ $Name>](x, exp) }
            }
            /// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
            fn count_ones(x: $Self) -> core::primitive::u32 {
                paste! { [<count_ones_ $Name>](x) }
            }
            /// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn rotate_right(x: $Self, n: core::primitive::u32) -> $Self {
                paste! { [<rotate_right_ $Name>](x, n) }
            }
            /// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn rotate_left(x: $Self, n: core::primitive::u32) -> $Self {
                paste! { [<rotate_left_ $Name>](x, n) }
            }
            /// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn leading_zeros(x: $Self) -> core::primitive::u32 {
                paste! { [<leading_zeros_ $Name>](x) }
            }
            /// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn ilog2(x: $Self) -> core::primitive::u32 {
                paste! { [<ilog2_ $Name>](x) }
            }
            /// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn from_str_radix(
                src: &str,
                radix: core::primitive::u32,
            ) -> Result<$Self, error::ParseIntError> {
                crate::panicking::internal::panic()
            }
            /// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn from_be_bytes(bytes: [core::primitive::u8; $Bytes]) -> $Self {
                paste! { [<from_be_bytes_ $Name>](bytes) }
            }
            /// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn from_le_bytes(bytes: [core::primitive::u8; $Bytes]) -> $Self {
                paste! { [<from_le_bytes_ $Name>](bytes) }
            }
            /// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn to_be_bytes(bytes: $Self) -> [core::primitive::u8; $Bytes] {
                paste! { [<to_be_bytes_ $Name>](bytes) }
            }
            /// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn to_le_bytes(bytes: $Self) -> [core::primitive::u8; $Bytes] {
                paste! { [<to_le_bytes_ $Name>](bytes) }
            }
        }
    };
}

use crate::option::Option;
use hax_lib::int::ToInt;

macro_rules! iint_impl {
    (
        $Self: ty,
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
            fn wrapping_add(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_add_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
            fn saturating_add(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_add_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
            fn overflowing_add(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_add_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
            fn checked_add(x: $Self, y: $Self) -> Option<$Self> {
                if Self::MIN.to_int() <= x.to_int() + y.to_int()
                    && x.to_int() + y.to_int() <= Self::MAX.to_int()
                {
                    Option::Some(x + y)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
            fn wrapping_sub(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_sub_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
            fn saturating_sub(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_sub_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
            fn overflowing_sub(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_sub_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
            fn checked_sub(x: $Self, y: $Self) -> Option<$Self> {
                if Self::MIN.to_int() <= x.to_int() - y.to_int()
                    && x.to_int() - y.to_int() <= Self::MAX.to_int()
                {
                    Option::Some(x - y)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
            fn wrapping_mul(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_mul_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
            fn saturating_mul(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_mul_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
            fn overflowing_mul(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_mul_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
            fn checked_mul(x: $Self, y: $Self) -> Option<$Self> {
                if Self::MIN.to_int() <= x.to_int() * y.to_int()
                    && x.to_int() * y.to_int() <= Self::MAX.to_int()
                {
                    Option::Some(x * y)
                } else {
                    Option::None
                }
            }
            /// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
            #[hax_lib::requires(y != 0)]
            fn rem_euclid(x: $Self, y: $Self) -> $Self {
                paste! { [<rem_euclid_ $Name>](x, y) }
            }
            /// See [`std::primitive::u8::pow`] (and similar for other integer types)
            fn pow(x: $Self, exp: core::primitive::u32) -> $Self {
                paste! { [<pow_ $Name>](x, exp) }
            }
            /// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
            fn count_ones(x: $Self) -> core::primitive::u32 {
                paste! { [<count_ones_ $Name>](x) }
            }
            /// See [`std::primitive::i8::abs`] (and similar for other signed integer types)
            #[hax_lib::requires(x > $Self::MIN)]
            fn abs(x: $Self) -> $Self {
                paste! { [<abs_ $Name>](x) }
            }
            /// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn rotate_right(x: $Self, n: core::primitive::u32) -> $Self {
                paste! { [<rotate_right_ $Name>](x, n) }
            }
            /// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn rotate_left(x: $Self, n: core::primitive::u32) -> $Self {
                paste! { [<rotate_left_ $Name>](x, n) }
            }
            /// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn leading_zeros(x: $Self) -> core::primitive::u32 {
                paste! { [<leading_zeros_ $Name>](x) }
            }
            /// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn ilog2(x: $Self) -> core::primitive::u32 {
                paste! { [<ilog2_ $Name>](x) }
            }
            /// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn from_str_radix(
                src: &str,
                radix: core::primitive::u32,
            ) -> Result<$Self, error::ParseIntError> {
                crate::panicking::internal::panic()
            }
            /// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn from_be_bytes(bytes: [core::primitive::u8; $Bytes]) -> $Self {
                paste! { [<from_be_bytes_ $Name>](bytes) }
            }
            /// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn from_le_bytes(bytes: [core::primitive::u8; $Bytes]) -> $Self {
                paste! { [<from_le_bytes_ $Name>](bytes) }
            }
            /// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn to_be_bytes(bytes: $Self) -> [core::primitive::u8; $Bytes] {
                paste! { [<to_be_bytes_ $Name>](bytes) }
            }
            /// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
            #[hax_lib::opaque]
            fn to_le_bytes(bytes: $Self) -> [core::primitive::u8; $Bytes] {
                paste! { [<to_le_bytes_ $Name>](bytes) }
            }
        }
    };
}

// These types are a trick to define impls on the right names as
// it is forbidden to do it on primitive types
/// See [`std::primitive::u8`]
#[hax_lib::exclude]
pub struct u8;
/// See [`std::primitive::u16`]
#[hax_lib::exclude]
pub struct u16;
/// See [`std::primitive::u32`]
#[hax_lib::exclude]
pub struct u32;
/// See [`std::primitive::u64`]
#[hax_lib::exclude]
pub struct u64;
/// See [`std::primitive::u128`]
#[hax_lib::exclude]
pub struct u128;
/// See [`std::primitive::usize`]
#[hax_lib::exclude]
pub struct usize;
/// See [`std::primitive::i8`]
#[hax_lib::exclude]
pub struct i8;
/// See [`std::primitive::i16`]
#[hax_lib::exclude]
pub struct i16;
/// See [`std::primitive::i32`]
#[hax_lib::exclude]
pub struct i32;
/// See [`std::primitive::i64`]
#[hax_lib::exclude]
pub struct i64;
/// See [`std::primitive::i128`]
#[hax_lib::exclude]
pub struct i128;
/// See [`std::primitive::isize`]
#[hax_lib::exclude]
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
    u8,
    255,
    8,
    1,
}

uint_impl! {
    core::primitive::u16,
    u16,
    65535,
    16,
    2,
}

uint_impl! {
    core::primitive::u32,
    u32,
    4294967295,
    32,
    4,
}

uint_impl! {
    core::primitive::u64,
    u64,
    18446744073709551615,
    64,
    8,
}

uint_impl! {
    core::primitive::u128,
    u128,
    340282366920938463463374607431768211455,
    128,
    16,
}

uint_impl! {
    core::primitive::usize,
    usize,
    USIZE_MAX,
    SIZE_BITS,
    SIZE_BYTES,
}

iint_impl! {
    core::primitive::i8,
    i8,
    127,
    -128,
    8,
    1,
}

iint_impl! {
    core::primitive::i16,
    i16,
    32767,
    -32768,
    16,
    2,
}

iint_impl! {
    core::primitive::i32,
    i32,
    2147483647,
    -2147483648,
    32,
    4,
}

iint_impl! {
    core::primitive::i64,
    i64,
    9223372036854775807,
    -9223372036854775808,
    64,
    8,
}

iint_impl! {
    core::primitive::i128,
    i128,
    170141183460469231731687303715884105727,
    -170141183460469231731687303715884105728,
    128,
    16,
}

iint_impl! {
    core::primitive::isize,
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
