#![allow(non_camel_case_types, unused_variables)]

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
            pub const MIN: $Self = 0;
            pub const MAX: $Self = $Max;
            pub const BITS: core::primitive::u32 = $Bits;
            fn wrapping_add(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_add_ $Name>](x, y) }
            }
            fn saturating_add(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_add_ $Name>](x, y) }
            }
            fn overflowing_add(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_add_ $Name>](x, y) }
            }
            fn checked_add(x: $Self, y: $Self) -> Option<$Self> {
                if Self::MIN.to_int() <= x.to_int() + y.to_int()
                    && x.to_int() + y.to_int() <= Self::MAX.to_int()
                {
                    Option::Some(x + y)
                } else {
                    Option::None
                }
            }
            fn wrapping_sub(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_sub_ $Name>](x, y) }
            }
            fn saturating_sub(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_sub_ $Name>](x, y) }
            }
            fn overflowing_sub(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_sub_ $Name>](x, y) }
            }
            fn checked_sub(x: $Self, y: $Self) -> Option<$Self> {
                if Self::MIN.to_int() <= x.to_int() - y.to_int()
                    && x.to_int() - y.to_int() <= Self::MAX.to_int()
                {
                    Option::Some(x - y)
                } else {
                    Option::None
                }
            }
            fn wrapping_mul(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_mul_ $Name>](x, y) }
            }
            fn saturating_mul(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_mul_ $Name>](x, y) }
            }
            fn overflowing_mul(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_mul_ $Name>](x, y) }
            }
            fn checked_mul(x: $Self, y: $Self) -> Option<$Self> {
                if Self::MIN.to_int() <= x.to_int() * y.to_int()
                    && x.to_int() * y.to_int() <= Self::MAX.to_int()
                {
                    Option::Some(x * y)
                } else {
                    Option::None
                }
            }
            #[hax_lib::requires(y != 0)]
            fn rem_euclid(x: $Self, y: $Self) -> $Self {
                paste! { [<rem_euclid_ $Name>](x, y) }
            }
            fn pow(x: $Self, exp: core::primitive::u32) -> $Self {
                paste! { [<pow_ $Name>](x, exp) }
            }
            fn count_ones(x: $Self) -> core::primitive::u32 {
                paste! { [<count_ones_ $Name>](x) }
            }
            #[hax_lib::opaque]
            fn rotate_right(x: $Self, n: core::primitive::u32) -> $Self {
                paste! { [<rotate_right_ $Name>](x, n) }
            }
            #[hax_lib::opaque]
            fn rotate_left(x: $Self, n: core::primitive::u32) -> $Self {
                paste! { [<rotate_left_ $Name>](x, n) }
            }
            #[hax_lib::opaque]
            fn leading_zeros(x: $Self) -> core::primitive::u32 {
                paste! { [<leading_zeros_ $Name>](x) }
            }
            #[hax_lib::opaque]
            fn ilog2(x: $Self) -> core::primitive::u32 {
                paste! { [<ilog2_ $Name>](x) }
            }
            #[hax_lib::opaque]
            fn from_str_radix(
                src: &str,
                radix: core::primitive::u32,
            ) -> Result<$Self, error::ParseIntError> {
                crate::panicking::internal::panic()
            }
            #[hax_lib::opaque]
            fn from_be_bytes(bytes: [core::primitive::u8; $Bytes]) -> $Self {
                paste! { [<from_be_bytes_ $Name>](bytes) }
            }
            #[hax_lib::opaque]
            fn from_le_bytes(bytes: [core::primitive::u8; $Bytes]) -> $Self {
                paste! { [<from_le_bytes_ $Name>](bytes) }
            }
            #[hax_lib::opaque]
            fn to_be_bytes(bytes: $Self) -> [core::primitive::u8; $Bytes] {
                paste! { [<to_be_bytes_ $Name>](bytes) }
            }
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
            pub const MIN: $Self = $Min;
            pub const MAX: $Self = $Max;
            pub const BITS: core::primitive::u32 = $Bits;
            fn wrapping_add(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_add_ $Name>](x, y) }
            }
            fn saturating_add(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_add_ $Name>](x, y) }
            }
            fn overflowing_add(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_add_ $Name>](x, y) }
            }
            fn checked_add(x: $Self, y: $Self) -> Option<$Self> {
                if Self::MIN.to_int() <= x.to_int() + y.to_int()
                    && x.to_int() + y.to_int() <= Self::MAX.to_int()
                {
                    Option::Some(x + y)
                } else {
                    Option::None
                }
            }
            fn wrapping_sub(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_sub_ $Name>](x, y) }
            }
            fn saturating_sub(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_sub_ $Name>](x, y) }
            }
            fn overflowing_sub(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_sub_ $Name>](x, y) }
            }
            fn checked_sub(x: $Self, y: $Self) -> Option<$Self> {
                if Self::MIN.to_int() <= x.to_int() - y.to_int()
                    && x.to_int() - y.to_int() <= Self::MAX.to_int()
                {
                    Option::Some(x - y)
                } else {
                    Option::None
                }
            }
            fn wrapping_mul(x: $Self, y: $Self) -> $Self {
                paste! { [<wrapping_mul_ $Name>](x, y) }
            }
            fn saturating_mul(x: $Self, y: $Self) -> $Self {
                paste! { [<saturating_mul_ $Name>](x, y) }
            }
            fn overflowing_mul(x: $Self, y: $Self) -> ($Self, bool) {
                paste! { [<overflowing_mul_ $Name>](x, y) }
            }
            fn checked_mul(x: $Self, y: $Self) -> Option<$Self> {
                if Self::MIN.to_int() <= x.to_int() * y.to_int()
                    && x.to_int() * y.to_int() <= Self::MAX.to_int()
                {
                    Option::Some(x * y)
                } else {
                    Option::None
                }
            }
            #[hax_lib::requires(y != 0)]
            fn rem_euclid(x: $Self, y: $Self) -> $Self {
                paste! { [<rem_euclid_ $Name>](x, y) }
            }
            fn pow(x: $Self, exp: core::primitive::u32) -> $Self {
                paste! { [<pow_ $Name>](x, exp) }
            }
            fn count_ones(x: $Self) -> core::primitive::u32 {
                paste! { [<count_ones_ $Name>](x) }
            }
            #[hax_lib::requires(x > $Self::MIN)]
            fn abs(x: $Self) -> $Self {
                paste! { [<abs_ $Name>](x) }
            }
            #[hax_lib::opaque]
            fn rotate_right(x: $Self, n: core::primitive::u32) -> $Self {
                paste! { [<rotate_right_ $Name>](x, n) }
            }
            #[hax_lib::opaque]
            fn rotate_left(x: $Self, n: core::primitive::u32) -> $Self {
                paste! { [<rotate_left_ $Name>](x, n) }
            }
            #[hax_lib::opaque]
            fn leading_zeros(x: $Self) -> core::primitive::u32 {
                paste! { [<leading_zeros_ $Name>](x) }
            }
            #[hax_lib::opaque]
            fn ilog2(x: $Self) -> core::primitive::u32 {
                paste! { [<ilog2_ $Name>](x) }
            }
            #[hax_lib::opaque]
            fn from_str_radix(
                src: &str,
                radix: core::primitive::u32,
            ) -> Result<$Self, error::ParseIntError> {
                crate::panicking::internal::panic()
            }
            #[hax_lib::opaque]
            fn from_be_bytes(bytes: [core::primitive::u8; $Bytes]) -> $Self {
                paste! { [<from_be_bytes_ $Name>](bytes) }
            }
            #[hax_lib::opaque]
            fn from_le_bytes(bytes: [core::primitive::u8; $Bytes]) -> $Self {
                paste! { [<from_le_bytes_ $Name>](bytes) }
            }
            #[hax_lib::opaque]
            fn to_be_bytes(bytes: $Self) -> [core::primitive::u8; $Bytes] {
                paste! { [<to_be_bytes_ $Name>](bytes) }
            }
            #[hax_lib::opaque]
            fn to_le_bytes(bytes: $Self) -> [core::primitive::u8; $Bytes] {
                paste! { [<to_le_bytes_ $Name>](bytes) }
            }
        }
    };
}

// These types are a trick to define impls on the right names as
// it is forbidden to do it on primitive types
#[hax_lib::exclude]
pub struct u8;
#[hax_lib::exclude]
pub struct u16;
#[hax_lib::exclude]
pub struct u32;
#[hax_lib::exclude]
pub struct u64;
#[hax_lib::exclude]
pub struct u128;
#[hax_lib::exclude]
pub struct usize;
#[hax_lib::exclude]
pub struct i8;
#[hax_lib::exclude]
pub struct i16;
#[hax_lib::exclude]
pub struct i32;
#[hax_lib::exclude]
pub struct i64;
#[hax_lib::exclude]
pub struct i128;
#[hax_lib::exclude]
pub struct isize;

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
