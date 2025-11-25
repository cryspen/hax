use super::result::Result;

pub enum Infallible {}

#[hax_lib::attributes]
trait TryInto<T> {
    type Error;
    #[hax_lib::requires(true)]
    fn try_into(self) -> Result<T, Self::Error>;
}

#[hax_lib::attributes]
trait Into<T> {
    #[hax_lib::requires(true)]
    fn into(self) -> T;
}

#[hax_lib::attributes]
trait From<T> {
    #[hax_lib::requires(true)]
    fn from(x: T) -> Self;
}

#[hax_lib::attributes]
trait TryFrom<T>: Sized {
    type Error;
    #[hax_lib::requires(true)]
    fn try_from(x: T) -> Result<Self, Self::Error>;
}

impl<T, U: From<T>> Into<U> for T {
    fn into(self) -> U {
        U::from(self)
    }
}

impl<T, U: From<T>> TryFrom<T> for U {
    type Error = Infallible;
    fn try_from(x: T) -> Result<Self, Self::Error> {
        Result::Ok(U::from(x))
    }
}

use crate::array::TryFromSliceError;
impl<T: Copy, const N: usize> TryFrom<&[T]> for [T; N] {
    type Error = TryFromSliceError;
    fn try_from(x: &[T]) -> Result<[T; N], TryFromSliceError> {
        if x.len() == N {
            Result::Ok(rust_primitives::slice::array_from_fn(|i| {
                *rust_primitives::slice::slice_index(x, i)
            }))
        } else {
            Result::Err(TryFromSliceError)
        }
    }
}

impl<T, U: TryFrom<T>> TryInto<U> for T {
    type Error = U::Error;
    fn try_into(self) -> Result<U, Self::Error> {
        U::try_from(self)
    }
}

impl<T> From<T> for T {
    fn from(x: T) -> Self {
        x
    }
}

trait AsRef<T> {
    fn as_ref(self) -> T;
}

impl<T> AsRef<T> for T {
    fn as_ref(self) -> T {
        self
    }
}

macro_rules! int_from {
    (
        $($From_t: ident)*,
        $($To_t: ident)*,
    ) => {
        $(
            impl From<$From_t> for $To_t {
                fn from(x: $From_t) -> $To_t {
                    x as $To_t
                }
            }
        )*
    }
}

use super::num::error::TryFromIntError;

macro_rules! int_try_from {
    (
        $($From_t: ident)*,
        $($To_t: ident)*,
    ) => {
        $(
            impl TryFrom<$From_t> for $To_t {
                type Error = TryFromIntError;
                fn try_from(x: $From_t) -> Result<$To_t, TryFromIntError> {
                    if x > ($To_t::MAX as $From_t) || x < ($To_t::MIN as $From_t) {
                        Result::Err(TryFromIntError(()))
                    } else {
                        Result::Ok(x as $To_t)
                    }
                }
            }
        )*
    }
}

int_from! {
    u8  u8  u16 u8  u16 u32 usize u8   u16  u32  u64  usize u8    u16   u32,
    u16 u32 u32 u64 u64 u64 u64   u128 u128 u128 u128 u128  usize usize usize,
}

int_from! {
    i8  i8  i16 i8  i16 i32 isize i8   i16  i32  i64  isize i8    i16   i32,
    i16 i32 i32 i64 i64 i64 i64   i128 i128 i128 i128 i128  isize isize isize,
}

int_try_from! {
    u16 u32 u32 u64 u64 u64 u64   u128 u128 u128 u128 u128  usize usize usize,
    u8  u8  u16 u8  u16 u32 usize u8   u16  u32  u64  usize u8    u16   u32,
}

int_try_from! {
    i16 i32 i32 i64 i64 i64 i64   i128 i128 i128 i128 i128  isize isize isize,
    i8  i8  i16 i8  i16 i32 isize i8   i16  i32  i64  isize i8    i16   i32,
}
