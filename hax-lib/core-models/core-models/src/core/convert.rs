use super::result::Result;

/// See [`std::convert::TryInto`]
#[hax_lib::attributes]
trait TryInto<T> {
    type Error;
    /// See [`std::convert::TryInto::try_into`]
    #[hax_lib::requires(true)]
    fn try_into(self) -> Result<T, Self::Error>;
}

/// See [`std::convert::Into`]
#[hax_lib::attributes]
trait Into<T> {
    /// See [`std::convert::Into::into`]
    #[hax_lib::requires(true)]
    fn into(self) -> T;
}

/// See [`std::convert::From`]
#[hax_lib::attributes]
trait From<T> {
    /// See [`std::convert::From::from`]
    #[hax_lib::requires(true)]
    fn from(x: T) -> Self;
}

/// See [`std::convert::TryFrom`]
#[hax_lib::attributes]
pub trait TryFrom<T>: Sized {
    type Error;
    /// See [`std::convert::TryFrom::try_from`]
    #[hax_lib::requires(true)]
    fn try_from(x: T) -> Result<Self, Self::Error>;
}

impl<T, U: From<T>> Into<U> for T {
    fn into(self) -> U {
        U::from(self)
    }
}

/// See [`std::convert::Infallible`]
pub struct Infallible;

impl<T, U: From<T>> TryFrom<T> for U {
    type Error = Infallible;
    fn try_from(x: T) -> Result<Self, Self::Error> {
        Result::Ok(U::from(x))
    }
}

use crate::array::TryFromSliceError;
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
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

/// See [`std::convert::AsRef`]
#[hax_lib::attributes]
trait AsRef<T> {
    /// See [`std::convert::AsRef::as_ref`]
    #[hax_lib::requires(true)]
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
            #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
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
            #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
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

macro_rules! int_try_from_trivial {
    (
        $($From_t: ident)*,
        $($To_t: ident)*,
    ) => {
        $(
            #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
            impl TryFrom<$From_t> for $To_t {
                type Error = TryFromIntError;
                fn try_from(x: $From_t) -> Result<$To_t, TryFromIntError> {
                    Result::Ok(x as $To_t)
                }
            }
        )*
    }
}

int_from! {
    u8  u8  u16 u8  u16 u32 u8   u16  u32  u64  u8    u16,
    u16 u32 u32 u64 u64 u64 u128 u128 u128 u128 usize usize,
}

int_from! {
    i8  i8  i16 i8  i16 i32 i8   i16  i32  i64  i8    i16,
    i16 i32 i32 i64 i64 i64 i128 i128 i128 i128 isize isize,
}

int_from! {
    u8  u8  u8  u8   u8    u16 u16 u16  u32 u32  u64,
    i16 i32 i64 i128 isize i32 i64 i128 i64 i128 i128,
}

int_try_from! {
    u16 u32 u32 u64 u64 u64 u64   u128 u128 u128 u128 u128  usize usize usize usize,
    u8  u8  u16 u8  u16 u32 usize u8   u16  u32  u64  usize u8    u16   u32   u64,
}

int_try_from! {
    i16 i32 i32 i64 i64 i64 i64   i128 i128 i128 i128 i128  isize isize isize isize,
    i8  i8  i16 i8  i16 i32 isize i8   i16  i32  i64  isize i8    i16   i32   i64,
}

// We assume a 64-bits machine
int_try_from_trivial! {
    i32   isize u32   usize,
    isize i128  usize u128,
}

macro_rules! int_try_from_u_to_i {
    (
        $($From_t: ident)*,
        $($To_t: ident)*,
    ) => {
        $(
            #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
            impl TryFrom<$From_t> for $To_t {
                type Error = TryFromIntError;
                fn try_from(x: $From_t) -> Result<$To_t, TryFromIntError> {
                    if x > ($To_t::MAX as $From_t) {
                        Result::Err(TryFromIntError(()))
                    } else {
                        Result::Ok(x as $To_t)
                    }
                }
            }
        )*
    }
}

macro_rules! int_try_from_i_to_u {
    (
        $($From_t: ident)*,
        $($To_t: ident)*,
    ) => {
        $(
            #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
            impl TryFrom<$From_t> for $To_t {
                type Error = TryFromIntError;
                #[allow(unused_comparisons)]
                fn try_from(x: $From_t) -> Result<$To_t, TryFromIntError> {
                    if x < 0 || (x as u128) > ($To_t::MAX as u128) {
                        Result::Err(TryFromIntError(()))
                    } else {
                        Result::Ok(x as $To_t)
                    }
                }
            }
        )*
    }
}

int_try_from_u_to_i! {
    u8   u16 u16 u32 u32 u32 u64 u64 u64 u64  u128 u128 u128 u128 u128  usize usize usize usize usize,
    i8   i8  i16 i8  i16 i32 i8  i16 i32 i64  i8   i16  i32  i64  i128  i8    i16   i32   i64   isize,
}

int_try_from_i_to_u! {
    i8  i8  i8  i8  i8   i8    i16 i16 i16 i16 i16  i16   i32 i32 i32 i32 i32  i32   i64 i64 i64 i64 i64  i64   i128 i128 i128 i128 i128 i128  isize isize isize isize isize isize,
    u8  u16 u32 u64 u128 usize u8  u16 u32 u64 u128 usize u8  u16 u32 u64 u128 usize u8  u16 u32 u64 u128 usize u8   u16  u32  u64  u128 usize u8    u16   u32   u64   u128  usize,
}

#[cfg(test)]
mod tests {
    use crate::testing::Inject;
    use pastey::paste;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_from_identity(x in any::<u8>()) {
            prop_assert_eq!(<u8 as super::From<u8>>::from(x.inject()), x);
        }

        #[test]
        fn test_into_identity(x in any::<u8>()) {
            prop_assert_eq!(super::Into::<u8>::into(x.inject()), x);
        }

        #[test]
        fn test_as_ref_identity(x in any::<u8>()) {
            prop_assert_eq!(super::AsRef::as_ref(x.inject()), x);
        }
    }

    macro_rules! int_from_test {
            (
                $($From_t: ident)*,
                $($To_t: ident)*,
            ) => {
                paste!{
                    $(
                        proptest! {
                            #[test]
                            fn [<test_from_$From_t _to_ $To_t>](x in any::<$From_t>()) {
                                prop_assert_eq!(<$To_t as super::From<$From_t>>::from(x.inject()), x.into());
                            }
                        }
                    )*
                }
            }
        }

    macro_rules! int_try_from_test {
            (
                $($From_t: ident)*,
                $($To_t: ident)*,
            ) => {
                paste!{
                    $(
                        proptest!{
                            #[test]
                            fn [<test_try_from_$From_t _to_ $To_t>](x in any::<$From_t>()) {
                                prop_assert_eq!(
                                    <$To_t as super::TryFrom<$From_t>>::try_from(x.inject()),
                                    $To_t::try_from(x).inject()
                                );
                            }
                        }
                    )*
                }
            }
        }

    int_from_test! {
        u8  u8  u16 u8  u16 u32 u8   u16  u32  u64  u8    u16,
        u16 u32 u32 u64 u64 u64 u128 u128 u128 u128 usize usize,
    }

    int_from_test! {
        i8  i8  i16 i8  i16 i32 i8   i16  i32  i64  i8    i16,
        i16 i32 i32 i64 i64 i64 i128 i128 i128 i128 isize isize,
    }

    int_from_test! {
        u8  u8  u8  u8   u8    u16 u16 u16  u32 u32  u64,
        i16 i32 i64 i128 isize i32 i64 i128 i64 i128 i128,
    }

    int_try_from_test! {
        u16 u32 u32 u32   u64 u64 u64 u64   u128 u128 u128 u128 u128  usize usize usize usize usize,
        u8  u8  u16 usize u8  u16 u32 usize u8   u16  u32  u64  usize u8    u16   u32   u64   u128,
    }

    int_try_from_test! {
        i16 i32 i32 i32   i64 i64 i64 i64   i128 i128 i128 i128 i128  isize isize isize isize isize,
        i8  i8  i16 isize i8  i16 i32 isize i8   i16  i32  i64  isize i8    i16   i32   i64   i128,
    }

    int_try_from_test! {
        u8   u16 u16 u32 u32 u32 u64 u64 u64 u64  u128 u128 u128 u128 u128  usize usize usize usize usize,
        i8   i8  i16 i8  i16 i32 i8  i16 i32 i64  i8   i16  i32  i64  i128  i8    i16   i32   i64   isize,
    }

    int_try_from_test! {
        i8  i8  i8  i8  i8   i8    i16 i16 i16 i16 i16  i16   i32 i32 i32 i32 i32  i32   i64 i64 i64 i64 i64  i64   i128 i128 i128 i128 i128 i128  isize isize isize isize isize isize,
        u8  u16 u32 u64 u128 usize u8  u16 u32 u64 u128 usize u8  u16 u32 u64 u128 usize u8  u16 u32 u64 u128 usize u8   u16  u32  u64  u128 usize u8    u16   u32   u64   u128  usize,
    }

    proptest! {
        #[test]
        fn test_try_from_slice_to_array_success(arr in any::<[u8; 4]>()) {
            prop_assert_eq!(
                <[u8; 4] as super::TryFrom<&[u8]>>::try_from(arr.as_slice()).unwrap(),
                arr
            );
        }

        #[test]
        fn test_try_from_slice_to_array_length_mismatch(arr in any::<[u8; 3]>()) {
            let result = <[u8; 4] as super::TryFrom<&[u8]>>::try_from(arr.as_slice());
            prop_assert!(result.is_err());
        }
    }
}
