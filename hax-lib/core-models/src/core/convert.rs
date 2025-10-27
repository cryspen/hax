use super::result::Result;

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

pub struct Infallible;

impl<T, U: From<T>> TryFrom<T> for U {
    type Error = Infallible;
    fn try_from(x: T) -> Result<Self, Self::Error> {
        Result::Ok(U::from(x))
    }
}

// TODO: reimplement that in Rust when arrays and slices are added to core models
#[hax_lib::fstar::after("
instance impl_slice_try_into_array_refined (t: Type0) (len: usize): t_TryInto (s: t_Slice t) (t_Array t len) = {
  f_Error = Core_models.Array.t_TryFromSliceError;
  f_try_into_pre = (fun (s: t_Slice t) -> true);
  f_try_into_post = (fun (s: t_Slice t) (out: Core_models.Result.t_Result (t_Array t len) Core_models.Array.t_TryFromSliceError) -> true);
  f_try_into = (fun (s: t_Slice t) -> 
    if Core_models.Slice.impl__len s = len
    then Core_models.Result.Result_Ok (s <: t_Array t len)
    else Core_models.Result.Result_Err Core_models.Array.TryFromSliceError
  )
}
")]
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
