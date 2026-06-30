use super::clone::Clone;

/// See [`std::marker::Copy`]
pub trait Copy: Clone {}
/// See [`std::marker::Send`]
pub trait Send {}
/// See [`std::marker::Sync`]
pub trait Sync {}
/// See [`std::marker::Sized`]
pub trait Sized {}
/// See [`std::marker::StructuralPartialEq`]
pub trait StructuralPartialEq {}

// In our models, all types implement those marker traits
impl<T> Send for T {}
impl<T> Sync for T {}
impl<T> Sized for T {}
#[cfg(hax)]
impl<T: Clone> Copy for T {}

macro_rules! copy_impl_for_int {
    ($($t:ty),*) => {
        $(
            impl Copy for $t {}
        )*
    };
}

#[cfg(not(hax))]
copy_impl_for_int!(
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

/// See [`std::marker::PhantomData`]
#[hax_lib::fstar::replace("type t_PhantomData (v_T: Type0) = | PhantomData : t_PhantomData v_T")]
#[hax_lib::lean::replace("structure PhantomData (T : Type) where")]
struct PhantomData<T>(T);
