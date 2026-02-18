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
impl<T: Clone> Copy for T {}

/// See [`std::marker::PhantomData`]
#[hax_lib::fstar::replace("type t_PhantomData (v_T: Type0) = | PhantomData : t_PhantomData v_T")]
#[hax_lib::lean::replace("structure PhantomData (T : Type) where")]
struct PhantomData<T>(T);
