pub trait Copy: Clone {}
pub trait Send {}
pub trait Sync {}
pub trait Sized {}
pub trait StructuralPartialEq {}

// In our models, all types implement those marker traits
impl<T> Send for T {}
impl<T> Sync for T {}
impl<T> Sized for T {}
#[hax_lib::fstar::after("type t_PhantomData (v_T: Type0) = | PhantomData : t_PhantomData v_T")]
impl<T: Clone> Copy for T {}
