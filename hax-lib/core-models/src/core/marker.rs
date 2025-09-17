pub trait Copy: Clone {}
pub trait Send {}
pub trait Sync {}
pub trait Sized {}
pub trait StructuralPartialEq {}

// In our models, all types implement those marker traits
impl<T> Send for T {}
impl<T> Sync for T {}
impl<T> Sized for T {}
