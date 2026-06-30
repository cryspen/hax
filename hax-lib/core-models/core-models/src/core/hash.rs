/// See [`std::hash::Hasher`]
pub trait Hasher {}

/// See [`std::hash::Hash`]
#[hax_lib::attributes]
pub trait Hash {
    /// See [`std::hash::Hash::hash`]
    #[hax_lib::requires(true)]
    fn hash<H: Hasher>(&self, h: H) -> H;
}

// Temporary
impl<T> Hash for T {
    fn hash<H: Hasher>(&self, h: H) -> H {
        crate::panicking::internal::panic()
    }
}
