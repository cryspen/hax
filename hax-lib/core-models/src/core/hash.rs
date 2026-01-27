pub trait Hasher {}

#[hax_lib::attributes]
pub trait Hash {
    #[hax_lib::requires(true)]
    fn hash<H: Hasher>(&self, h: H) -> H;
}

// Temporary
impl<T> Hash for T {
    fn hash<H: Hasher>(&self, h: H) -> H {
        crate::panicking::internal::panic()
    }
}
