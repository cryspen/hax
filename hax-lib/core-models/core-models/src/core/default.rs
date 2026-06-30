/// See [`std::default::Default`]
#[hax_lib::attributes]
pub trait Default {
    /// See [`std::default::Default::default`]
    #[hax_lib::requires(true)]
    fn default() -> Self;
}
