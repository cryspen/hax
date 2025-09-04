#[hax_lib::attributes]
pub trait Default {
    #[hax_lib::requires(true)]
    fn default() -> Self;
}
