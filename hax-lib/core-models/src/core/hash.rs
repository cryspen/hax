trait Hasher {}

#[hax_lib::attributes]
trait Hash {
    #[hax_lib::requires(true)]
    fn hash<H: Hasher>(&self, h: H) -> H;
}
