trait Hasher {}

trait Hash {
    fn hash<H: Hasher>(&self, h: H) -> H;
}
