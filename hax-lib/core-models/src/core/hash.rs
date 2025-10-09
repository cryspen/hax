pub trait Hasher {}

pub trait Hash {
    fn hash<H: Hasher>(&self, h: H) -> H;
}
