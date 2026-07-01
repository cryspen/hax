/// See [`std::borrow::Borrow`]
trait Borrow<Borrowed> {
    /// See [`std::borrow::Borrow::borrow`]
    fn borrow(&self) -> Borrowed;
}
