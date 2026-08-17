/// See [`std::borrow::Borrow`]
trait Borrow<Borrowed> {
    /// See [`std::borrow::Borrow::borrow`]
    fn borrow(&self) -> Borrowed;
}

// Real core declares `BorrowMut<Borrowed>: Borrow<Borrowed>`. We drop the
// supertrait: the model's `Borrow::borrow` returns `Borrowed` by value, so the
// reflexive `Borrow<T> for T` real core provides is not writable here, and
// requiring it would leave `BorrowMut` uninhabited.
/// See [`std::borrow::BorrowMut`]
// Excluded from F*: hax rejects a `&mut` return (`HAX0003`/`HAX0010`), the same
// reason `Result::as_mut` is excluded. Aeneas handles it (back-and-forth
// functions), so the Lean side keeps the item.
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
trait BorrowMut<Borrowed> {
    /// See [`std::borrow::BorrowMut::borrow_mut`]
    fn borrow_mut(&mut self) -> &mut Borrowed;
}

#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
impl<T> BorrowMut<T> for T {
    fn borrow_mut(&mut self) -> &mut T {
        self
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    proptest! {
        // The reflexive `BorrowMut` hands back the value itself, and writes
        // through the returned reference land in the original.
        #[test]
        fn test_borrow_mut_reflexive(x in any::<u8>(), y in any::<u8>()) {
            let mut model = x;
            let mut std_ = x;
            prop_assert_eq!(
                *super::BorrowMut::borrow_mut(&mut model),
                *core::borrow::BorrowMut::<u8>::borrow_mut(&mut std_)
            );
            *super::BorrowMut::borrow_mut(&mut model) = y;
            *core::borrow::BorrowMut::<u8>::borrow_mut(&mut std_) = y;
            prop_assert_eq!(model, std_);
        }
    }
}
