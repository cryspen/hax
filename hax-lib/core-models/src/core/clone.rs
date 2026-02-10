// In F* we replace the definition to have the equality a value
// and its clone.
// We need to consume self, instead of taking a reference, otherwise Rust would
// not allow returning an owned Self. This is the same after going through hax.
/// See [`std::clone::Clone`]
#[hax_lib::fstar::replace(
    "class t_Clone self = {
  f_clone_pre: self -> Type0;
  f_clone_post: self -> self -> Type0;
  f_clone: x:self -> r:self {x == r}
}"
)]
pub trait Clone {
    /// See [`std::clone::Clone::clone`]
    fn clone(self) -> Self;
}

// In our model, everything is clonable
impl<T> Clone for T {
    fn clone(self) -> Self {
        self
    }
}

#[cfg(test)]
mod tests {
    use crate::testing::Inject;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_clone(x in any::<u8>()) {
            let model = x.inject();
            prop_assert_eq!(model.clone(), model);
        }
    }
}
