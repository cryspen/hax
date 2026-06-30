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
#[cfg(hax)]
impl<T> Clone for T {
    fn clone(self) -> Self {
        self
    }
}

macro_rules! clone_impl_for_int {
    ($($t:ty),*) => {
        $(
            impl crate::clone::Clone for $t {
                fn clone(self) -> Self {
                    self
                }
            }
        )*
    };
}

#[cfg(not(hax))]
clone_impl_for_int!(
    core::primitive::u8,
    core::primitive::u16,
    core::primitive::u32,
    core::primitive::u64,
    core::primitive::u128,
    core::primitive::usize,
    core::primitive::i8,
    core::primitive::i16,
    core::primitive::i32,
    core::primitive::i64,
    core::primitive::i128,
    core::primitive::isize
);

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
