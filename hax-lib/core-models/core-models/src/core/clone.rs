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

// In our model for F*, everything is clonable
#[cfg(hax_backend_fstar)]
impl<T> Clone for T {
    fn clone(self) -> Self {
        self
    }
}

macro_rules! clone_impl_for_copy {
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

#[cfg(not(hax_backend_fstar))]
clone_impl_for_copy!(
    core::primitive::bool,
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
    use pastey::paste;
    use proptest::prelude::*;

    // For every `Copy` type with a `Clone` impl, check the model's `Clone`
    // agrees with std's on a random value.
    macro_rules! clone_tests {
        ($($t:ident),*) => {
            paste! { $(
                proptest! {
                    #[test]
                    fn [<test_clone_ $t>](x in any::<$t>()) {
                        prop_assert_eq!(crate::clone::Clone::clone(x.inject()), x.clone().inject());
                    }
                }
            )* }
        };
    }

    clone_tests!(
        bool, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
    );
}
