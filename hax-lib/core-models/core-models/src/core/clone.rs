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

// Real core makes this an `unsafe trait` (implementing it asserts that `clone`
// is a bitwise copy). Like `marker::Send`/`marker::Sync`, the model drops the
// `unsafe`: there is no unsafe obligation to discharge in a pure model.
/// See [`std::clone::TrivialClone`]
pub trait TrivialClone: Clone {}

/// See [`std::clone::UseCloned`]
pub trait UseCloned: Clone {}

// In our model for F*, `Clone` is the identity on every type, so both markers
// hold everywhere.
#[cfg(hax_backend_fstar)]
impl<T> TrivialClone for T {}
#[cfg(hax_backend_fstar)]
impl<T> UseCloned for T {}

macro_rules! clone_impl_for_copy {
    ($($t:ty),*) => {
        $(
            impl crate::clone::Clone for $t {
                fn clone(self) -> Self {
                    self
                }
            }
            impl crate::clone::TrivialClone for $t {}
            impl crate::clone::UseCloned for $t {}
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

    // `TrivialClone` and `UseCloned` are empty markers, so the only thing to
    // observe is that the primitive impls exist and that cloning through the
    // bound still agrees with std's `clone`.
    fn clone_trivial<T: crate::clone::TrivialClone>(x: T) -> T {
        crate::clone::Clone::clone(x)
    }

    fn clone_used<T: crate::clone::UseCloned>(x: T) -> T {
        crate::clone::Clone::clone(x)
    }

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

                    // `TrivialClone` postdates the toolchain we build with and
                    // `UseCloned` is unstable, so both expectations are pinned
                    // against std's plain `Clone` rather than the std markers.
                    #[test]
                    fn [<test_trivial_clone_ $t>](x in any::<$t>()) {
                        prop_assert_eq!(clone_trivial(x.inject()), x.clone().inject());
                    }

                    #[test]
                    fn [<test_use_cloned_ $t>](x in any::<$t>()) {
                        prop_assert_eq!(clone_used(x.inject()), x.clone().inject());
                    }
                }
            )* }
        };
    }

    clone_tests!(
        bool, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
    );
}
