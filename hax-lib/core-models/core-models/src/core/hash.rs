/// See [`std::hash::Hasher`]
pub trait Hasher {
    /// See [`std::hash::Hasher::finish`]
    fn finish(&self) -> u64;
    /// See [`std::hash::Hasher::write`]
    fn write(&mut self, bytes: &[u8]);
}

/// See [`std::hash::Hash`]
#[hax_lib::attributes]
pub trait Hash {
    /// See [`std::hash::Hash::hash`]. As elsewhere in the model, the hasher is
    /// threaded by value (`h: H` in, `H` out) rather than by `&mut`.
    #[hax_lib::requires(true)]
    fn hash<H: Hasher>(&self, h: H) -> H;
}

// The integer `Hash` impls std keeps in `core::hash::impls`.
//
// DEVIATION(std): std feeds `to_ne_bytes()`; the abstract `Hasher` makes the
// exact bytes unobservable, so we feed a single cast byte.
macro_rules! impl_hash_for_int {
    ($($t:ty),*) => {
        $(
            #[hax_lib::attributes]
            impl Hash for $t {
                fn hash<H: Hasher>(&self, mut h: H) -> H {
                    h.write(&[*self as u8]);
                    h
                }
            }
        )*
    };
}

impl_hash_for_int!(
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
    use super::{Hash, Hasher};
    use pastey::paste;
    use proptest::prelude::*;

    /// Records the bytes fed to it. The model's `Hasher` is abstract, so a
    /// recorder is the only way to observe what `hash` writes.
    struct Recorder(std::vec::Vec<u8>);

    impl Hasher for Recorder {
        fn finish(&self) -> u64 {
            self.0.len() as u64
        }
        fn write(&mut self, bytes: &[u8]) {
            self.0.extend_from_slice(bytes)
        }
    }

    // DEVIATION(std): the model feeds one cast byte instead of `to_ne_bytes()`
    // (see `impl_hash_for_int`), so there is nothing in `core` to compare to.
    macro_rules! hash_tests {
        ($($t:ident),*) => {
            paste! { $(
                proptest! {
                    #[test]
                    fn [<test_hash_ $t>](x in any::<$t>()) {
                        let h = Hash::hash(&x, Recorder(std::vec::Vec::new()));
                        prop_assert_eq!(h.0.as_slice(), &[x as u8][..]);
                        prop_assert_eq!(h.finish(), 1);
                    }
                }
            )* }
        };
    }

    hash_tests!(
        u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
    );
}
