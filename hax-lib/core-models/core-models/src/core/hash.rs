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
// DEVIATION(std): std feeds `to_ne_bytes()`; the model has no native-endian
// conversion and pins little-endian everywhere, so we feed `to_le_bytes()`.
macro_rules! impl_hash_for_int {
    ($($t:ty => $n:ident),*) => {
        $(
            #[hax_lib::attributes]
            impl Hash for $t {
                fn hash<H: Hasher>(&self, mut h: H) -> H {
                    h.write(&crate::num::$n::to_le_bytes(*self));
                    h
                }
            }
        )*
    };
}

impl_hash_for_int!(
    core::primitive::u8 => u8,
    core::primitive::u16 => u16,
    core::primitive::u32 => u32,
    core::primitive::u64 => u64,
    core::primitive::u128 => u128,
    core::primitive::usize => usize,
    core::primitive::i8 => i8,
    core::primitive::i16 => i16,
    core::primitive::i32 => i32,
    core::primitive::i64 => i64,
    core::primitive::i128 => i128,
    core::primitive::isize => isize
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

    // DEVIATION(std): the model feeds `to_le_bytes()` instead of `to_ne_bytes()`
    // (see `impl_hash_for_int`); on a little-endian target the two agree.
    macro_rules! hash_tests {
        ($($t:ident),*) => {
            paste! { $(
                proptest! {
                    #[test]
                    fn [<test_hash_ $t>](x in any::<$t>()) {
                        let h = Hash::hash(&x, Recorder(std::vec::Vec::new()));
                        prop_assert_eq!(h.0.as_slice(), &x.to_le_bytes()[..]);
                        prop_assert_eq!(h.finish(), (size_of::<$t>()) as u64);
                    }
                }
            )* }
        };
    }

    proptest! {
        /// Distinct values of a multi-byte integer must not collide, which the
        /// old single-truncated-byte model allowed (`hash(1u16) == hash(257u16)`).
        #[test]
        fn test_hash_u16_injective(x in any::<u16>(), y in any::<u16>()) {
            let hx = Hash::hash(&x, Recorder(std::vec::Vec::new())).0;
            let hy = Hash::hash(&y, Recorder(std::vec::Vec::new())).0;
            prop_assert_eq!(x == y, hx == hy);
        }
    }

    hash_tests!(
        u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
    );
}
