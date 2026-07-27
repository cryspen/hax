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
