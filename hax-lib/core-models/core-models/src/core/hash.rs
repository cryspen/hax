// The provided methods are Lean-only, as F* traits have no provided methods.
// DEVIATION(std): they write little-endian bytes where std writes native-endian ones.
/// See [`std::hash::Hasher`]
#[hax_lib::attributes]
pub trait Hasher {
    /// See [`std::hash::Hasher::finish`]
    #[hax_lib::requires(true)]
    fn finish(&self) -> u64;
    /// See [`std::hash::Hasher::write`]
    fn write(&mut self, bytes: &[u8]);
    /// See [`std::hash::Hasher::write_u8`]
    #[cfg(not(hax_backend_fstar))]
    fn write_u8(&mut self, i: u8) {
        self.write(&[i])
    }
    /// See [`std::hash::Hasher::write_u16`]
    #[cfg(not(hax_backend_fstar))]
    fn write_u16(&mut self, i: u16) {
        self.write(&[i as u8, (i >> 8) as u8])
    }
    /// See [`std::hash::Hasher::write_u32`]
    #[cfg(not(hax_backend_fstar))]
    fn write_u32(&mut self, i: u32) {
        self.write(&[i as u8, (i >> 8) as u8, (i >> 16) as u8, (i >> 24) as u8])
    }
    /// See [`std::hash::Hasher::write_u64`]
    #[cfg(not(hax_backend_fstar))]
    fn write_u64(&mut self, i: u64) {
        self.write(&[
            i as u8,
            (i >> 8) as u8,
            (i >> 16) as u8,
            (i >> 24) as u8,
            (i >> 32) as u8,
            (i >> 40) as u8,
            (i >> 48) as u8,
            (i >> 56) as u8,
        ])
    }
    /// See [`std::hash::Hasher::write_u128`]
    #[cfg(not(hax_backend_fstar))]
    fn write_u128(&mut self, i: u128) {
        self.write(&[
            i as u8,
            (i >> 8) as u8,
            (i >> 16) as u8,
            (i >> 24) as u8,
            (i >> 32) as u8,
            (i >> 40) as u8,
            (i >> 48) as u8,
            (i >> 56) as u8,
            (i >> 64) as u8,
            (i >> 72) as u8,
            (i >> 80) as u8,
            (i >> 88) as u8,
            (i >> 96) as u8,
            (i >> 104) as u8,
            (i >> 112) as u8,
            (i >> 120) as u8,
        ])
    }
    /// See [`std::hash::Hasher::write_usize`]
    #[cfg(not(hax_backend_fstar))]
    fn write_usize(&mut self, i: usize) {
        self.write(&[
            i as u8,
            (i >> 8) as u8,
            (i >> 16) as u8,
            (i >> 24) as u8,
            (i >> 32) as u8,
            (i >> 40) as u8,
            (i >> 48) as u8,
            (i >> 56) as u8,
        ])
    }
    /// See [`std::hash::Hasher::write_i8`]
    #[cfg(not(hax_backend_fstar))]
    fn write_i8(&mut self, i: i8) {
        self.write_u8(i as u8)
    }
    /// See [`std::hash::Hasher::write_i16`]
    #[cfg(not(hax_backend_fstar))]
    fn write_i16(&mut self, i: i16) {
        self.write_u16(i as u16)
    }
    /// See [`std::hash::Hasher::write_i32`]
    #[cfg(not(hax_backend_fstar))]
    fn write_i32(&mut self, i: i32) {
        self.write_u32(i as u32)
    }
    /// See [`std::hash::Hasher::write_i64`]
    #[cfg(not(hax_backend_fstar))]
    fn write_i64(&mut self, i: i64) {
        self.write_u64(i as u64)
    }
    /// See [`std::hash::Hasher::write_i128`]
    #[cfg(not(hax_backend_fstar))]
    fn write_i128(&mut self, i: i128) {
        self.write_u128(i as u128)
    }
    /// See [`std::hash::Hasher::write_isize`]
    #[cfg(not(hax_backend_fstar))]
    fn write_isize(&mut self, i: isize) {
        self.write_usize(i as usize)
    }
    /// See [`std::hash::Hasher::write_length_prefix`]
    #[cfg(not(hax_backend_fstar))]
    fn write_length_prefix(&mut self, len: usize) {
        self.write_usize(len)
    }
    /// See [`std::hash::Hasher::write_str`]
    #[cfg(not(hax_backend_fstar))]
    fn write_str(&mut self, s: &str) {
        self.write(rust_primitives::string::str_as_bytes(s));
        self.write_u8(0xff)
    }
}

/// See [`std::hash::Hash`]
#[hax_lib::attributes]
pub trait Hash {
    /// See [`std::hash::Hash::hash`]
    #[hax_lib::requires(true)]
    fn hash<H: Hasher>(&self, state: &mut H);
    /// See [`std::hash::Hash::hash_slice`]
    #[cfg(not(hax_backend_fstar))]
    fn hash_slice<H: Hasher>(data: &[Self], state: &mut H)
    where
        Self: Sized,
    {
        let mut i = 0;
        while i < rust_primitives::slice::slice_length(data) {
            rust_primitives::slice::slice_index(data, i).hash(state);
            i += 1;
        }
    }
}

/// See [`std::hash::BuildHasher`]
pub trait BuildHasher {
    /// See [`std::hash::BuildHasher::Hasher`]
    type Hasher: Hasher;
    /// See [`std::hash::BuildHasher::build_hasher`]
    fn build_hasher(&self) -> Self::Hasher;
    /// See [`std::hash::BuildHasher::hash_one`]
    #[cfg(not(hax_backend_fstar))]
    // The `Self::Hasher` bound repeats the associated type's, as core does:
    // callers pass one dictionary per clause.
    fn hash_one<T: Hash>(&self, x: T) -> u64
    where
        Self: Sized,
        Self::Hasher: Hasher,
    {
        let mut hasher = self.build_hasher();
        x.hash(&mut hasher);
        hasher.finish()
    }
}

/// See [`std::hash::BuildHasherDefault`]
//
// DEVIATION(std): the phantom is over `H`, not `fn() -> H`; variance is irrelevant here.
pub struct BuildHasherDefault<H>(std::marker::PhantomData<H>);

// Placeholder for core's `impl Hasher for &mut H`, so `new` is `impl_1` as in core.
impl<H> BuildHasherDefault<H> {}

impl<H> BuildHasherDefault<H> {
    /// See [`std::hash::BuildHasherDefault::new`]
    pub fn new() -> BuildHasherDefault<H> {
        BuildHasherDefault(std::marker::PhantomData)
    }
}

impl<H: super::default::Default + Hasher> BuildHasher for BuildHasherDefault<H> {
    type Hasher = H;
    fn build_hasher(&self) -> H {
        H::default()
    }
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
                fn hash<H: Hasher>(&self, state: &mut H) {
                    state.write(&[*self as u8])
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
    use super::*;
    use pastey::paste;
    use proptest::prelude::*;

    /// Byte-log hasher implementing both the model's and std's `Hasher`.
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Log(Vec<u8>);

    impl Log {
        fn new() -> Log {
            Log(Vec::new())
        }
        fn fnv(&self) -> u64 {
            let mut h: u64 = 0xcbf2_9ce4_8422_2325;
            for b in &self.0 {
                h ^= *b as u64;
                h = h.wrapping_mul(0x0000_0100_0000_01b3);
            }
            h
        }
    }

    impl std::default::Default for Log {
        fn default() -> Log {
            Log::new()
        }
    }

    impl crate::default::Default for Log {
        fn default() -> Log {
            Log::new()
        }
    }

    impl std::hash::Hasher for Log {
        fn finish(&self) -> u64 {
            self.fnv()
        }
        fn write(&mut self, bytes: &[u8]) {
            self.0.extend_from_slice(bytes)
        }
    }

    // Only the required methods, so the tests below run the provided ones.
    impl Hasher for Log {
        fn finish(&self) -> u64 {
            self.fnv()
        }
        fn write(&mut self, bytes: &[u8]) {
            self.0.extend_from_slice(bytes)
        }
    }

    // DEVIATION(std): the model feeds one cast byte instead of `to_ne_bytes()`.
    macro_rules! hash_tests {
        ($($t:ident),*) => {
            paste! { $(
                proptest! {
                    #[test]
                    fn [<test_hash_ $t>](x in any::<$t>()) {
                        let mut h = Log::new();
                        Hash::hash(&x, &mut h);
                        prop_assert_eq!(h.0.as_slice(), &[x as u8][..]);
                    }
                }
            )* }
        };
    }

    hash_tests!(
        u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
    );

    // std's defaults write native-endian bytes, which are little-endian here.
    #[cfg(not(hax_backend_fstar))]
    macro_rules! write_prop {
        ($($name:ident, $meth:ident, $t:ty;)*) => {
            proptest! {
                $(
                    #[test]
                    fn $name(x in any::<$t>()) {
                        let mut m = Log::new();
                        <Log as Hasher>::$meth(&mut m, x);
                        let mut s = Log::new();
                        <Log as std::hash::Hasher>::$meth(&mut s, x);
                        prop_assert_eq!(&m, &s);
                    }
                )*
            }
        };
    }

    #[cfg(not(hax_backend_fstar))]
    write_prop! {
        test_write_u8, write_u8, u8;
        test_write_u16, write_u16, u16;
        test_write_u32, write_u32, u32;
        test_write_u64, write_u64, u64;
        test_write_u128, write_u128, u128;
        test_write_usize, write_usize, usize;
        test_write_i8, write_i8, i8;
        test_write_i16, write_i16, i16;
        test_write_i32, write_i32, i32;
        test_write_i64, write_i64, i64;
        test_write_i128, write_i128, i128;
        test_write_isize, write_isize, isize;
        test_write_length_prefix, write_length_prefix, usize;
    }

    proptest! {
        #[test]
        fn test_write(bytes in prop::collection::vec(any::<u8>(), 0..32)) {
            let mut m = Log::new();
            <Log as Hasher>::write(&mut m, &bytes);
            let mut s = Log::new();
            <Log as std::hash::Hasher>::write(&mut s, &bytes);
            prop_assert_eq!(&m, &s);
            prop_assert_eq!(
                <Log as Hasher>::finish(&m),
                <Log as std::hash::Hasher>::finish(&s)
            );
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_write_str(s in "\\PC{0,16}") {
            let mut m = Log::new();
            <Log as Hasher>::write_str(&mut m, &s);
            let mut r = Log::new();
            <Log as std::hash::Hasher>::write_str(&mut r, &s);
            prop_assert_eq!(&m, &r);
        }

        #[test]
        fn test_hash_matches_std_u8(x in any::<u8>()) {
            let mut m = Log::new();
            Hash::hash(&x, &mut m);
            let mut s = Log::new();
            std::hash::Hash::hash(&x, &mut s);
            prop_assert_eq!(&m, &s);
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_hash_slice_u8(v in prop::collection::vec(any::<u8>(), 0..32)) {
            let mut m = Log::new();
            <u8 as Hash>::hash_slice(&v, &mut m);
            let mut s = Log::new();
            std::hash::Hash::hash_slice(&v, &mut s);
            prop_assert_eq!(&m, &s);
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_build_hasher_default_hash_one(x in any::<u8>()) {
            let m = BuildHasherDefault::<Log>::new();
            let s = std::hash::BuildHasherDefault::<Log>::default();
            prop_assert_eq!(
                BuildHasher::hash_one(&m, x),
                std::hash::BuildHasher::hash_one(&s, x)
            );
        }

        #[test]
        fn test_build_hasher_build_hasher(bytes in prop::collection::vec(any::<u8>(), 0..8)) {
            let m = BuildHasherDefault::<Log>::new();
            let s = std::hash::BuildHasherDefault::<Log>::default();
            let mut mh = BuildHasher::build_hasher(&m);
            let mut sh = std::hash::BuildHasher::build_hasher(&s);
            <Log as Hasher>::write(&mut mh, &bytes);
            <Log as std::hash::Hasher>::write(&mut sh, &bytes);
            prop_assert_eq!(&mh, &sh);
        }
    }
}
