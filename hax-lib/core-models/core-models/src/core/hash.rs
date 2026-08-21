/// See [`std::hash::Hasher`]
///
/// Real `core` supplies every `write_*` method as a trait *default* on top of
/// `write`; hax does not support trait defaults, so they are required methods
/// here and every `Hasher` implementation spells them out. The doc comment on
/// each one names the `core` method it mirrors, and the bodies an implementation
/// is expected to give are exactly `core`'s defaults.
pub trait Hasher {
    /// See [`std::hash::Hasher::finish`]
    fn finish(&self) -> u64;
    /// See [`std::hash::Hasher::write`]
    fn write(&mut self, bytes: &[u8]);
    /// See [`std::hash::Hasher::write_u8`]
    fn write_u8(&mut self, i: u8);
    /// See [`std::hash::Hasher::write_u16`]
    fn write_u16(&mut self, i: u16);
    /// See [`std::hash::Hasher::write_u32`]
    fn write_u32(&mut self, i: u32);
    /// See [`std::hash::Hasher::write_u64`]
    fn write_u64(&mut self, i: u64);
    /// See [`std::hash::Hasher::write_u128`]
    fn write_u128(&mut self, i: u128);
    /// See [`std::hash::Hasher::write_usize`]
    fn write_usize(&mut self, i: usize);
    /// See [`std::hash::Hasher::write_i8`]
    fn write_i8(&mut self, i: i8);
    /// See [`std::hash::Hasher::write_i16`]
    fn write_i16(&mut self, i: i16);
    /// See [`std::hash::Hasher::write_i32`]
    fn write_i32(&mut self, i: i32);
    /// See [`std::hash::Hasher::write_i64`]
    fn write_i64(&mut self, i: i64);
    /// See [`std::hash::Hasher::write_i128`]
    fn write_i128(&mut self, i: i128);
    /// See [`std::hash::Hasher::write_isize`]
    fn write_isize(&mut self, i: isize);
    /// See [`std::hash::Hasher::write_length_prefix`]
    fn write_length_prefix(&mut self, len: usize);
    /// See [`std::hash::Hasher::write_str`]
    fn write_str(&mut self, s: &str);
}

/// See [`std::hash::Hash`]
#[hax_lib::attributes]
pub trait Hash {
    /// See [`std::hash::Hash::hash`]. As elsewhere in the model, the hasher is
    /// threaded by value (`h: H` in, `H` out) rather than by `&mut`.
    #[hax_lib::requires(true)]
    fn hash<H: Hasher>(&self, h: H) -> H;
    /// See [`std::hash::Hash::hash_slice`]. Real `core` gives this as a trait
    /// default (feed each element in turn), which hax does not support, so it is
    /// a required method here.
    fn hash_slice<H: Hasher>(data: &[Self], h: H) -> H
    where
        Self: Sized;
}

/// See [`std::hash::BuildHasher`]
pub trait BuildHasher {
    /// See [`std::hash::BuildHasher::Hasher`]
    type Hasher: Hasher;
    /// See [`std::hash::BuildHasher::build_hasher`]
    fn build_hasher(&self) -> Self::Hasher;
    /// See [`std::hash::BuildHasher::hash_one`]. A trait default in real `core`,
    /// hence a required method here.
    fn hash_one<T: Hash>(&self, x: T) -> u64;
}

/// See [`std::hash::BuildHasherDefault`]
//
// DEVIATION(std): std's field is `PhantomData<fn() -> H>`, chosen only to keep
// `BuildHasherDefault<H>` covariant in `H` and to stay `Send`/`Sync`; variance
// carries no meaning in the model, so the phantom is over `H` directly.
pub struct BuildHasherDefault<H>(std::marker::PhantomData<H>);

impl<H> BuildHasherDefault<H> {
    /// See [`std::hash::BuildHasherDefault::new`]
    pub fn new() -> BuildHasherDefault<H> {
        BuildHasherDefault(std::marker::PhantomData)
    }
}

impl<H: Hasher + super::default::Default> BuildHasher for BuildHasherDefault<H> {
    type Hasher = H;
    fn build_hasher(&self) -> H {
        H::default()
    }
    fn hash_one<T: Hash>(&self, x: T) -> u64 {
        x.hash(self.build_hasher()).finish()
    }
}

// The integer `Hash` impls std keeps in `core::hash::impls`.
//
// DEVIATION(std): std feeds `to_ne_bytes()`; the abstract `Hasher` makes the
// exact bytes unobservable, so we feed a single cast byte. For the same reason
// `hash_slice` follows the generic trait default (one `hash` per element)
// instead of std's integer specialisation, which reinterprets the whole slice
// as bytes and feeds it with a single `write`.
macro_rules! impl_hash_for_int {
    ($($t:ty),*) => {
        $(
            #[hax_lib::attributes]
            impl Hash for $t {
                fn hash<H: Hasher>(&self, mut h: H) -> H {
                    h.write(&[*self as u8]);
                    h
                }
                fn hash_slice<H: Hasher>(data: &[$t], mut h: H) -> H {
                    let mut i = 0;
                    while i < rust_primitives::slice::slice_length(data) {
                        h = rust_primitives::slice::slice_index(data, i).hash(h);
                        i += 1;
                    }
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
        // The `write_*` family is a set of trait *defaults* in real core; hax
        // has no trait defaults, so they are required here and every `Hasher`
        // spells them out. These mirror core's defaults exactly.
        fn write_u8(&mut self, i: u8) {
            self.write(&i.to_ne_bytes())
        }
        fn write_u16(&mut self, i: u16) {
            self.write(&i.to_ne_bytes())
        }
        fn write_u32(&mut self, i: u32) {
            self.write(&i.to_ne_bytes())
        }
        fn write_u64(&mut self, i: u64) {
            self.write(&i.to_ne_bytes())
        }
        fn write_u128(&mut self, i: u128) {
            self.write(&i.to_ne_bytes())
        }
        fn write_usize(&mut self, i: usize) {
            self.write(&i.to_ne_bytes())
        }
        fn write_i8(&mut self, i: i8) {
            self.write_u8(i as u8)
        }
        fn write_i16(&mut self, i: i16) {
            self.write_u16(i as u16)
        }
        fn write_i32(&mut self, i: i32) {
            self.write_u32(i as u32)
        }
        fn write_i64(&mut self, i: i64) {
            self.write_u64(i as u64)
        }
        fn write_i128(&mut self, i: i128) {
            self.write_u128(i as u128)
        }
        fn write_isize(&mut self, i: isize) {
            self.write_usize(i as usize)
        }
        fn write_length_prefix(&mut self, len: usize) {
            self.write_usize(len)
        }
        fn write_str(&mut self, s: &str) {
            self.write(s.as_bytes());
            self.write_u8(0xff)
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
    use super::*;
    use proptest::prelude::*;

    /// A byte-log hasher, implemented twice over the same type: once for the
    /// model's `Hasher` — spelling out the `write_*` family the way real
    /// `core`'s defaults do — and once for `std::hash::Hasher`, which supplies
    /// those defaults itself. Comparing the two logs is what checks the model's
    /// required methods against `core`'s defaults.
    ///
    /// `write` appends, so a hasher that receives *n* one-byte writes and one
    /// that receives a single *n*-byte write are indistinguishable. That is
    /// deliberate: it is what lets `hash_slice` be compared against std's
    /// single-`write` integer specialisation.
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Log(Vec<u8>);

    impl Log {
        fn new() -> Log {
            Log(Vec::new())
        }
        fn push(&mut self, bytes: &[u8]) {
            self.0.extend_from_slice(bytes);
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
            self.push(bytes)
        }
    }

    // Every method here is `core`'s own default body, written out in terms of
    // the inherent `push` so that no call resolves ambiguously between the two
    // `Hasher` traits this type implements.
    impl Hasher for Log {
        fn finish(&self) -> u64 {
            self.fnv()
        }
        fn write(&mut self, bytes: &[u8]) {
            self.push(bytes)
        }
        fn write_u8(&mut self, i: u8) {
            self.push(&[i])
        }
        fn write_u16(&mut self, i: u16) {
            self.push(&i.to_ne_bytes())
        }
        fn write_u32(&mut self, i: u32) {
            self.push(&i.to_ne_bytes())
        }
        fn write_u64(&mut self, i: u64) {
            self.push(&i.to_ne_bytes())
        }
        fn write_u128(&mut self, i: u128) {
            self.push(&i.to_ne_bytes())
        }
        fn write_usize(&mut self, i: usize) {
            self.push(&i.to_ne_bytes())
        }
        fn write_i8(&mut self, i: i8) {
            self.push(&[i as u8])
        }
        fn write_i16(&mut self, i: i16) {
            self.push(&(i as u16).to_ne_bytes())
        }
        fn write_i32(&mut self, i: i32) {
            self.push(&(i as u32).to_ne_bytes())
        }
        fn write_i64(&mut self, i: i64) {
            self.push(&(i as u64).to_ne_bytes())
        }
        fn write_i128(&mut self, i: i128) {
            self.push(&(i as u128).to_ne_bytes())
        }
        fn write_isize(&mut self, i: isize) {
            self.push(&(i as usize).to_ne_bytes())
        }
        fn write_length_prefix(&mut self, len: usize) {
            self.push(&len.to_ne_bytes())
        }
        fn write_str(&mut self, s: &str) {
            self.push(s.as_bytes());
            self.push(&[0xff])
        }
    }

    /// One arm per `write_*` method: run it on the model's `Hasher` and on
    /// std's, and check the byte log and the resulting `finish()` agree.
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
                        prop_assert_eq!(
                            <Log as Hasher>::finish(&m),
                            <Log as std::hash::Hasher>::finish(&s)
                        );
                    }
                )*
            }
        };
    }

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

        #[test]
        fn test_write_str(s in "\\PC{0,16}") {
            let mut m = Log::new();
            <Log as Hasher>::write_str(&mut m, &s);
            let mut r = Log::new();
            <Log as std::hash::Hasher>::write_str(&mut r, &s);
            prop_assert_eq!(&m, &r);
        }

        /// `Hash for u8` is the one width at which the model does not deviate:
        /// std's `write_u8` also feeds exactly one byte.
        #[test]
        fn test_hash_matches_std_u8(x in any::<u8>()) {
            let m = super::Hash::hash(&x, Log::new());
            let mut s = Log::new();
            std::hash::Hash::hash(&x, &mut s);
            prop_assert_eq!(&m, &s);
        }

        #[test]
        fn test_hash_matches_std_i8(x in any::<i8>()) {
            let m = super::Hash::hash(&x, Log::new());
            let mut s = Log::new();
            std::hash::Hash::hash(&x, &mut s);
            prop_assert_eq!(&m, &s);
        }

        /// Wider integers hit the documented deviation, so the expectation is
        /// pinned directly: a single cast byte.
        #[test]
        fn test_hash_u32_is_cast_byte(x in any::<u32>()) {
            let m = super::Hash::hash(&x, Log::new());
            prop_assert_eq!(m.0, vec![x as u8]);
        }

        /// A `Log` cannot see the difference between std's single `write` of the
        /// whole `u8` slice and the model's one-`write`-per-element default.
        #[test]
        fn test_hash_slice_u8(v in prop::collection::vec(any::<u8>(), 0..32)) {
            let m = <u8 as super::Hash>::hash_slice(&v, Log::new());
            let mut s = Log::new();
            std::hash::Hash::hash_slice(&v, &mut s);
            prop_assert_eq!(&m, &s);
            prop_assert_eq!(
                <Log as Hasher>::finish(&m),
                <Log as std::hash::Hasher>::finish(&s)
            );
        }

        #[test]
        fn test_hash_slice_i8(v in prop::collection::vec(any::<i8>(), 0..32)) {
            let m = <i8 as super::Hash>::hash_slice(&v, Log::new());
            let mut s = Log::new();
            std::hash::Hash::hash_slice(&v, &mut s);
            prop_assert_eq!(&m, &s);
        }

        /// `hash_slice` of a wider integer is the model's per-element default.
        #[test]
        fn test_hash_slice_u32_is_cast_bytes(v in prop::collection::vec(any::<u32>(), 0..8)) {
            let m = <u32 as super::Hash>::hash_slice(&v, Log::new());
            prop_assert_eq!(m.0, v.iter().map(|x| *x as u8).collect::<Vec<u8>>());
        }

        /// `BuildHasherDefault::new` + `build_hasher` + `hash_one`, against
        /// std's, at the one width where `Hash` does not deviate.
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
