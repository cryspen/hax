#![allow(unused_variables)]
// Gated so the crate still builds on stable, where the attribute is unknown.
#![cfg_attr(coverage_nightly, feature(coverage_attribute))]

pub mod slice {
    pub fn slice_length<T>(s: &[T]) -> usize {
        s.len()
    }
    #[hax_lib::requires(mid <= slice_length(s))]
    pub fn slice_split_at<T>(s: &[T], mid: usize) -> (&[T], &[T]) {
        s.split_at(mid)
    }
    pub fn slice_contains<T: PartialEq>(s: &[T], v: &T) -> bool {
        s.contains(v)
    }
    #[hax_lib::requires(i < slice_length(s))]
    pub fn slice_index<T>(s: &[T], i: usize) -> &T {
        &s[i]
    }
    #[hax_lib::requires(i < slice_length(s))]
    pub fn slice_index_mut<T>(s: &mut [T], i: usize) -> &mut T {
        &mut s[i]
    }
    pub fn slice_slice<T>(s: &[T], b: usize, e: usize) -> &[T] {
        &s[b..e]
    }
    #[hax_lib::requires(b <= e && e <= slice_length(s))]
    pub fn slice_slice_mut<T>(s: &mut [T], b: usize, e: usize) -> &mut [T] {
        &mut s[b..e]
    }
    pub fn slice_clone_from_slice<T: Clone>(s: &mut [T], src: &[T]) {
        s.clone_from_slice(src)
    }
    // `reverse`/`swap` mutate in place; with no `Clone`/`Copy` bound the elements
    // can't be read out of the shared-ref `slice_index`/`slice_slice` and written
    // back, so they are primitives.
    pub fn slice_reverse<T>(s: &mut [T]) {
        s.reverse()
    }
    #[hax_lib::requires(a < slice_length(s) && b < slice_length(s))]
    pub fn slice_swap<T>(s: &mut [T], a: usize, b: usize) {
        s.swap(a, b)
    }
    // In the following two functions, F is actually a function type.
    // Not constraining that here allows to call it with closures,
    // or to pass parameters that implement the `Fn` trait for core_models.
    // Each backend can type `f` as needed.
    pub fn array_from_fn<T, const N: usize, F: FnMut(usize) -> T>(f: F) -> [T; N] {
        std::array::from_fn(f)
    }
    pub fn array_map<T, U, const N: usize, F: FnMut(T) -> U>(s: [T; N], f: F) -> [U; N] {
        s.map(f)
    }
    pub fn array_as_slice<T, const N: usize>(s: &[T; N]) -> &[T] {
        &s[..]
    }
    // A `[a, b]` literal written in the model extracts to
    // `Rust_primitives.Hax.array_of_list`, and `Rust_primitives.Hax` depends on
    // `Core_models.{Array, Slice, Ops.Range}`, which closes a module cycle
    // through hax's bundle. Going through this helper keeps the construction in
    // `Rust_primitives.Slice`, which `Core_models` does not depend on.
    pub fn array_pair<T>(a: T, b: T) -> [T; 2] {
        [a, b]
    }
    pub fn array_as_slice_mut<T, const N: usize>(s: &mut [T; N]) -> &mut [T] {
        &mut s[..]
    }
    // Viewing a place as a one-element array is a pointer cast in real core, so
    // it cannot be written in the model itself.
    pub fn array_from_ref<T>(s: &T) -> &[T; 1] {
        std::array::from_ref(s)
    }
    pub fn array_from_mut<T>(s: &mut T) -> &mut [T; 1] {
        std::array::from_mut(s)
    }
    // `Clone` is Rust's here, not the model's: the model's `clone` consumes its
    // receiver, so it cannot produce `N` copies of a single owned value. Like
    // `core::array::repeat`, the last element is `val` itself and the other
    // `N - 1` are clones.
    pub fn array_repeat<T: Clone, const N: usize>(val: T) -> [T; N] {
        // `repeat_n` rather than `from_fn(|_| val.clone())`: like `[val; N]` it
        // clones `val` for all but the last slot, which takes `val` itself.
        array_from_vec(std::iter::repeat_n(val, N).collect())
    }
    /// The `N` elements of `v` as an array. Panics on any other length; the one
    /// caller above always passes `N`, so the panic is reached only by the test
    /// that calls this directly.
    // Excluded from coverage: the length check is per-instantiation, and only the
    // one the test names can reach it. Split out of `array_repeat` so that the
    // exclusion covers these four lines rather than the whole function.
    #[cfg_attr(coverage_nightly, coverage(off))]
    pub(crate) fn array_from_vec<T, const N: usize>(v: Vec<T>) -> [T; N] {
        match <[T; N]>::try_from(v) {
            Ok(a) => a,
            Err(v) => panic!("expected {} elements, got {}", N, v.len()),
        }
    }
    pub fn array_slice<T, const N: usize>(a: &[T; N], b: usize, e: usize) -> &[T] {
        &a[b..e]
    }
    pub fn array_index<T, const N: usize>(a: &[T; N], i: usize) -> &T {
        &a[i]
    }
}

/// Layout and value-moving primitives backing `core_models::mem`. `core_models`
/// must not call `core` itself, so every `mem` model delegates here.
pub mod mem {
    // mutants::skip: forgetting has no observable effect, so the empty body is an equivalent mutant.
    #[cfg_attr(test, mutants::skip)]
    pub fn forget<T>(t: T) {
        core::mem::forget(t)
    }
    pub fn size_of<T>() -> usize {
        core::mem::size_of::<T>()
    }
    pub fn size_of_val<T: ?Sized>(val: &T) -> usize {
        core::mem::size_of_val(val)
    }
    pub fn align_of<T>() -> usize {
        core::mem::align_of::<T>()
    }
    pub fn align_of_val<T: ?Sized>(val: &T) -> usize {
        core::mem::align_of_val(val)
    }
    pub fn needs_drop<T: ?Sized>() -> bool {
        core::mem::needs_drop::<T>()
    }
    pub fn swap<T>(x: &mut T, y: &mut T) {
        core::mem::swap(x, y)
    }
    pub fn replace<T>(dest: &mut T, src: T) -> T {
        core::mem::replace(dest, src)
    }
    pub unsafe fn zeroed<T>() -> T {
        unsafe { core::mem::zeroed() }
    }
    pub unsafe fn transmute_copy<Src, Dst>(src: &Src) -> Dst {
        unsafe { core::mem::transmute_copy(src) }
    }
    // `core::mem::transmute` needs `Src` and `Dst` to have provably equal sizes,
    // which no generic function can state; `transmute_copy` checks it at runtime.
    pub unsafe fn transmute<Src, Dst>(src: Src) -> Dst {
        let dst = unsafe { core::mem::transmute_copy(&src) };
        core::mem::forget(src);
        dst
    }
}

pub mod sequence {
    #[derive(PartialEq, Debug)]
    pub struct Seq<T>(Vec<T>);
    pub fn seq_empty<T>() -> Seq<T> {
        Seq(Vec::new())
    }
    pub fn seq_from_slice<T>(s: &[T]) -> Seq<&T> {
        Seq(s.iter().collect())
    }
    pub fn seq_from_boxed_slice<T>(s: Box<[T]>) -> Seq<T> {
        Seq(s.into_vec())
    }
    pub fn seq_from_array<T, const N: usize>(s: [T; N]) -> Seq<T> {
        Seq(s.into_iter().collect())
    }
    pub fn seq_to_slice<T>(s: &Seq<T>) -> &[T] {
        s.0.as_slice()
    }
    pub fn seq_to_slice_mut<T>(s: &mut Seq<T>) -> &mut [T] {
        s.0.as_mut_slice()
    }

    pub fn seq_into_boxed_slice<T>(s: Seq<T>) -> Box<[T]> {
        s.0.into_boxed_slice()
    }
    pub fn seq_concat<T>(s1: &mut Seq<T>, s2: &mut Seq<T>) {
        s1.0.append(&mut s2.0)
    }
    pub fn seq_extend<T>(s1: &mut Seq<T>, s2: &[T])
    where
        T: Clone,
    {
        s1.0.extend_from_slice(s2)
    }
    pub fn seq_push<T>(s1: &mut Seq<T>, v: T) {
        s1.0.push(v)
    }
    pub fn seq_one<T>(x: T) -> Seq<T> {
        Seq(vec![x])
    }
    pub fn seq_create<T: Clone>(x: T, n: usize) -> Seq<T> {
        Seq(vec![x; n])
    }
    pub fn seq_len<T>(s: &Seq<T>) -> usize {
        s.0.len()
    }
    pub fn seq_drain<T>(s: &mut Seq<T>, b: usize, e: usize) -> Seq<T> {
        Seq(s.0.drain(b..e).collect())
    }
    pub fn seq_remove<T>(s: &mut Seq<T>, n: usize) -> T {
        s.0.remove(n)
    }
    pub fn seq_index<T>(s: &Seq<T>, i: usize) -> &T {
        &s.0[i]
    }
    #[hax_lib::requires(i < seq_len(s))]
    pub fn seq_index_mut<T>(s: &mut Seq<T>, i: usize) -> &mut T {
        &mut s.0[i]
    }
}

pub mod string {
    use std::sync::OnceLock;

    static STRING_ARENA: OnceLock<std::sync::Mutex<Vec<String>>> = OnceLock::new();

    fn leak_string(s: String) -> &'static str {
        let arena = STRING_ARENA.get_or_init(|| std::sync::Mutex::new(Vec::new()));
        let mut arena = arena.lock().unwrap();
        arena.push(s);
        // SAFETY: The string is stored in the arena and will live for the program's lifetime
        unsafe { std::mem::transmute(arena.last().unwrap().as_str()) }
    }

    pub fn str_concat(s1: &'static str, s2: &'static str) -> &'static str {
        leak_string(format!("{}{}", s1, s2))
    }
    pub fn str_of_char(c: char) -> &'static str {
        leak_string(c.to_string())
    }
    /// The `[b, e)` sub-string of `s`, in **char** positions.
    pub fn str_sub(s: &'static str, b: usize, e: usize) -> &'static str {
        leak_string(s.chars().skip(b).take(e - b).collect())
    }
    /// The `[b, e)` sub-string of `s`, in **byte** positions — i.e. `&s[b..e]`,
    /// so it panics exactly where indexing a `str` does.
    pub fn str_sub_bytes(s: &'static str, b: usize, e: usize) -> &'static str {
        &s[b..e]
    }
    /// The char at **char** position `i`.
    pub fn str_index(s: &'static str, i: usize) -> char {
        s.chars().nth(i).unwrap()
    }
    /// Length in `char`s, to match `str_sub`/`str_index` above. `str::len`
    /// counts bytes, so the two disagree on any multi-byte char.
    pub fn str_len(s: &'static str) -> usize {
        s.chars().count()
    }
    // `Option`/`Result` are `core` types, which `core_models` may not touch, so
    // these fallible primitives answer with a validity flag instead.
    // On failure the last two components carry `Utf8Error`'s payload:
    // `valid_up_to`, and `error_len` with 0 standing for `None` (a real
    // `error_len` is 1..=3, so 0 is unambiguous).
    pub fn str_from_utf8(s: &[u8]) -> (bool, &str, usize, u8) {
        match core::str::from_utf8(s) {
            Ok(s) => (true, s, 0, 0),
            Err(e) => (false, "", e.valid_up_to(), e.error_len().unwrap_or(0) as u8),
        }
    }
    /// The UTF-8 encoding of `s`. This is the gateway primitive for the
    /// byte-oriented part of the `str` model: everything else there is written
    /// in plain Rust on top of it.
    pub fn str_as_bytes(s: &str) -> &[u8] {
        s.as_bytes()
    }
    /// `&s[b..e]`, indexed in **bytes** (unlike `str_sub`, which counts
    /// `char`s). Slicing a `str` off a char boundary panics.
    #[hax_lib::requires(b <= e && e <= crate::slice::slice_length(str_as_bytes(s)))]
    pub fn str_sub_bytes(s: &str, b: usize, e: usize) -> &str {
        &s[b..e]
    }
    /// The number of chars in `s` (not its byte length).
    pub fn str_char_count(s: &'static str) -> usize {
        s.chars().count()
    }
    /// Mirrors [`str::is_char_boundary`]: `false` for `i > s.len()`.
    pub fn str_is_char_boundary(s: &'static str, i: usize) -> bool {
        s.is_char_boundary(i)
    }
    /// Whether `bytes` is a valid UTF-8 encoding.
    pub fn str_is_utf8(bytes: &[u8]) -> bool {
        core::str::from_utf8(bytes).is_ok()
    }
    /// `bytes` decoded as UTF-8, invalid sequences replaced by U+FFFD
    /// (the conversion behind `String::from_utf8_lossy`). It is the identity
    /// on valid input, which is what lets `String::from_utf8` reuse it.
    pub fn str_from_utf8_lossy(bytes: &[u8]) -> &'static str {
        leak_string(String::from_utf8_lossy(bytes).into_owned())
    }
    /// `x` rendered through its [`core::fmt::Display`] implementation. Only
    /// reachable from `ToString`'s blanket impl, which is `#[hax_lib::opaque]`:
    /// running a `Display` impl is not something the model can express, so this
    /// is a Rust-side oracle and never surfaces in an extraction.
    pub fn str_of_display<T: core::fmt::Display>(x: &T) -> &'static str {
        leak_string(format!("{}", x))
    }
}

pub mod float {
    pub fn abs_f64(x: f64) -> f64 {
        x.abs()
    }
    pub fn powf_f64(x: f64, y: f64) -> f64 {
        x.powf(y)
    }
}

pub mod arithmetic {
    use pastey::paste;

    macro_rules! arithmetic_ops {
        (
            types: $t:ident,
            ops: $($op:ident)*,
            overflowing_ops: $($ov_op:ident)*,
        ) => {
            paste!{
                $(pub fn [<$op _ $t>](x: $t, y: $t) -> $t {
                    x.$op(y)
                })*
                $(pub fn [<$ov_op _ $t>](x: $t, y: $t) -> ($t, bool) {
                    x.$ov_op(y)
                })*
            }
        };

        (
            types: $first_t:ident $($t:ident)+,
            ops: $($op:ident)*,
            overflowing_ops: $($ov_op:ident)*,
        ) => {
            arithmetic_ops!(types: $first_t, ops: $($op)*, overflowing_ops: $($ov_op)*,);
            arithmetic_ops!(types: $($t)*, ops: $($op)*, overflowing_ops: $($ov_op)*,);
        };

    }

    macro_rules! all_ops {
        (
            $($Self: ident)*,
            $($Bytes: expr)*,
        ) => {
            paste! {
                $(
                pub fn [<pow_ $Self>](x: $Self, exp: u32) -> $Self {
                    x.pow(exp)
                }
                pub fn [<overflowing_pow_ $Self>](x: $Self, exp: u32) -> ($Self, bool) {
                    x.overflowing_pow(exp)
                }
                pub fn [<count_ones_ $Self>](x: $Self) -> u32 {
                    x.count_ones()
                }
                pub fn [<rotate_right_ $Self>](x: $Self, n: u32) -> $Self {
                    x.rotate_right(n)
                }
                pub fn [<rotate_left_ $Self>](x: $Self, n: u32) -> $Self {
                    x.rotate_left(n)
                }
                pub fn [<leading_zeros_ $Self>](x: $Self) -> u32 {
                    x.leading_zeros()
                }
                pub fn [<ilog2_ $Self>](x: $Self) -> u32 {
                    x.ilog2()
                }
                pub fn [<from_be_bytes_ $Self>](bytes: [u8; $Bytes]) -> $Self {
                    $Self::from_be_bytes(bytes)
                }
                pub fn [<from_le_bytes_ $Self>](bytes: [u8; $Bytes]) -> $Self {
                    $Self::from_le_bytes(bytes)
                }
                pub fn [<to_be_bytes_ $Self>](bytes: $Self) -> [u8; $Bytes] {
                    bytes.to_be_bytes()
                }
                pub fn [<to_le_bytes_ $Self>](bytes: $Self) -> [u8; $Bytes] {
                    bytes.to_le_bytes()
                }
                // Validity flag rather than `Result`: see `string::str_from_utf8`.
                pub fn [<from_str_radix_ $Self>](src: &str, radix: u32) -> (bool, $Self) {
                    match $Self::from_str_radix(src, radix) {
                        Ok(v) => (true, v),
                        Err(_) => (false, 0),
                    }
                })*
            }
        }
    }

    macro_rules! signed_ops {
        ($($Self: ident)*) => {
            paste! {
                $(
                    pub fn [<abs_ $Self>](x: $Self) -> $Self {
                    x.abs()
                }
                )*
            }
        }
    }

    // Rust inlines these values, for now we model usize by u64
    // eventually we could try to define in the backend as 32 or 64
    pub const SIZE_BYTES: usize = 8;
    pub const SIZE_BITS: u32 = 64;
    pub const USIZE_MAX: usize = u64::MAX as usize;
    pub const ISIZE_MAX: isize = i64::MAX as isize;
    pub const ISIZE_MIN: isize = i64::MIN as isize;

    arithmetic_ops! {
        types: u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize,
        ops: wrapping_add saturating_add wrapping_sub saturating_sub wrapping_mul saturating_mul rem_euclid,
        overflowing_ops: overflowing_add overflowing_sub overflowing_mul,
    }

    all_ops! {
        u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize,
        1 2 4 8 16 SIZE_BYTES 1 2 4 8 16 SIZE_BYTES,
    }

    signed_ops! {
        i8 i16 i32 i64 i128 isize
    }
}

// `array_slice` is only reached through the F* variant of `core_models::array`'s
// `Index` impls, and `seq_one`/`str_sub`/`str_index` have no model caller at
// all, so they are checked here directly.
#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    // `array_repeat` always passes exactly `N` elements, so its length check is
    // only reachable from here.
    #[test]
    fn test_array_from_vec_wrong_length_panics() {
        let res =
            std::panic::catch_unwind(|| crate::slice::array_from_vec::<u8, 3>(std::vec![1u8, 2]));
        assert!(res.is_err());
    }

    proptest! {
        #[test]
        fn test_array_slice(a in any::<[u8; 8]>(), i in 0usize..=8, j in 0usize..=8) {
            let (b, e) = (i.min(j), i.max(j));
            prop_assert_eq!(super::slice::array_slice(&a, b, e), &a[b..e]);
        }

        // `slice_index_mut`/`slice_slice_mut` have no caller in the F* models, and
        // `array_map` none in the others.
        #[test]
        fn test_slice_index_mut(v in proptest::collection::vec(any::<u8>(), 1..20), i in 0usize..20, x in any::<u8>()) {
            let i = i % v.len();
            let mut model = v.clone();
            *super::slice::slice_index_mut(&mut model, i) = x;
            let mut expected = v;
            expected[i] = x;
            prop_assert_eq!(model, expected);
        }

        #[test]
        fn test_slice_slice_mut(v in proptest::collection::vec(any::<u8>(), 1..20), i in 0usize..20, len in 0usize..20, x in any::<u8>()) {
            let b = i % v.len();
            let e = (b + len).min(v.len());
            let mut model = v.clone();
            super::slice::slice_slice_mut(&mut model, b, e).fill(x);
            let mut expected = v;
            expected[b..e].fill(x);
            prop_assert_eq!(model, expected);
        }

        #[test]
        fn test_array_map(a in any::<[u8; 4]>(), table in any::<[u8; 256]>()) {
            let f = |x: u8| table[x as usize];
            prop_assert_eq!(super::slice::array_map(a, f), a.map(f));
        }

        #[test]
        fn test_seq_to_slice_mut(x in any::<u8>(), y in any::<u8>()) {
            let mut s = super::sequence::seq_one(x);
            super::sequence::seq_to_slice_mut(&mut s)[0] = y;
            prop_assert_eq!(super::sequence::seq_to_slice(&s), &[y][..]);
        }

        #[test]
        fn test_seq_one(x in any::<u8>()) {
            let s = super::sequence::seq_one(x);
            prop_assert_eq!(super::sequence::seq_len(&s), 1);
            prop_assert_eq!(super::sequence::seq_to_slice(&s), &[x][..]);
        }

        #[test]
        fn test_str_sub_and_index(text in "[a-z]{1,10}", start in 0usize..10, len in 0usize..10) {
            let chars: std::vec::Vec<char> = text.chars().collect();
            let leaked: &'static str = Box::leak(text.into_boxed_str());
            let b = start % chars.len();
            let e = (b + len).min(chars.len());
            let expected: String = chars[b..e].iter().collect();
            prop_assert_eq!(super::string::str_sub(leaked, b, e), expected.as_str());
            prop_assert_eq!(super::string::str_index(leaked, b), chars[b]);
        }
    }
}
