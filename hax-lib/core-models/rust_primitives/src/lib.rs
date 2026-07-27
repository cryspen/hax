#![allow(unused_variables)]

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
    pub fn slice_slice<T>(s: &[T], b: usize, e: usize) -> &[T] {
        &s[b..e]
    }
    pub fn slice_clone_from_slice<T: Clone>(s: &mut [T], src: &[T]) {
        s.clone_from_slice(src)
    }
    // In the following two functions, F is actually a function type.
    // Not constraining that here allows to call it with closures,
    // or to pass parameters that implement the `Fn` trait for core_models.
    // Each backend can type `f` as needed.
    pub fn array_from_fn<T, const N: usize, F: FnMut(usize) -> T>(f: F) -> [T; N] {
        std::array::from_fn(f)
    }
    pub fn array_map<T, U, const N: usize, F: Fn(T) -> U>(s: [T; N], f: F) -> [U; N] {
        s.map(f)
    }
    pub fn array_as_slice<T, const N: usize>(s: &[T; N]) -> &[T] {
        &s[..]
    }
    pub fn array_slice<T, const N: usize>(a: &[T; N], b: usize, e: usize) -> &[T] {
        &a[b..e]
    }
    pub fn array_index<T, const N: usize>(a: &[T; N], i: usize) -> &T {
        &a[i]
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
    pub fn str_sub(s: &'static str, b: usize, e: usize) -> &'static str {
        leak_string(s.chars().skip(b).take(e - b).collect())
    }
    pub fn str_index(s: &'static str, i: usize) -> char {
        s.chars().nth(i).unwrap()
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
