#![allow(unused_variables)]

pub mod slice {
    pub fn slice_length<T>(s: &[T]) -> usize {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    #[hax_lib::requires(mid <= slice_length(s))]
    pub fn slice_split_at<T>(s: &[T], mid: usize) -> (&[T], &[T]) {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn slice_contains<T>(s: &[T], v: T) -> bool {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    #[hax_lib::requires(i < slice_length(s))]
    pub fn slice_index<T>(s: &[T], i: usize) -> &T {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn slice_slice<T>(s: &[T], b: usize, e: usize) -> &[T] {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    // In the following two functions, F is actually a function type.
    // Not constraining that here allows to call it with closures,
    // or to pass parameters that implement the `Fn` trait for core_models.
    // Each backend can type `f` as needed.
    pub fn array_from_fn<T, const N: usize, F>(f: F) -> [T; N] {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn array_map<T, U, const N: usize, F>(s: [T; N], f: F) -> [U; N] {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn array_as_slice<T, const N: usize>(s: &[T; N]) -> &[T] {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn array_slice<T, const N: usize>(a: &[T; N], b: usize, e: usize) -> &[T] {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn array_index<T, const N: usize>(a: &[T; N], i: usize) -> &T {
        unimplemented!("This is a stub that is implemented in each backend")
    }
}

pub mod sequence {
    pub struct Seq<T>(Option<T>);
    pub fn seq_empty<T>() -> Seq<T> {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn seq_from_slice<T>(_s: &[T]) -> Seq<T> {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn seq_from_array<T, const N: usize>(_s: [T; N]) -> Seq<T> {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn seq_to_slice<T>(_s: &Seq<T>) -> &[T] {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn seq_concat<T>(s1: &mut Seq<T>, s2: &Seq<T>) {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn seq_one<T>(x: T) -> Seq<T> {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn seq_create<T>(x: T, n: usize) -> Seq<T> {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn seq_len<T>(s: &Seq<T>) -> usize {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn seq_slice<T>(s: &Seq<T>, b: usize, e: usize) -> Seq<T> {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn seq_last<T>(s: &Seq<T>) -> T {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn seq_first<T>(s: &Seq<T>) -> T {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn seq_index<T>(s: &Seq<T>, i: usize) -> &T {
        unimplemented!("This is a stub that is implemented in each backend")
    }
}

pub mod string {
    pub fn str_concat(s1: &'static str, s2: &'static str) -> &'static str {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn str_of_char(c: char) -> &'static str {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn str_sub(s: &'static str, b: usize, e: usize) -> &'static str {
        unimplemented!("This is a stub that is implemented in each backend")
    }
    pub fn str_index(s: &'static str, i: usize) -> char {
        unimplemented!("This is a stub that is implemented in each backend")
    }
}

pub mod mem {
    pub fn replace<T: ?Sized>(src: &mut T, dst: &T) {
        unimplemented!("This is a stub that is implemented in each backend")
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
                    unimplemented!("This is a stub that is implemented in each backend")
                })*
                $(pub fn [<$ov_op _ $t>](x: $t, y: $t) -> ($t, bool) {
                    unimplemented!("This is a stub that is implemented in each backend")
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
                    unimplemented!("This is a stub that is implemented in each backend")
                }
                pub fn [<count_ones_ $Self>](x: $Self) -> u32 {
                    unimplemented!("This is a stub that is implemented in each backend")
                }
                pub fn [<rotate_right_ $Self>](x: $Self, n: u32) -> $Self {
                    unimplemented!("This is a stub that is implemented in each backend")
                }
                pub fn [<rotate_left_ $Self>](x: $Self, n: u32) -> $Self {
                    unimplemented!("This is a stub that is implemented in each backend")
                }
                pub fn [<leading_zeros_ $Self>](x: $Self) -> u32 {
                    unimplemented!("This is a stub that is implemented in each backend")
                }
                pub fn [<ilog2_ $Self>](x: $Self) -> u32 {
                    unimplemented!("This is a stub that is implemented in each backend")
                }
                pub fn [<from_be_bytes_ $Self>](bytes: [u8; $Bytes]) -> $Self {
                    unimplemented!("This is a stub that is implemented in each backend")
                }
                pub fn [<from_le_bytes_ $Self>](bytes: [u8; $Bytes]) -> $Self {
                    unimplemented!("This is a stub that is implemented in each backend")
                }
                pub fn [<to_be_bytes_ $Self>](bytes: $Self) -> [u8; $Bytes] {
                    unimplemented!("This is a stub that is implemented in each backend")
                }
                pub fn [<to_le_bytes_ $Self>](bytes: $Self) -> [u8; $Bytes] {
                    unimplemented!("This is a stub that is implemented in each backend")
                })*
            }
        }
    }

    macro_rules! signed_ops {
        ($($Self: ident)*) => {
            paste! {
                $(
                    pub fn [<abs_ $Self>](x: $Self) -> $Self {
                    unimplemented!("This is a stub that is implemented in each backend")
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
