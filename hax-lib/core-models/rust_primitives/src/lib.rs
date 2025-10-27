#![allow(unused_variables)]

pub mod slice {
    pub fn length<T>(s: &[T]) -> usize {
        panic!()
    }
    pub fn split_at<T>(s: &[T], mid: usize) -> (&[T], &[T]) {
        panic!()
    }
    pub fn contains<T>(s: &[T], v: T) -> bool {
        panic!()
    }
    pub fn array_from_fn<T, const N: usize>(f: fn(usize) -> T) -> [T; N] {
        panic!()
    }
    pub fn array_map<T, U, const N: usize, F>(s: [T; N], f: F) -> [U; N] {
        panic!()
    }
    pub fn array_as_slice<T, const N: usize>(s: [T; N]) -> &'static [T] {
        panic!()
    }
    pub fn slice_index<T>(s: &[T], i: usize) -> &T {
        panic!()
    }
}

pub mod mem {
    pub fn replace<T: ?Sized>(src: &mut T, dst: &T) {
        panic!()
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
                    panic!()
                })*
                $(pub fn [<$ov_op _ $t>](x: $t, y: $t) -> ($t, bool) {
                    panic!()
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
                    panic!()
                }
                pub fn [<count_ones_ $Self>](x: $Self) -> u32 {
                    panic!()
                }
                pub fn [<rotate_right_ $Self>](x: $Self, n: u32) -> $Self {
                    panic!()
                }
                pub fn [<rotate_left_ $Self>](x: $Self, n: u32) -> $Self {
                    panic!()
                }
                pub fn [<leading_zeros_ $Self>](x: $Self) -> u32 {
                    panic!()
                }
                pub fn [<ilog2_ $Self>](x: $Self) -> u32 {
                    panic!()
                }
                pub fn [<from_be_bytes_ $Self>](bytes: [u8; $Bytes]) -> $Self {
                    panic!()
                }
                pub fn [<from_le_bytes_ $Self>](bytes: [u8; $Bytes]) -> $Self {
                    panic!()
                }
                pub fn [<to_be_bytes_ $Self>](bytes: $Self) -> [u8; $Bytes] {
                    panic!()
                }
                pub fn [<to_le_bytes_ $Self>](bytes: $Self) -> [u8; $Bytes] {
                    panic!()
                })*
            }
        }
    }

    macro_rules! signed_ops {
        ($($Self: ident)*) => {
            paste! {
                $(
                    pub fn [<abs_ $Self>](x: $Self) -> $Self {
                    panic!()
                }
                )*
            }
        }
    }

    // Dummy values, to be defined by backends
    pub const SIZE_BYTES: usize = 0;
    pub const SIZE_BITS: u32 = 0;
    pub const USIZE_MAX: usize = 0;
    pub const ISIZE_MAX: isize = 0;
    pub const ISIZE_MIN: isize = 0;

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
