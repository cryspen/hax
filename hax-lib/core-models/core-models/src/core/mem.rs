#![allow(unused_variables)]

use super::marker::Copy;

/// See [`std::mem::forget`]
#[hax_lib::opaque]
// mutants::skip: forgetting has no observable effect, so replacing the body with () is an equivalent mutant.
#[cfg_attr(test, mutants::skip)]
pub fn forget<T>(t: T) {
    rust_primitives::mem::forget(t)
}

/// See [`std::mem::forget_unsized`]
#[hax_lib::opaque]
// mutants::skip: as for `forget`, the empty body is an equivalent mutant.
#[cfg_attr(test, mutants::skip)]
pub fn forget_unsized<T>(t: T) {
    rust_primitives::mem::forget(t)
}

/// See [`std::mem::size_of`]
#[hax_lib::opaque]
pub fn size_of<T>() -> usize {
    rust_primitives::mem::size_of::<T>()
}

/// See [`std::mem::size_of_val`]
#[hax_lib::opaque]
pub fn size_of_val<T: ?Sized>(val: &T) -> usize {
    rust_primitives::mem::size_of_val(val)
}

/// See [`std::mem::min_align_of`]
#[hax_lib::opaque]
pub fn min_align_of<T>() -> usize {
    rust_primitives::mem::align_of::<T>()
}

/// See [`std::mem::min_align_of_val`]
#[hax_lib::opaque]
pub fn min_align_of_val<T: ?Sized>(val: &T) -> usize {
    rust_primitives::mem::align_of_val(val)
}

/// See [`std::mem::align_of`]
#[hax_lib::opaque]
pub fn align_of<T>() -> usize {
    rust_primitives::mem::align_of::<T>()
}

/// See [`std::mem::align_of_val`]
#[hax_lib::opaque]
pub fn align_of_val<T: ?Sized>(val: &T) -> usize {
    rust_primitives::mem::align_of_val(val)
}

/// See [`std::mem::align_of_val_raw`]
// Excluded from coverage: unlike std's, this signature takes the value itself
// rather than a raw pointer, so there is no callable meaning to give it.
#[cfg_attr(coverage_nightly, coverage(off))]
#[hax_lib::opaque]
pub unsafe fn align_of_val_raw<T>(val: T) -> usize {
    panic!()
}

/// See [`std::mem::needs_drop`]
#[hax_lib::opaque]
pub fn needs_drop<T: ?Sized>() -> bool {
    rust_primitives::mem::needs_drop::<T>()
}

/// See [`std::mem::uninitialized`]
// Excluded from coverage: calling it is instant UB, so no test may run it.
#[cfg_attr(coverage_nightly, coverage(off))]
#[hax_lib::opaque]
pub unsafe fn uninitialized<T>() -> T {
    panic!()
}

/// See [`std::mem::swap`]
#[hax_lib::opaque]
pub fn swap<T>(x: &mut T, y: &mut T) {
    rust_primitives::mem::swap(x, y)
}

/// See [`std::mem::replace`]
#[hax_lib::opaque]
pub fn replace<T>(dest: &mut T, src: T) -> T {
    rust_primitives::mem::replace(dest, src)
}

/// See [`std::mem::drop`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn drop<T>(_x: T) {}

/// See [`std::mem::take`]
// Excluded from coverage: std's `take` needs `T: Default` to leave something
// behind in `*x`; this signature has no such bound, so it cannot be written.
#[cfg_attr(coverage_nightly, coverage(off))]
#[hax_lib::opaque]
pub unsafe fn take<T>(x: &mut T) -> T {
    panic!()
}

/// See [`std::mem::transmute_copy`]
#[hax_lib::opaque]
pub unsafe fn transmute_copy<Src, Dst>(src: &Src) -> Dst {
    unsafe { rust_primitives::mem::transmute_copy(src) }
}

/// See [`std::mem::variant_count`]
// Excluded from coverage: `core::mem::variant_count` is a nightly-only
// intrinsic, and `rust_primitives` must keep building on stable.
#[cfg_attr(coverage_nightly, coverage(off))]
#[hax_lib::opaque]
// mutants::skip: excluded from coverage above, so no test can kill a mutant here.
#[cfg_attr(test, mutants::skip)]
pub fn variant_count<T>() -> usize {
    panic!()
}

/// See [`std::mem::zeroed`]
#[hax_lib::opaque]
pub unsafe fn zeroed<T>() -> T {
    unsafe { rust_primitives::mem::zeroed() }
}

/// See [`std::mem::transmute`]
#[hax_lib::opaque]
pub unsafe fn transmute<Src, Dst>(src: Src) -> Dst {
    unsafe { rust_primitives::mem::transmute(src) }
}

mod manually_drop {
    pub struct ManuallyDrop<T: ?Sized> {
        value: T,
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    // Layout queries take no runtime input, so they are checked per type
    // against `std::mem` rather than over a proptest domain.
    macro_rules! layout_tests {
        ($($t:ident),*) => {
            pastey::paste! { $(
                #[test]
                fn [<test_size_of_ $t>]() {
                    assert_eq!(super::size_of::<$t>(), std::mem::size_of::<$t>());
                }
                #[test]
                fn [<test_align_of_ $t>]() {
                    assert_eq!(super::align_of::<$t>(), std::mem::align_of::<$t>());
                    assert_eq!(super::min_align_of::<$t>(), std::mem::align_of::<$t>());
                }
                #[test]
                fn [<test_needs_drop_ $t>]() {
                    assert_eq!(super::needs_drop::<$t>(), std::mem::needs_drop::<$t>());
                }
            )* }
        };
    }

    layout_tests!(
        u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, bool
    );

    #[test]
    fn test_needs_drop_string() {
        assert_eq!(
            super::needs_drop::<std::string::String>(),
            std::mem::needs_drop::<std::string::String>()
        );
    }

    proptest! {
        #[test]
        fn test_size_of_val(v in prop::collection::vec(any::<u8>(), 0..50)) {
            prop_assert_eq!(super::size_of_val(v.as_slice()), std::mem::size_of_val(v.as_slice()));
            prop_assert_eq!(
                super::min_align_of_val(v.as_slice()),
                std::mem::align_of_val(v.as_slice())
            );
            prop_assert_eq!(
                super::align_of_val(v.as_slice()),
                std::mem::align_of_val(v.as_slice())
            );
        }

        // A wider element type: with `u8` slices every alignment is 1, which
        // any wrong answer of 1 also satisfies.
        #[test]
        fn test_align_of_val_wide(v in prop::collection::vec(any::<u64>(), 1..50)) {
            prop_assert_eq!(
                super::align_of_val(v.as_slice()),
                std::mem::align_of_val(v.as_slice())
            );
            prop_assert_eq!(
                super::min_align_of_val(v.as_slice()),
                std::mem::align_of_val(v.as_slice())
            );
        }

        #[test]
        fn test_swap(x in any::<u32>(), y in any::<u32>()) {
            let (mut ma, mut mb) = (x, y);
            super::swap(&mut ma, &mut mb);
            let (mut sa, mut sb) = (x, y);
            std::mem::swap(&mut sa, &mut sb);
            prop_assert_eq!((ma, mb), (sa, sb));
        }

        #[test]
        fn test_replace(dest in any::<u32>(), src in any::<u32>()) {
            let mut md = dest;
            let mold = super::replace(&mut md, src);
            let mut sd = dest;
            let sold = std::mem::replace(&mut sd, src);
            prop_assert_eq!((mold, md), (sold, sd));
        }

        #[test]
        fn test_forget(x in any::<u32>()) {
            // `forget` is observationally a no-op for a `Copy` value; what is
            // checked is that it consumes its argument without panicking.
            super::forget(x);
            super::forget_unsized(x);
            super::drop(x);
            prop_assert_eq!(x, x);
        }

        #[test]
        fn test_zeroed(_ignored in any::<u8>()) {
            prop_assert_eq!(unsafe { super::zeroed::<u32>() }, unsafe { std::mem::zeroed::<u32>() });
        }

        #[test]
        fn test_transmute(x in any::<u32>()) {
            prop_assert_eq!(unsafe { super::transmute::<u32, [u8; 4]>(x) }, x.to_ne_bytes());
        }

        #[test]
        fn test_transmute_copy(x in any::<u32>()) {
            prop_assert_eq!(
                unsafe { super::transmute_copy::<u32, [u8; 4]>(&x) },
                x.to_ne_bytes()
            );
        }
    }
}
