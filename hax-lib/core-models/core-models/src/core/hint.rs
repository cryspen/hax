/// See [`std::hint::black_box`]
#[cfg_attr(hax_backend_fstar, hax_lib::ensures(|res| fstar!("$res == $dummy")))]
pub fn black_box<T>(dummy: T) -> T {
    dummy
}

/// See [`std::hint::must_use`]
#[cfg_attr(hax_backend_fstar, hax_lib::ensures(|res| fstar!("$res == $value")))]
pub fn must_use<T>(value: T) -> T {
    value
}

/// See [`std::hint::likely`]
#[cfg_attr(hax_backend_fstar, hax_lib::ensures(|res| fstar!("$res == $b")))]
pub const fn likely(b: bool) -> bool {
    b
}

/// See [`std::hint::unlikely`]
#[cfg_attr(hax_backend_fstar, hax_lib::ensures(|res| fstar!("$res == $b")))]
pub const fn unlikely(b: bool) -> bool {
    b
}

/// See [`std::hint::select_unpredictable`]
#[cfg_attr(hax_backend_fstar, hax_lib::ensures(|res| fstar!("$res == (if $condition then $true_val else $false_val)")))]
pub fn select_unpredictable<T>(condition: bool, true_val: T, false_val: T) -> T {
    if condition { true_val } else { false_val }
}

/// See [`std::hint::spin_loop`]
pub fn spin_loop() {}

/// See [`std::hint::cold_path`]
pub const fn cold_path() {}

/// See [`std::hint::unreachable_unchecked`]
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub const unsafe fn unreachable_unchecked() -> ! {
    panic!()
}

/// See [`std::hint::assert_unchecked`]
// Not `const fn` (real core's is): the model's panic helper is not const.
#[hax_lib::requires(cond)]
pub unsafe fn assert_unchecked(cond: bool) {
    if !cond {
        crate::panicking::internal::panic()
    }
}

/// See [`std::hint::Locality`]
pub enum Locality {
    /// See [`std::hint::Locality::L3`]
    L3,
    /// See [`std::hint::Locality::L2`]
    L2,
    /// See [`std::hint::Locality::L1`]
    L1,
}

// Excluded from F*, which rejects raw pointers; Aeneas supports them.

/// See [`std::hint::prefetch_read`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub const fn prefetch_read<T>(ptr: *const T, locality: Locality) {}

/// See [`std::hint::prefetch_read_non_temporal`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub const fn prefetch_read_non_temporal<T>(ptr: *const T, locality: Locality) {}

/// See [`std::hint::prefetch_read_instruction`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub const fn prefetch_read_instruction<T>(ptr: *const T, locality: Locality) {}

/// See [`std::hint::prefetch_write`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub const fn prefetch_write<T>(ptr: *mut T, locality: Locality) {}

/// See [`std::hint::prefetch_write_non_temporal`]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
pub const fn prefetch_write_non_temporal<T>(ptr: *const T, locality: Locality) {}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_black_box(x in any::<u8>()) {
            prop_assert_eq!(super::black_box(x), core::hint::black_box(x));
        }

        // `core::hint::must_use` is unstable, so this pins the identity directly.
        #[test]
        fn test_must_use(x in any::<u8>()) {
            prop_assert_eq!(super::must_use(x), x);
        }

        #[test]
        fn test_likely(b in any::<bool>()) {
            prop_assert_eq!(super::likely(b), core::hint::likely(b));
        }

        #[test]
        fn test_unlikely(b in any::<bool>()) {
            prop_assert_eq!(super::unlikely(b), core::hint::unlikely(b));
        }

        #[test]
        fn test_select_unpredictable(c in any::<bool>(), t in any::<u8>(), f in any::<u8>()) {
            prop_assert_eq!(
                super::select_unpredictable(c, t, f),
                core::hint::select_unpredictable(c, t, f)
            );
        }

        #[test]
        fn test_assert_unchecked_true(x in any::<u8>()) {
            unsafe { super::assert_unchecked(x == x) };
            unsafe { core::hint::assert_unchecked(x == x) };
        }
    }

    #[test]
    fn test_spin_loop() {
        super::spin_loop();
        core::hint::spin_loop();
    }

    #[test]
    fn test_cold_path() {
        super::cold_path();
        core::hint::cold_path();
    }

    // UB in real core, so only the model side is checked.
    #[test]
    fn test_unreachable_unchecked_panics() {
        let res = std::panic::catch_unwind(|| unsafe { super::unreachable_unchecked() });
        assert!(res.is_err());
    }

    #[test]
    fn test_assert_unchecked_false_panics() {
        let res = std::panic::catch_unwind(|| unsafe {
            super::assert_unchecked(std::hint::black_box(false))
        });
        assert!(res.is_err());
    }

    // Not in this crate's toolchain's std, so not compared against it.
    #[test]
    fn test_prefetch_is_a_noop() {
        let x = 42u8;
        let mut y = 7u8;
        super::prefetch_read(&x as *const u8, super::Locality::L1);
        super::prefetch_read_non_temporal(&x as *const u8, super::Locality::L2);
        super::prefetch_read_instruction(&x as *const u8, super::Locality::L3);
        super::prefetch_write(&mut y as *mut u8, super::Locality::L1);
        super::prefetch_write_non_temporal(&y as *const u8, super::Locality::L3);
        assert_eq!((x, y), (42u8, 7u8));
    }
}
