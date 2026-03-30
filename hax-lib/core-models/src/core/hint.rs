/// See [`std::hint::black_box`]
#[hax_lib::ensures(|res| fstar!("$res == $dummy"))]
pub fn black_box<T>(dummy: T) -> T {
    dummy
}

/// See [`std::hint::must_use`]
#[hax_lib::ensures(|res| fstar!("$res == $value"))]
pub fn must_use<T>(value: T) -> T {
    value
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_black_box(x in any::<u8>()) {
            prop_assert_eq!(super::black_box(x), x);
        }

        #[test]
        fn test_must_use(x in any::<u8>()) {
            prop_assert_eq!(super::must_use(x), x);
        }
    }
}
