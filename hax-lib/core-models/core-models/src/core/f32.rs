/// See [`std::primitive::f32`]
#[allow(non_camel_case_types)]
// F*-only: under `cfg(charon)` `hax_lib::exclude` now emits `charon::exclude`,
// which drops this dummy type while its `impl` block still references it.
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
struct f32;

impl f32 {
    /// See [`std::primitive::f32::abs`]
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    fn abs(x: f64) -> f64 {
        rust_primitives::float::abs_f64(x)
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    proptest! {
        // Compared on bits so that NaN inputs (where `==` is false) still count.
        #[test]
        fn test_abs(x in any::<f64>()) {
            prop_assert_eq!(super::f32::abs(x).to_bits(), x.abs().to_bits());
        }
    }
}
