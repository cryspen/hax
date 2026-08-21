/// See [`std::primitive::f32`]
#[allow(non_camel_case_types)]
// F*-only: under `cfg(charon)` `hax_lib::exclude` now emits `charon::exclude`,
// which drops this dummy type while its `impl` block still references it.
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
struct f32;

impl f32 {
    /// See [`std::primitive::f32::abs`]
    #[hax_lib::opaque]
    fn abs(x: f64) -> f64 {
        panic!()
    }
}
