/// See [`std::primitive::f32`]
#[allow(non_camel_case_types)]
#[hax_lib::exclude]
struct f32;

impl f32 {
    /// See [`std::primitive::f32::abs`]
    #[hax_lib::opaque]
    fn abs(x: f64) -> f64 {
        panic!()
    }
}
