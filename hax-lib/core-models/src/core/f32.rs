#[hax_lib::exclude]
struct f32;

impl f32 {
    #[hax_lib::opaque]
    fn abs(x: f64) -> f64 {
        panic!()
    }
}
