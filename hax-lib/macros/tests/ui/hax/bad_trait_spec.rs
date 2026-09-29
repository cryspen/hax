#[hax_lib::attributes]
trait T {
    #[cfg_attr(all(), hax_lib::requires(,))]
    fn f(&self, x: u8) -> u8;
}

fn main() {}
