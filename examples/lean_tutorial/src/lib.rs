#[hax_lib::requires(x < 16)]
#[hax_lib::ensures(|res| res >= x)]
fn square(x: u8) -> u8 {
    x * x
}
