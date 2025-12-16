#[hax_lib::requires(x > 0)]
#[hax_lib::ensures(|r| r == x)]
fn test(x: u8) -> u8 {
    x
}
