#[hax_lib::requires(x < 16)]
#[hax_lib::ensures(|res| res >= x)]
#[hax_lib::legacy_lean::proof("by unfold square; hax_bv_decide")]
fn square(x: u8) -> u8 {
    x * x
}
