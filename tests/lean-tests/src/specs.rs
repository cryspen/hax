#[hax_lib::requires(x > 0)]
#[hax_lib::ensures(|r| r == x)]
fn test(x: u8) -> u8 {
    x
}

#[hax_lib::requires(x > 0)]
#[hax_lib::ensures(|r| r == x)]
#[hax_lib::lean::proof("by unfold Lean_tests.Specs.test_proof; hax_bv_decide")]
fn test_proof(x: u8) -> u8 {
    x
}
