use anodized::spec;

// Specs on functions

#[spec(requires: x > 0)]
fn f1(x: u8) {}


/// Reference for comparison
#[hax_lib::requires(x > 0)]
fn f2(x: u8) {}

#[spec(ensures: *output == 1)]
fn f3() -> u8 {
    1
}
#[spec(ensures: |res| *res == 1)]
fn f4() -> u8 {
    1
}

/// Reference for comparison
#[spec(ensures: |res| *res == 1)] 
fn f5() -> u8 {
    1
}


#[spec(maintains: *x > 0)]
fn f6(x: &mut u8) {}


