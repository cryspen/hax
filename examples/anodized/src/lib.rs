use anodized::spec;

// Specs on functions

#[spec(requires: x > 0)]
fn f1(x: u8) {}


/// Reference for comparison
#[hax_lib::requires(x > 0)]
fn f2(x: u8) {}

// The argument is only there to work around cryspen/hax#2177: the Lean backend
// drops the postcondition of a function that takes none. Remove once fixed.

#[spec(ensures: *output == x)]
fn f3(x: u8) -> u8 {
    x
}
#[spec(ensures: |res| *res == x)]
fn f4(x: u8) -> u8 {
    x
}

/// Reference for comparison: `hax_lib::ensures` binds the result by value,
/// `anodized` by reference.
#[hax_lib::ensures(|res| res == x)]
fn f5(x: u8) -> u8 {
    x
}


#[spec(maintains: *x > 0)]
fn f6(x: &mut u8) {}


