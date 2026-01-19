// Arrays with const generic sizes

fn f<const N: usize>(x: [u8; N]) {}

fn g<const N: usize>(x: [u8; N]) {
    f(x);
    f([0u8; 10]);
}
