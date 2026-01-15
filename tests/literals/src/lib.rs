trait Plus: Sized {
    fn plus(self, other: Self) -> Self;
}

#[hax_lib_macros::new_attributes]
impl Plus for u8 {
    #[hax_lib::requires(self + other + 3 == 4)]
    fn plus(self, other: Self) -> Self {
        self + other
    }
}

// trait Foo: Eq {
//     fn f(self) {}
// }
