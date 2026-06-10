/// See [`std::default::Default`]
#[hax_lib::attributes]
pub trait Default {
    /// See [`std::default::Default::default`]
    #[hax_lib::requires(true)]
    fn default() -> Self;
}

#[cfg(test)]
mod tests {
    use pastey::paste;

    macro_rules! default_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    #[test]
                    fn [<test_ $t _default>]() {
                        assert_eq!(<$t as super::Default>::default(), <$t as std::default::Default>::default());
                    }
                )*
            }
        }
    }

    default_test! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }
}
