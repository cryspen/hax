mod converts {
    #[hax_lib::opaque]
    fn from_utf8(s: &[u8]) -> crate::result::Result<&str, super::error::Utf8Error> {
        panic!()
    }
}

mod error {
    pub struct Utf8Error;
}

mod iter {
    struct Split<T>(T);
}

mod traits {
    trait FromStr: Sized {
        type Err;
        fn from_str(s: &str) -> crate::result::Result<Self, Self::Err>;
    }

    #[hax_lib::opaque]
    #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
    impl FromStr for u64 {
        type Err = u64;
        fn from_str(s: &str) -> crate::result::Result<Self, Self::Err> {
            panic!()
        }
    }
}
