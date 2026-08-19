#![allow(unused)]

pub trait RngCore {
    // Required methods
    fn next_u32(&mut self) -> u32;
    fn next_u64(&mut self) -> u64;
    fn fill_bytes(&mut self, dst: &mut [u8]);
}

pub trait CryptoRng: RngCore {}

mod os {
    pub struct OsRng;
    // Dummy impl
    #[hax_lib::opaque]
    impl super::RngCore for OsRng {
        fn next_u32(&mut self) -> u32 {
            0
        }
        fn next_u64(&mut self) -> u64 {
            0
        }
        fn fill_bytes(&mut self, dst: &mut [u8]) {}
    }
    impl super::CryptoRng for OsRng {}
}

#[cfg(test)]
mod tests {
    use super::RngCore;

    // `OsRng` is a dummy impl: the model has no source of randomness, so the
    // constant answers below are the whole specification.
    #[test]
    fn test_os_rng_is_a_dummy() {
        let mut rng = crate::os::OsRng;
        assert_eq!(rng.next_u32(), 0);
        assert_eq!(rng.next_u64(), 0);
        let mut buf = [1u8; 4];
        rng.fill_bytes(&mut buf);
        assert_eq!(buf, [1u8; 4]);
    }
}
