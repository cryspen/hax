
pub trait RngCore {
    // Required methods
    fn next_u32(&mut self) -> u32;
    fn next_u64(&mut self) -> u64;
    fn fill_bytes(&mut self, dst: &mut [u8]);
}

pub trait CryptoRng: RngCore { }

mod os {
    pub struct OsRng;
    // Dummy impl
    impl super::RngCore for OsRng {
        fn next_u32(&mut self) -> u32 {
            0
        }
        fn next_u64(&mut self) -> u64 {
            0
        }
        fn fill_bytes(&mut self, dst: &mut [u8]){}
    }
    impl super::CryptoRng for OsRng {}
}

