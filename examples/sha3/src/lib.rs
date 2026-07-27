// This example verifies parts of SHA-3. We prove two (partial) implementations to be equivalent:
// - a realistic SHA-3 implementation taken from the `libcrux` library
// - a reference implementation close to the official FIPS spec of the algorithm

// We verify only a very small part of SHA-3 here. Most of the implementation is not here
// and some parts are `unimplemented!()`.

// ===========================================================================
// Reference implementation: The five step mappings — FIPS 202, Algorithms 1–6
// ===========================================================================

mod reference {

    /// Keccak-f[1600] state: 5×5 lanes of 64-bit words.
    /// Keccak state type, exposed for cross-crate verification.
    pub type State = [u64; 25];

    /// Round constants `RC[ir]` for `ir = 0..23` — FIPS 202, Algorithm 5.
    pub const ROUND_CONSTANTS: [u64; 24] = [
        0x0000_0000_0000_0001,
        0x0000_0000_0000_8082,
        0x8000_0000_0000_808A,
        0x8000_0000_8000_8000,
        0x0000_0000_0000_808B,
        0x0000_0000_8000_0001,
        0x8000_0000_8000_8081,
        0x8000_0000_0000_8009,
        0x0000_0000_0000_008A,
        0x0000_0000_0000_0088,
        0x0000_0000_8000_8009,
        0x0000_0000_8000_000A,
        0x0000_0000_8000_808B,
        0x8000_0000_0000_008B,
        0x8000_0000_0000_8089,
        0x8000_0000_0000_8003,
        0x8000_0000_0000_8002,
        0x8000_0000_0000_0080,
        0x0000_0000_0000_800A,
        0x8000_0000_8000_000A,
        0x8000_0000_8000_8081,
        0x8000_0000_0000_8080,
        0x0000_0000_8000_0001,
        0x8000_0000_8000_8008,
    ];

    pub fn theta(_state: State) -> State {
        unimplemented!() // Not part of this example
    }

    pub fn rho(_state: State) -> State {
        unimplemented!() // Not part of this example
    }

    pub fn pi(_state: State) -> State {
        unimplemented!() // Not part of this example
    }

    pub fn chi(_state: State) -> State {
        unimplemented!() // Not part of this example
    }

    /// ι step — FIPS 202, Algorithm 6.
    ///
    ///   A′[0,0] = A[0,0] ⊕ RC[ir]
    #[hax_lib::requires(round < 24)]
    pub fn iota(mut state: State, round: usize) -> State {
        state[0] ^= ROUND_CONSTANTS[round];
        state
    }
}

// =========================================================================
// Realistic implementation (libcrux)
// =========================================================================

mod implementation {

    pub(crate) const ROUNDCONSTANTS: [u64; 24] = [
        0x0000_0000_0000_0001u64,
        0x0000_0000_0000_8082u64,
        0x8000_0000_0000_808au64,
        0x8000_0000_8000_8000u64,
        0x0000_0000_0000_808bu64,
        0x0000_0000_8000_0001u64,
        0x8000_0000_8000_8081u64,
        0x8000_0000_0000_8009u64,
        0x0000_0000_0000_008au64,
        0x0000_0000_0000_0088u64,
        0x0000_0000_8000_8009u64,
        0x0000_0000_8000_000au64,
        0x0000_0000_8000_808bu64,
        0x8000_0000_0000_008bu64,
        0x8000_0000_0000_8089u64,
        0x8000_0000_0000_8003u64,
        0x8000_0000_0000_8002u64,
        0x8000_0000_0000_0080u64,
        0x0000_0000_0000_800au64,
        0x8000_0000_8000_000au64,
        0x8000_0000_8000_8081u64,
        0x8000_0000_0000_8080u64,
        0x0000_0000_8000_0001u64,
        0x8000_0000_8000_8008u64,
    ];

    fn _veorq_n_u64(a: u64, c: u64) -> u64 {
        a ^ c
    }

    impl KeccakItem<1> for u64 {
        fn xor_constant(a: Self, c: u64) -> Self {
            _veorq_n_u64(a, c)
        }
    }

    pub(crate) fn get_ij<const N: usize, T: KeccakItem<N>>(
        arr: &[T; 25],
        i: usize,
        j: usize,
    ) -> &T {
        &arr[5 * j + i]
    }

    pub(crate) fn set_ij<const N: usize, T: KeccakItem<N>>(
        arr: &mut [T; 25],
        i: usize,
        j: usize,
        value: T,
    ) {
        arr[5 * j + i] = value;
    }

    /// A Keccak Item for multiplexing arithmetic implementations.
    pub(crate) trait KeccakItem<const N: usize>: Clone + Copy {
        /// `a ^ c`
        fn xor_constant(a: Self, c: u64) -> Self;
    }

    #[derive(Copy, Clone)]
    pub(crate) struct KeccakState<const N: usize, T: KeccakItem<N>> {
        pub(crate) st: [T; 25],
    }

    use core::ops::Index;

    impl<const N: usize, T: KeccakItem<N>> Index<(usize, usize)> for KeccakState<N, T> {
        type Output = T;

        /// Get element `[i, j]`.
        fn index(&self, index: (usize, usize)) -> &Self::Output {
            get_ij(&self.st, index.0, index.1)
        }
    }

    impl<const N: usize, T: KeccakItem<N>> KeccakState<N, T> {
        /// Set element `[i, j] = v`.
        fn set(&mut self, i: usize, j: usize, v: T) {
            set_ij(&mut self.st, i, j, v);
        }

        pub fn theta(&mut self) -> [T; 5] {
            unimplemented!() // Not part of this example
        }

        pub fn rho(&mut self, t: [T; 5]) {
            unimplemented!() // Not part of this example
        }

        pub fn chi(&mut self) {
            unimplemented!() // Not part of this example
        }

        pub fn pi(&mut self) {
            unimplemented!() // Not part of this example
        }

        pub fn iota(&mut self, i: usize) {
            self.set(0, 0, T::xor_constant(self[(0, 0)], ROUNDCONSTANTS[i]));
        }

        fn round(&mut self, i: usize) {
            let t = self.theta();
            self.rho(t);
            self.pi();
            self.chi();
            self.iota(i);
        }
    }

    // =========================================================================
    // Pre- and Postconditions
    // =========================================================================

    use crate::reference;

    // =========================================================================
    // Theta & Rho
    // =========================================================================

    // Theta and rho don't perfectly match the reference implementation. So we call `rho` from the
    // postcondition of theta. In this way, we can state a specification for `theta` and `rho` together.

    fn _requires_theta(_st: &KeccakState<1, u64>) -> bool {
        true
    }

    fn _ensures_theta(st: &KeccakState<1, u64>, res: &KeccakState<1, u64>, d: [u64; 5]) -> bool {
        let mut res = res.clone();
        res.rho(d);
        res.st == reference::rho(reference::theta(st.st))
    }

    // =========================================================================
    // Pi
    // =========================================================================

    fn _requires_pi(_st: &KeccakState<1, u64>) -> bool {
        true
    }

    fn _ensures_pi(st: &KeccakState<1, u64>, res: &KeccakState<1, u64>) -> bool {
        res.st == reference::pi(st.st)
    }

    // =========================================================================
    // Chi
    // =========================================================================

    fn _requires_chi(_st: &KeccakState<1, u64>) -> bool {
        true
    }

    fn _ensures_chi(st: &KeccakState<1, u64>, res: &KeccakState<1, u64>) -> bool {
        res.st == reference::chi(st.st)
    }

    // =========================================================================
    // Iota
    // =========================================================================

    fn _requires_iota(_st: &KeccakState<1, u64>, i: usize) -> bool {
        i < ROUNDCONSTANTS.len()
    }

    fn _ensures_iota(st: &KeccakState<1, u64>, i: usize, res: &KeccakState<1, u64>) -> bool {
        res.st == reference::iota(st.st, i)
    }

    // =========================================================================
    // Round
    // =========================================================================

    fn _requires_round(_st: &KeccakState<1, u64>, i: usize) -> bool {
        i < ROUNDCONSTANTS.len()
    }

    fn _ensures_round(st: &KeccakState<1, u64>, i: usize, res: &KeccakState<1, u64>) -> bool {
        res.st
            == reference::iota(
                reference::chi(reference::pi(reference::rho(reference::theta(st.st)))),
                i,
            )
    }
}
