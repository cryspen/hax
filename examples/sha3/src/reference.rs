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

fn _requires_iota(mut state: State, round: usize) -> bool {
    round < 24
}

/// ι step — FIPS 202, Algorithm 6.
///
///   A′[0,0] = A[0,0] ⊕ RC[ir]
#[hax_lib::requires(round < 24)]
pub fn iota(mut state: State, round: usize) -> State {
    state[0] ^= ROUND_CONSTANTS[round];
    state
}
