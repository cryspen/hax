mod reference;
use core::ops::Index;
use reference::*;

#[derive(Copy, Clone)]
pub(crate) struct KeccakState<const N: usize, T: KeccakItem<N>> {
    pub(crate) st: [T; 25],
}

pub fn _requires_get_ij<const N: usize, T: KeccakItem<N>>(
    arr: &[T; 25],
    i: usize,
    j: usize,
) -> bool {
    i < 5 && j < 5
}

// XXX: These should be default functions on `KeccakItem`, but hax doesn't
//      support that yet. cryspen/hax#888
#[hax_lib::requires(i < 5 && j < 5)]
#[inline(always)]
pub(crate) fn get_ij<const N: usize, T: KeccakItem<N>>(arr: &[T; 25], i: usize, j: usize) -> &T {
    &arr[5 * j + i]
}

pub fn _requires_set_ij<const N: usize, T: KeccakItem<N>>(
    arr: &mut [T; 25],
    i: usize,
    j: usize,
    value: T,
) -> bool {
    i < 5 && j < 5
}

#[hax_lib::requires(i < 5 && j < 5)]
#[inline(always)]
pub(crate) fn set_ij<const N: usize, T: KeccakItem<N>>(
    arr: &mut [T; 25],
    i: usize,
    j: usize,
    value: T,
) {
    arr[5 * j + i] = value;
}

#[hax_lib::attributes]
pub(crate) trait KeccakItem<const N: usize>: Clone + Copy {
    /// Zero
    #[hax_lib::requires(true)]
    fn zero() -> Self;

    /// `a ^ c`
    #[hax_lib::requires(true)]
    fn xor_constant(a: Self, c: u64) -> Self;
}

#[inline(always)]
fn _veorq_n_u64(a: u64, c: u64) -> u64 {
    a ^ c
}

#[hax_lib::attributes]
impl KeccakItem<1> for u64 {
    #[inline(always)]
    fn zero() -> Self {
        0
    }

    #[inline(always)]
    fn xor_constant(a: Self, c: u64) -> Self {
        _veorq_n_u64(a, c)
    }
}

pub const ROUNDCONSTANTS: [u64; 24] = [
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

#[hax_lib::attributes]
impl<const N: usize, T: KeccakItem<N>> KeccakState<N, T> {
    /// Create a new Shake128 x4 state.
    #[inline(always)]
    pub(crate) fn new() -> Self {
        Self {
            st: [T::zero(); 25],
        }
    }

    fn _requires_set(&mut self, i: usize, j: usize, v: T) -> bool {
        i < 5 && j < 5
    }

    /// Set element `[i, j] = v`.
    #[hax_lib::requires(i < 5 && j < 5)]
    fn set(&mut self, i: usize, j: usize, v: T) {
        set_ij(&mut self.st, i, j, v);
    }

    fn _requires_iota(&mut self, i: usize) -> bool {
        i < ROUNDCONSTANTS.len()
    }

    #[inline(always)]
    #[hax_lib::requires(i < ROUNDCONSTANTS.len())]
    fn iota(&mut self, i: usize) {
        self.set(0, 0, T::xor_constant(self[(0, 0)], ROUNDCONSTANTS[i]));
    }
}

fn _requires_index(index: (usize, usize)) -> bool {
    index.0 < 5 && index.1 < 5
}

#[hax_lib::attributes]
impl<const N: usize, T: KeccakItem<N>> Index<(usize, usize)> for KeccakState<N, T> {
    type Output = T;

    /// Get element `[i, j]`.
    #[hax_lib::requires(index.0 < 5 && index.1 < 5)]
    fn index(&self, index: (usize, usize)) -> &Self::Output {
        get_ij(&self.st, index.0, index.1)
    }
}
