use super::State;

#[hax_lib::requires(bytes.len() == 12)]
#[hax_lib::ensures(|_| true)]
#[hax_lib::lean::proof_method::grind]
pub(super) fn to_le_u32s_3(bytes: &[u8]) -> [u32; 3] {
    // assert_eq!($l, bytes.len() / 4);
    let mut out = [0; 3];
    // for (i, block) in bytes.chunks(4).enumerate() {
    for i in 0..3 {
        out[i] = u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap());
    }
    out
}

#[hax_lib::requires(bytes.len() == 32)]
#[hax_lib::ensures(|_| true)]
#[hax_lib::lean::proof_method::grind]
pub(super) fn to_le_u32s_8(bytes: &[u8]) -> [u32; 8] {
    // assert_eq!(8, bytes.len() / 4);
    let mut out = [0; 8];
    // for (i, block) in bytes.chunks(4).enumerate() {
    for i in 0..8 {
        out[i] = u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap());
    }
    out
}

#[hax_lib::requires(bytes.len() == 64)]
#[hax_lib::ensures(|_| true)]
#[hax_lib::lean::proof_method::grind]
pub(super) fn to_le_u32s_16(bytes: &[u8]) -> [u32; 16] {
    // assert_eq!(16, bytes.len() / 4);
    let mut out = [0; 16];
    // for (i, block) in bytes.chunks(4).enumerate() {
    for i in 0..16 {
        out[i] = u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap());
    }
    out
}

#[hax_lib::ensures(|_| true)]
#[hax_lib::lean::proof_method::grind]
pub(super) fn u32s_to_le_bytes(state: &[u32; 16]) -> [u8; 64] {
    // <const L: usize>
    let mut out = [0; 64];
    for i in 0..state.len() {
        let tmp = state[i].to_le_bytes();
        for j in 0..4 {
            out[i * 4 + j] = tmp[j];
        }
    }
    out
}

#[hax_lib::ensures(|_| true)]
#[hax_lib::lean::proof_method::grind]
pub(super) fn xor_state(mut state: State, other: State) -> State {
    for i in 0..16 {
        state[i] = state[i] ^ other[i];
    }
    state
}

#[hax_lib::ensures(|_| true)]
#[hax_lib::lean::proof_method::grind]
pub(super) fn add_state(mut state: State, other: State) -> State {
    for i in 0..16 {
        state[i] = state[i].wrapping_add(other[i]);
    }
    state
}

#[hax_lib::requires(val.len() <= 64)]
#[hax_lib::ensures(|_| true)]
#[hax_lib::lean::proof_method::grind]
pub(super) fn update_array(mut array: [u8; 64], val: &[u8]) -> [u8; 64] {
    // <const L: usize>
    assert!(64 >= val.len());
    for i in 0..val.len() {
        array[i] = val[i];
    }
    array
}
