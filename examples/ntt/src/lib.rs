type FieldElement = i16;
type MontgomeryFieldElement = i16;
type FieldElementTimesMontgomeryR = i16;
const MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i16 = 1353;
const FIELD_MODULUS: i16 = 3329;
const FIELD_ELEMENTS_IN_VECTOR: usize = 16;
const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R
const MONTGOMERY_SHIFT: u8 = 16;
const MONTGOMERY_R: i32 = 1 << MONTGOMERY_SHIFT;


fn montgomery_reduce_element(value: i32) -> MontgomeryFieldElement {
    let k = ((value as i16) as i32) * (INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32);
    let k_times_modulus = (k as i16 as i32) * (FIELD_MODULUS as i32);
    let c = (k_times_modulus >> MONTGOMERY_SHIFT) as i16;
    let value_high = (value >> MONTGOMERY_SHIFT) as i16;
    let result = value_high.wrapping_sub(c);
    result
}

fn montgomery_multiply_fe_by_fer(
    fe: FieldElement,
    fer: FieldElementTimesMontgomeryR,
) -> FieldElement {
    let product = (fe as i32) * (fer as i32);
    montgomery_reduce_element(product)
}

#[hax_lib::requires(i < 16 && j < 16)]
pub fn ntt_step(vec: &mut [i16; 16], zeta: i16, i: usize, j: usize) {
    let t = montgomery_multiply_fe_by_fer(vec[j], zeta);
    let a_minus_t = vec[i].wrapping_sub(t);
    let a_plus_t = vec[i].wrapping_add(t);
    vec[j] = a_minus_t;
    vec[i] = a_plus_t;
}