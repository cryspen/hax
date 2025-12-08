const FIELD_MODULUS: i16 = 3329;
const MONTGOMERY_SHIFT: u8 = 16;
const MONTGOMERY_R: i32 = 1 << MONTGOMERY_SHIFT;
const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R

mod spec {
    pub(crate) fn bounded_i32(x: i32, b: i32) -> bool {
        b >= 0 && x >= -b && x <= b
    }
    pub(crate) fn bounded_i16(x: i16, b: i16) -> bool {
        b >= 0 && x >= -b && x <= b
    }
    pub(crate) fn bounded_i16_array(x: &[i16; 16], b: i16) -> bool {
        bounded_i16(x[0], b)
            && bounded_i16(x[1], b)
            && bounded_i16(x[2], b)
            && bounded_i16(x[3], b)
            && bounded_i16(x[4], b)
            && bounded_i16(x[5], b)
            && bounded_i16(x[6], b)
            && bounded_i16(x[7], b)
            && bounded_i16(x[8], b)
            && bounded_i16(x[9], b)
            && bounded_i16(x[10], b)
            && bounded_i16(x[11], b)
            && bounded_i16(x[12], b)
            && bounded_i16(x[13], b)
            && bounded_i16(x[14], b)
            && bounded_i16(x[15], b)
    }
}

#[hax_lib::requires(spec::bounded_i32(value, 32768*3328))]
#[hax_lib::ensures(|result| spec::bounded_i16(result, 3328))]
fn montgomery_reduce_element(value: i32) -> i16 {
    let k = ((value as i16) as i32) * (INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32);
    let k_times_modulus = (k as i16 as i32) * (FIELD_MODULUS as i32);
    let c = (k_times_modulus >> MONTGOMERY_SHIFT) as i16;
    let value_high = (value >> MONTGOMERY_SHIFT) as i16;
    let result = value_high - c;
    result
}

#[hax_lib::fstar::options("--z3rlimit 100")]
#[hax_lib::requires(i < 8 && out.len() >= 16 && spec::bounded_i16(zeta, 1664) &&
                    spec::bounded_i16_array(a,3328) && spec::bounded_i16_array(b,3328))]
pub fn accumulating_ntt_multiply_binomials(
    a: &[i16; 16],
    b: &[i16; 16],
    zeta: i16,
    i: usize,
    out: &mut [i32],
) {
    let ai = a[2 * i];
    let bi = b[2 * i];
    let aj = a[2 * i + 1];
    let bj = b[2 * i + 1];

    let ai_bi = (ai as i32) * (bi as i32);
    let bj_zeta_ = (bj as i32) * (zeta as i32);
    let bj_zeta = montgomery_reduce_element(bj_zeta_);
    let aj_bj_zeta = (aj as i32) * (bj_zeta as i32);
    let ai_bi_aj_bj = ai_bi + aj_bj_zeta;
    let o0 = ai_bi_aj_bj;

    let ai_bj = (ai as i32) * (bj as i32);
    let aj_bi = (aj as i32) * (bi as i32);
    let ai_bj_aj_bi = ai_bj + aj_bi;
    let o1 = ai_bj_aj_bi;

    out[2 * i] = out[2 * i].wrapping_add(o0);
    out[2 * i + 1] = out[2 * i + 1].wrapping_add(o1);
}
