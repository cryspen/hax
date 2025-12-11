const MONTGOMERY_SHIFT: u8 = 16;
const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R

mod spec {
    use hax_lib::int::*;
    pub(crate) const FIELD_MODULUS: i16 = 3329;
    pub(crate) fn bounded_i32(x: i32, b: i32) -> bool {
        b >= 0 && x >= -b && x <= b
    }
    pub(crate) fn bounded_i16(x: i16, b: i16) -> bool {
        b >= 0 && x >= -b && x <= b
    }

    // Can be replaced by an invocation to forall, but that turns it into a Prop
    pub(crate) fn bounded_i16x16(x: &[i16; 16], b: i16) -> bool {
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

    pub(crate) fn bounded_i32x16(x: &[i32; 16], b: i32) -> bool {
        bounded_i32(x[0], b)
            && bounded_i32(x[1], b)
            && bounded_i32(x[2], b)
            && bounded_i32(x[3], b)
            && bounded_i32(x[4], b)
            && bounded_i32(x[5], b)
            && bounded_i32(x[6], b)
            && bounded_i32(x[7], b)
            && bounded_i32(x[8], b)
            && bounded_i32(x[9], b)
            && bounded_i32(x[10], b)
            && bounded_i32(x[11], b)
            && bounded_i32(x[12], b)
            && bounded_i32(x[13], b)
            && bounded_i32(x[14], b)
            && bounded_i32(x[15], b)
    }

    // Can be replaced by an invocation to forall, but that turns it into a Prop
    pub(crate) fn bounded_i16x8(x: &[i16; 8], b: i16) -> bool {
        bounded_i16(x[0], b)
            && bounded_i16(x[1], b)
            && bounded_i16(x[2], b)
            && bounded_i16(x[3], b)
            && bounded_i16(x[4], b)
            && bounded_i16(x[5], b)
            && bounded_i16(x[6], b)
            && bounded_i16(x[7], b)
    }

    // Keeping this opaque speeds up proofs in F*
    pub(crate) fn modp(x: Int) -> Int {
        x.rem_euclid(FIELD_MODULUS.to_int())
    }

    // A functional spec for montgomery reduction
    pub(crate) fn montgomery_reduce_i32_spec(value: i32, result: i16) -> bool {
        modp(result.to_int()) == modp(value.to_int() * 169.to_int())
    }

    // A functional spec for even-index NTT multiplication
    pub(crate) fn ntt_mul_spec_0(a0: i16, a1: i16, b0: i16, b1: i16, zeta: i16, c0: i32) -> bool {
        modp(c0.to_int())
            == modp(
                a0.to_int() * b0.to_int()
                    + a1.to_int() * b1.to_int() * modp(zeta.to_int() * 169.to_int()),
            )
    }

    // A functional spec for odd-index NTT multiplication
    pub(crate) fn ntt_mul_spec_1(a0: i16, a1: i16, b0: i16, b1: i16, c1: i32) -> bool {
        modp(c1.to_int()) == modp(a0.to_int() * b1.to_int() + a1.to_int() * b0.to_int())
    }
}

/// More precise post-condition:
/// spec::montgomery_reduce_i32_spec(value, result)
/// Requires proof annotations
#[hax_lib::requires(spec::bounded_i32(value, 32768*3328))]
#[hax_lib::ensures(|result| spec::bounded_i16(result, 3328))]
fn montgomery_reduce_i32(value: i32) -> i16 {
    let k = (value as i16).wrapping_mul(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i16);
    let k_times_modulus = (k as i32) * (spec::FIELD_MODULUS as i32);
    let k_times_modulus_high = (k_times_modulus >> MONTGOMERY_SHIFT) as i16;
    let value_high = (value >> MONTGOMERY_SHIFT) as i16;
    let result = value_high - k_times_modulus_high;
    result
}

/// More precise post-condition:
/// spec::ntt_mul_spec_0(a0, a1, b0, b1, zeta, result)
/// Requires stronger post-condition on montgomery and proof annotations.
#[hax_lib::requires(spec::bounded_i16(zeta, 1664) &&
                    spec::bounded_i16(a0,3328) && spec::bounded_i16(a1,3328) &&
                    spec::bounded_i16(b0,3328) && spec::bounded_i16(b1,3328))]
#[hax_lib::ensures(|result| spec::bounded_i32(result, 3328*3328*2))]
fn ntt_multiply_binomials_0(a0: i16, a1: i16, b0: i16, b1: i16, zeta: i16) -> i32 {
    let a0_b0 = (a0 as i32) * (b0 as i32);
    let b1_zeta = montgomery_reduce_i32((b1 as i32) * (zeta as i32));
    let a1_b1_zeta = (a1 as i32) * (b1_zeta as i32);
    a0_b0 + a1_b1_zeta
}

#[hax_lib::requires(spec::bounded_i16(a0,3328) && spec::bounded_i16(a1,3328) &&
                    spec::bounded_i16(b0,3328) && spec::bounded_i16(b1,3328))]
#[hax_lib::ensures(|result| spec::bounded_i32(result, 3328*3328*2) &&
                            spec::ntt_mul_spec_1(a0, a1, b0, b1, result))]
fn ntt_multiply_binomials_1(a0: i16, a1: i16, b0: i16, b1: i16) -> i32 {
    let a0_b1 = (a0 as i32) * (b1 as i32);
    let a1_b0 = (a1 as i32) * (b0 as i32);
    a0_b1 + a1_b0
}

/// We may want to turn the fixed-length arrays into slices,
/// but this will require additional preconditions and loop invariants
#[hax_lib::requires(_i <= 4 &&
                    spec::bounded_i32x16(out, 3328*3328*2*(_i as i32)) &&
                    spec::bounded_i16x8(zetas, 1664) &&
                    spec::bounded_i16x16(a,3328) &&
                    spec::bounded_i16x16(b,3328))]
#[hax_lib::ensures(|_| spec::bounded_i32x16(future(out), 
                                            3328*3328*2*((_i as i32)+1)))]
pub fn accumulating_ntt_multiply_binomials(
    _i: usize,
    a: &[i16; 16],
    b: &[i16; 16],
    zetas: &[i16; 8],
    out: &mut [i32; 16],
) {
    #[cfg(hax)]
    let _out_original = *out;
    for i in 0..8 {
        hax_lib::loop_invariant!(|i:usize| 
            hax_lib::forall(|j:usize| hax_lib::implies(j < 2*i, 
                        spec::bounded_i32(out[j], 3328 * 3328 * 2 * ((i as i32)+1)))).and(
            hax_lib::forall(|j:usize| hax_lib::implies(j >= 2*i && j < 16, 
                        out[j] == _out_original[j]))));
        let o0 = ntt_multiply_binomials_0(a[2 * i], a[2 * i + 1], b[2 * i], b[2 * i + 1], zetas[i]);
        let o1 = ntt_multiply_binomials_1(a[2 * i], a[2 * i + 1], b[2 * i], b[2 * i + 1]);
        out[2 * i] = out[2 * i] + o0;
        out[2 * i + 1] = out[2 * i + 1] + o1;
    }
}
