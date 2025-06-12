module Barrett
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_BARRETT_SHIFT: i64 = mk_i64 26

let v_BARRETT_R: i64 = mk_i64 67108864

/// This is calculated as ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋
let v_BARRETT_MULTIPLIER: i64 = mk_i64 20159

let v_FIELD_MODULUS: i32 = mk_i32 3329

#push-options "--z3rlimit 100"

/// Signed Barrett Reduction
/// Given an input `value`, `barrett_reduce` outputs a representative `result`
/// such that:
/// - result ≡ value (mod FIELD_MODULUS)
/// - the absolute value of `result` is bound as follows:
/// `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)
/// In particular, if `|value| < BARRETT_R`, then `|result| < FIELD_MODULUS`.
let barrett_reduce (value: i32)
    : Prims.Pure i32
      (requires
        (Core.Convert.f_from #i64 #i32 #FStar.Tactics.Typeclasses.solve value <: i64) >=.
        (Core.Ops.Arith.f_neg v_BARRETT_R <: i64) &&
        (Core.Convert.f_from #i64 #i32 #FStar.Tactics.Typeclasses.solve value <: i64) <=.
        v_BARRETT_R)
      (ensures
        fun result ->
          let result:i32 = result in
          result >. (Core.Ops.Arith.f_neg v_FIELD_MODULUS <: i32) && result <. v_FIELD_MODULUS &&
          (result %! v_FIELD_MODULUS <: i32) =. (value %! v_FIELD_MODULUS <: i32)) =
  let t:i64 =
    (Core.Convert.f_from #i64 #i32 #FStar.Tactics.Typeclasses.solve value <: i64) *!
    v_BARRETT_MULTIPLIER
  in
  let t:i64 = t +! (v_BARRETT_R >>! mk_i32 1 <: i64) in
  let quotient:i64 = t >>! v_BARRETT_SHIFT in
  let quotient:i32 = cast (quotient <: i64) <: i32 in
  let sub:i32 = quotient *! v_FIELD_MODULUS in
  let _:Prims.unit = Math.Lemmas.cancel_mul_mod (v quotient) 3329 in
  value -! sub

#pop-options
