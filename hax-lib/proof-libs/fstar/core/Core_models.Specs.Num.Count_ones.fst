module Core_models.Specs.Num.Count_ones

/// Behavioural contract of the `count_ones` integer models, which sum the bits
/// of their argument rather than routing through a primitive.
///
/// Every lemma here is a proof obligation, not runtime code. The bound lemmas
/// also stand in for the refinement the old `Rust_primitives.Arithmetic`
/// primitives carried in their type (`r: u32{v r <= 8}` and friends), which a
/// modelled body cannot express in its return type.
///
/// The popcount equality is stated for `u8` only. It is proved by unfolding the
/// model's `fold_range` once per bit, which is cheap at width 8 and does not
/// scale: at width 32 the same proof runs for minutes and then fails.
///
/// The obvious fix — induct on the fold's start index instead, so the cost is
/// width-independent — does not work, and the reason is worth recording. The
/// step is
///
///   fold_range s w inv acc f == fold_range (s +! 1) w inv (f acc s) f
///
/// which is `fold_range`'s own body, but it is not provable at any fuel. `f`'s
/// type mentions `start` (`fold_range_wf_index start end_ true (v i)`), so the
/// `f` in the recursive call is re-typed at `s + 1`: the two occurrences are not
/// the same term to Z3, and closing the gap needs functional extensionality.
/// Widening this therefore wants a characterisation lemma for `fold_range` in
/// `Rust_primitives.Hax.Folds` — where the step can be related pointwise, as a
/// `Lemma` argument — not more fuel and not a cleverer statement here.

open FStar.Mul
open Rust_primitives

/// Number of set bits of a natural, peeling from the low end. This is the shape
/// consumers state popcount facts in.
let rec popcount (n: nat) : Tot nat (decreases n) =
  if n = 0 then 0 else n % 2 + popcount (n / 2)

/// Sum of bits `s .. k-1` of `n`. Deliberately recursive on the *low* index, so
/// that it unfolds in lockstep with the `fold_range` the models extract to
/// (which recurses by advancing its start index).
let rec bitsum (n: nat) (s: nat) (k: nat{s <= k}) : Tot nat (decreases k - s) =
  if s = k then 0 else (n / pow2 s) % 2 + bitsum n (s + 1) k

#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"

/// Dropping the lowest bit shifts the window: bit `i+1` of `n` is bit `i` of `n/2`.
let rec bitsum_shift (n: nat) (s: nat) (k: nat{s <= k})
    : Lemma (ensures bitsum n (s + 1) (k + 1) == bitsum (n / 2) s k) (decreases k - s)
  = if s = k
    then ()
    else
      begin
        bitsum_shift n (s + 1) k;
        FStar.Math.Lemmas.pow2_plus 1 s;
        FStar.Math.Lemmas.division_multiplication_lemma n 2 (pow2 s)
      end

/// Once `k` bits are enough to hold `n`, the bit sum is the popcount.
let rec popcount_bitsum (n: nat) (k: nat)
    : Lemma (requires n < pow2 k) (ensures popcount n == bitsum n 0 k) (decreases k)
  = if k = 0
    then ()
    else
      begin
        FStar.Math.Lemmas.pow2_plus 1 (k - 1);
        popcount_bitsum (n / 2) (k - 1);
        bitsum_shift n 0 (k - 1)
      end

#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"

/// `(x >> i) & 1` is bit `i` of a non-negative `x`.
let bit_test (#t: inttype) (x: int_t t) (i: u32{v i < bits t})
    : Lemma (requires v x >= 0)
      (ensures (((x >>! i) &. mk_int #t 1) =. mk_int #t 1) == ((v x / pow2 (v i)) % 2 = 1))
  = assert_norm (pow2 1 == 2);
    logand_mask_lemma #t (x >>! i) 1

/// The models' `fold_range` invariant bounds the accumulator by the bit index,
/// so the result never exceeds the width. This is what the old
/// `Rust_primitives.Arithmetic.count_ones_*` primitives said in their type.
let count_ones_u8_bound (x: u8) : Lemma (v (Core_models.Num.impl_u8__count_ones x) <= 8) = ()

let count_ones_u16_bound (x: u16) : Lemma (v (Core_models.Num.impl_u16__count_ones x) <= 16) = ()

let count_ones_u32_bound (x: u32) : Lemma (v (Core_models.Num.impl_u32__count_ones x) <= 32) = ()

let count_ones_u64_bound (x: u64) : Lemma (v (Core_models.Num.impl_u64__count_ones x) <= 64) = ()

let count_ones_u128_bound (x: u128) : Lemma (v (Core_models.Num.impl_u128__count_ones x) <= 128) = ()

let count_ones_usize_bound (x: usize)
    : Lemma (v (Core_models.Num.impl_usize__count_ones x) <= size_bits)
  = ()

let count_ones_i8_bound (x: i8) : Lemma (v (Core_models.Num.impl_i8__count_ones x) <= 8) = ()

let count_ones_i16_bound (x: i16) : Lemma (v (Core_models.Num.impl_i16__count_ones x) <= 16) = ()

let count_ones_i32_bound (x: i32) : Lemma (v (Core_models.Num.impl_i32__count_ones x) <= 32) = ()

let count_ones_i64_bound (x: i64) : Lemma (v (Core_models.Num.impl_i64__count_ones x) <= 64) = ()

let count_ones_i128_bound (x: i128) : Lemma (v (Core_models.Num.impl_i128__count_ones x) <= 128) = ()

let count_ones_isize_bound (x: isize)
    : Lemma (v (Core_models.Num.impl_isize__count_ones x) <= size_bits)
  = ()

#pop-options

#push-options "--fuel 9 --ifuel 2 --z3rlimit 300"

let count_ones_u8_bitsum (x: u8)
    : Lemma (ensures v (Core_models.Num.impl_u8__count_ones x) == bitsum (v x) 0 8)
  = bit_test x (mk_u32 0);
    bit_test x (mk_u32 1);
    bit_test x (mk_u32 2);
    bit_test x (mk_u32 3);
    bit_test x (mk_u32 4);
    bit_test x (mk_u32 5);
    bit_test x (mk_u32 6);
    bit_test x (mk_u32 7)

#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"

/// `u8::count_ones` counts the set bits.
let count_ones_u8_popcount (x: u8)
    : Lemma (ensures v (Core_models.Num.impl_u8__count_ones x) == popcount (v x))
  = count_ones_u8_bitsum x;
    popcount_bitsum (v x) 8

#pop-options
