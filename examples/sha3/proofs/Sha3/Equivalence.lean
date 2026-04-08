import Sha3.Funs

namespace sha3

-- The reference implementation
#check reference.iota

-- The real implementaion
#check iota

open Std.Do Aeneas
set_option mvcgen.warning false

set_option trace.Hax.hax_mvcgen_at true

-- attribute [spec] KeccakState.Insts.CoreOpsIndexIndexPairUsizeUsizeT.index
-- attribute [spec] get_ij
-- attribute [spec] U64.Insts.Sha3KeccakItem1.xor_constant _veorq_n_u64 KeccakState.set set_ij

theorem iota_spec
  (st : KeccakState U64.Insts.Sha3KeccakItem1) (i : Std.Usize)
  (h : (_requires_iota st i).holds):
    ⦃ ⌜ True ⌝ ⦄
    iota st i
    ⦃ ⇓ r => ⌜ (_ensures_iota st i r).holds ⌝ ⦄ := by
  unfold iota KeccakState.iota  KeccakState.Insts.CoreOpsIndexIndexPairUsizeUsizeT.index get_ij
    _requires_iota at *
  dsimp only [U64.Insts.Sha3KeccakItem1.xor_constant, _veorq_n_u64, KeccakState.set, set_ij, _ensures_iota,
    reference.iota]
  mvcgen
  · grind
  · grind
  · hax_mvcgen at h
    simp only [Std.Slice.len, Std.Array.to_slice, USize64.reduceToNat, decide_eq_true_eq,
      ExceptConds.fst_false, SPred.down_pure, imp_false, USize64.not_lt]
    rwa [USize64.ofNat_le_iff]
    grind
  · grind
  · grind
  · unfold Result.holds
    mvcgen
    · grind
    · grind
    · grind
    · unfold ROUNDCONSTANTS reference.ROUND_CONSTANTS at *
      grind
