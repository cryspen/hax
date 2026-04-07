import Sha3.Funs

namespace sha3

-- The reference implementation
#check reference.iota

-- The real implementaion
#check iota

open Std.Do Aeneas
set_option mvcgen.warning false

set_option trace.Hax.hax_mvcgen_at true

attribute [spec] KeccakState.Insts.CoreOpsIndexIndexPairUsizeUsizeT.index
attribute [spec] get_ij
attribute [spec] U64.Insts.Sha3KeccakItem1.xor_constant _veorq_n_u64 KeccakState.set set_ij

theorem iota_spec
  (st : KeccakState U64.Insts.Sha3KeccakItem1) (i : Std.Usize)
  (h : (_requires_iota st i).holds):
    ⦃ ⌜ True ⌝ ⦄
    iota st i
    ⦃ ⇓ r => ⌜ (_ensures_iota st i r).holds ⌝ ⦄ := by
  hax_mvcgen [iota, KeccakState.iota, _requires_iota]
  mspec
  mspec
  sorry
  hax_mvcgen
  mspec
  sorry
  hax_mvcgen
  mspec
  sorry
  hax_mvcgen
  mspec
  mspec
  sorry
  hax_mvcgen
  mspec
  mspec
  hax_mvcgen
  mspec
  mspec
  sorry
  hax_mvcgen
  mspec
  sorry
  hax_mvcgen
  mspec
  sorry
  hax_mvcgen
  mspec
  sorry
