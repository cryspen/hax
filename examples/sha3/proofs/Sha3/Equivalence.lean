import Sha3.Funs

namespace sha3

-- The reference implementation
#check reference.iota

-- The real implementaion
#check iota

open Std.Do Aeneas
set_option mvcgen.warning false

theorem iota_spec
  (st : KeccakState U64.Insts.Sha3KeccakItem1) (i : Std.Usize)
  (h : (_requires_iota st i).holds):
    ⦃ ⌜ True ⌝ ⦄
    iota st i
    ⦃ ⇓ r => ⌜ (_ensures_iota st i r).holds ⌝ ⦄ := by
  hax_mvcgen [iota, KeccakState.iota, _requires_iota]
