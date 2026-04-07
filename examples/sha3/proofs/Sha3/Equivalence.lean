import Sha3.Funs

namespace sha3

-- The reference implementation
#check reference.iota

-- The real implementaion
#check KeccakState.iota

theorem KeccakState.iota_spec :
  ⦃ ⌜ True ⌝ ⦄
  KeccakState.iota
  ⦃ ⇓ r => ⌜ ⌝ ⦄
