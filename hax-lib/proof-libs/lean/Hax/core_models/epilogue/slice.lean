import Hax.core_models.core_models

open Std.Do
set_option mvcgen.warning false

namespace core_models.slice

@[spec]
theorem Impl.len.spec (α : Type) (s : RustSlice α) :
    ⦃ ⌜ True ⌝ ⦄ Impl.len α s ⦃⇓ r => ⌜ r.toNat = s.val.size ⌝ ⦄ := by
  mvcgen; rw[USize64.toNat_ofNat_of_lt' s.size_lt_usizeSize]

end core_models.slice
