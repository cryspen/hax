import Hax

open Std.Do

-- A custom operation with no spec in any specset
def myOp (a b : u64) : RustM u64 := pure (a + b)

-- Example with an operation without spec
-- set_option hax_mvcgen.specset "int" in
-- example (a b : u64) (h : ⦃ ⌜ True ⌝ ⦄ (do (← myOp a b) >? 0) ⦃ ⇓r => ⌜ r ⌝ ⦄) : True := by
--   hax_mvcgen at h
--   sorry


@[specset int]
theorem haxAdd_spec {x y : u64} :
    ⦃ ⌜ True ⌝ ⦄ (x +? y) ⦃ ⇓? r => ⌜ r.toNat = x.toNat + y.toNat ⌝ ⦄ := by sorry



set_option hax_mvcgen.specset "int" in
example (a b : u64) (h : ⦃ ⌜ True ⌝ ⦄ (do (← a +? b) >? 0) ⦃ ⇓r => ⌜ r ⌝ ⦄) : True := by
  hax_mvcgen -apply at h
  apply True.intro


set_option hax_mvcgen.specset "int" in
example (a b : u64) (h : ∀ i, ⦃ ⌜ True ⌝ ⦄ (do (← a +? b) >? i) ⦃ ⇓r => ⌜ r ⌝ ⦄) :  a + b > 0 := by
  hax_mvcgen at h
  apply h
  grind
  sorry

set_option hax_mvcgen.specset "int" in
example (a b : u64) (h : ⦃ ⌜ True ⌝ ⦄ (do if ← (← a +? b) >? 0 then pure true else pure false) ⦃ ⇓r => ⌜ r ⌝ ⦄) : True := by
  hax_mvcgen -apply at h
  apply True.intro
