import Hax.Tactic.HaxConstructPure
import Hax.Tactic.HaxBVDecide
import Hax.rust_primitives

open Std.Do

/-! # Tests for `hax_construct_pure` -/

attribute [hax_bv_decide] UInt8.addOverflow

/-- Checked add: straight-line code. -/
example (a b : UInt8) (h : ¬a.addOverflow b = true) :
    { p // ⦃⌜ True ⌝⦄ (a +? b) ⦃⇓ r => ⌜ r = p ⌝⦄} := by
  hax_construct_pure <;> hax_bv_decide

/-- If-then-else with checked add. -/
example (a b : UInt8) (h : ¬a.addOverflow b = true) :
    { p // ⦃⌜ True ⌝⦄ if a > 0 then (a +? b) else pure a ⦃⇓ r => ⌜ r = p ⌝⦄} := by
  hax_construct_pure <;> hax_bv_decide


set_option trace.Hax.hax_construct_pure true in
/-- Do-block with let-bindings, multiple operators, and if-then-else. -/
example (a b c : UInt8)
    (h1 : ¬a.toBitVec.uaddOverflow b.toBitVec = true)
    (h2 : ¬(a + b).toBitVec.uaddOverflow c.toBitVec = true) :
    { p // ⦃⌜ True ⌝⦄ (do
      let x ← a +? b
      let y ← x +? c
      let z ← x ==? y
      if z then pure x else pure y : RustM _) ⦃⇓ r => ⌜ r = p ⌝⦄} := by
  hax_construct_pure <;> bv_decide
