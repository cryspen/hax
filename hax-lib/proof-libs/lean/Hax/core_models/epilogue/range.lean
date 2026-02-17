import Hax.core_models.core_models

open core_models.ops.range
open Std.Do

set_option mvcgen.warning false

instance Range.instGetElemResultArrayUSize64 {α: Type}:
  GetElemResult
    (Array α)
    (Range usize)
    (Array α) where
  getElemResult xs i := match i with
  | ⟨s, e⟩ =>
    let size := xs.size;
    if s ≤ e && e.toNat ≤ size then
      pure ( xs.extract s.toNat e.toNat )
    else
      RustM.fail Error.arrayOutOfBounds

instance Range.instGetElemResultVectorUSize64 {α : Type} {n : Nat} :
  GetElemResult
    (Vector α n)
    (Range usize)
    (Array α) where
  getElemResult xs i := match i with
  | ⟨s, e⟩ =>
    if s ≤ e && e.toNat ≤ n then
      pure (xs.extract s.toNat e.toNat).toArray
    else
      RustM.fail Error.arrayOutOfBounds

@[spec]
theorem Range.getElemArrayUSize64_spec
  (α : Type) (a: Array α) (s e: usize) :
  s.toNat ≤ e.toNat →
  e.toNat ≤ a.size →
  ⦃ ⌜ True ⌝ ⦄
  ( a[(Range.mk s e)]_? )
  ⦃ ⇓ r => ⌜ r = Array.extract a s.toNat e.toNat ⌝ ⦄
:= by
  intros
  mvcgen [Core.Ops.Index.Index.index, Range.instGetElemResultArrayUSize64]
  grind [USize64.le_iff_toNat_le]

@[spec]
theorem Range.getElemVectorUSize64_spec
  (α : Type) (n: Nat) (a: Vector α n) (s e: usize) :
  s.toNat ≤ e.toNat →
  e.toNat ≤ a.size →
  ⦃ ⌜ True ⌝ ⦄
  ( a[(Range.mk s e)]_? )
  ⦃ ⇓ r => ⌜ r = (Vector.extract a s.toNat e.toNat).toArray ⌝ ⦄
:= by
  intros
  mvcgen [Core.Ops.Index.Index.index, Range.instGetElemResultVectorUSize64]
  grind [USize64.le_iff_toNat_le]
