import Hax.core_models.core_models

open core_models.ops.range
open Std.Do

set_option mvcgen.warning false

open rust_primitives.sequence

attribute [local grind! .] USize64.toNat_lt_size

instance Range.instGetElemResultArrayUSize64 {α: Type}:
  GetElemResult
    (Seq α)
    (Range usize)
    (Seq α) where
  getElemResult xs i := match i with
  | ⟨s, e⟩ =>
    let size := xs.val.size;
    if s ≤ e && e.toNat ≤ size then
      pure ⟨xs.val.extract s.toNat e.toNat, by grind⟩
    else
      RustM.fail Error.arrayOutOfBounds

instance Range.instGetElemResultVectorUSize64 {α : Type} {n : Nat} :
  GetElemResult
    (Vector α n)
    (Range usize)
    (Seq α) where
  getElemResult xs i := match i with
  | ⟨s, e⟩ =>
    if s ≤ e && e.toNat ≤ n then
      pure ⟨(xs.extract s.toNat e.toNat).toArray, by grind⟩
    else
      RustM.fail Error.arrayOutOfBounds

@[spec]
theorem Range.getElemArrayUSize64_spec
  (α : Type) (a: Seq α) (s e: usize) :
  s.toNat ≤ e.toNat →
  e.toNat ≤ a.val.size →
  ⦃ ⌜ True ⌝ ⦄
  ( a[(Range.mk s e)]_? )
  ⦃ ⇓ r => ⌜ r = ⟨Array.extract a.val s.toNat e.toNat, by grind⟩ ⌝ ⦄
:= by
  intros
  mvcgen [Range.instGetElemResultArrayUSize64]
  grind [USize64.le_iff_toNat_le]

@[spec]
theorem Range.getElemVectorUSize64_spec
  (α : Type) (n: Nat) (a: Vector α n) (s e: usize) :
  s.toNat ≤ e.toNat →
  e.toNat ≤ a.size →
  ⦃ ⌜ True ⌝ ⦄
  ( a[(Range.mk s e)]_? )
  ⦃ ⇓ r => ⌜ r = ⟨(Vector.extract a s.toNat e.toNat).toArray, by grind⟩ ⌝ ⦄
:= by
  intros
  mvcgen [Range.instGetElemResultVectorUSize64]
  grind [USize64.le_iff_toNat_le]
